/* vi:set ts=8 sts=4 sw=4 et:
 *
 * VIM - Vi IMproved    by Bram Moolenaar
 *
 * Bore by Jonas Kjellström & Per-Jonny Käck
 *
 * Do ":help uganda"  in Vim to read copying and usage conditions.
 * Do ":help credits" in Vim to see a list of people who contributed.
 * See README.txt for an overview of the Vim source code.
 */

#include "vim.h"
#include "if_bore.h"

// #define BORE_VIMPROFILE
// __pragma(optimize("", off))

#ifdef BORE_VIMPROFILE
#define BORE_VIMPROFILE_INIT proftime_T ptime
#define BORE_VIMPROFILE_START profile_start(&ptime)
#define BORE_VIMPROFILE_STOP(str) do \
{ \
    char pmess[100]; \
    profile_end(&ptime); \
    vim_snprintf(pmess, 100, "%s %s", profile_msg(&ptime), str); \
    const int p_msg_silent = msg_silent; \
    msg_silent = 0; \
    msg(_(pmess)); \
    msg_silent = p_msg_silent; \
} while(0)
#else
#define BORE_VIMPROFILE_INIT
#define BORE_VIMPROFILE_START
#define BORE_VIMPROFILE_STOP(str)
#endif

#if defined(FEAT_BORE)

/* Hash set for visited directories — prevents duplicate scans across csproj files */
#define BORE_VISITED_BUCKETS 4096
typedef struct bore_visited_entry_t {
    struct bore_visited_entry_t* next;
    struct bore_visited_entry_t* next_alloc;
    u32 hash;
    int wdir_len;
    const char* pattern;
    WCHAR wdir[1];
} bore_visited_entry_t;

static bore_visited_entry_t* bore_visited_table[BORE_VISITED_BUCKETS];
static bore_visited_entry_t* bore_visited_alloc_list;

static void bore_visited_reset(void)
{
    bore_visited_entry_t* e;
    bore_visited_entry_t* next;
    for (e = bore_visited_alloc_list; e; e = next)
    {
        next = e->next_alloc;
        vim_free(e);
    }
    memset(bore_visited_table, 0, sizeof(bore_visited_table));
    bore_visited_alloc_list = NULL;
}

/* Returns 1 if already visited, 0 if newly inserted */
static int bore_visit_and_insert(const WCHAR* wdir, int wdir_len, const char* pattern)
{
    u32 h = 5381;
    int i, bucket, alloc_size;
    bore_visited_entry_t* e;

    for (i = 0; i < wdir_len; ++i)
        h = ((h << 5) + h) + (u32)wdir[i];
    h ^= (u32)(uintptr_t)pattern;
    bucket = h & (BORE_VISITED_BUCKETS - 1);

    for (e = bore_visited_table[bucket]; e; e = e->next)
        if (e->hash == h && e->wdir_len == wdir_len && e->pattern == pattern &&
            0 == memcmp(e->wdir, wdir, wdir_len * sizeof(WCHAR)))
            return 1;

    alloc_size = (int)(offsetof(bore_visited_entry_t, wdir) + (wdir_len + 1) * sizeof(WCHAR));
    e = (bore_visited_entry_t*)alloc(alloc_size);
    if (!e)
        return 1;
    e->hash = h;
    e->wdir_len = wdir_len;
    e->pattern = pattern;
    memcpy(e->wdir, wdir, wdir_len * sizeof(WCHAR));
    e->wdir[wdir_len] = 0;
    e->next = bore_visited_table[bucket];
    bore_visited_table[bucket] = e;
    e->next_alloc = bore_visited_alloc_list;
    bore_visited_alloc_list = e;
    return 0;
}

static int bore_canonicalize (const char* src, char* dst, DWORD* attr);
static u32 bore_string_hash(const char* s);
static u32 bore_string_hash_n(const char* s, int n);
static int bore_is_excluded_file(const char* path);
static int bore_is_excluded_file_n(const char* path, int len);

void bore_prealloc(bore_alloc_t* p, size_t size)
{
    p->base = (u8*)lalloc(size + BORE_CACHELINE, TRUE);
    p->offset = BORE_CACHELINE - ((size_t)(p->base) & (BORE_CACHELINE - 1));
    p->base += p->offset;
    assert(((size_t)(p->base) & (BORE_CACHELINE - 1)) == 0);
    p->end  = p->base + size;
    p->cursor = p->base;
}

void* bore_alloc(bore_alloc_t* p, size_t size)
{
    void* mem;
    if (p->cursor + size > p->end)
    {
        // resize
        size_t capacity = p->end - p->base;
        size_t newcapacity = capacity * 2;
        size_t currentsize = p->cursor - p->base;
        size_t newsize = currentsize + size;
        size_t offsetnew;
        u8* basenew;
        if (newsize > newcapacity)
            newcapacity = newsize * 2;
        basenew = lalloc(newcapacity + BORE_CACHELINE, TRUE);
        offsetnew = BORE_CACHELINE - ((size_t)basenew & (BORE_CACHELINE - 1));
        basenew += offsetnew;
        assert(((size_t)basenew & (BORE_CACHELINE - 1)) == 0);
        memcpy(basenew, p->base, currentsize);
        vim_free(p->base - p->offset);
        p->cursor = basenew + currentsize;
        p->base = basenew;
        p->offset = offsetnew;
        p->end = p->base + newcapacity;
    }
    mem = p->cursor;
    p->cursor += size;
    return mem;
}

void bore_alloc_trim(bore_alloc_t* p, size_t size)
{
    p->cursor -= size;
}

void bore_alloc_free(bore_alloc_t* p)
{
    if (p->base)
        vim_free(p->base - p->offset);
}

static bore_t* g_bore = 0;

static void bore_free(bore_t* b)
{
    int i;
    if (!b) return;
    bore_alloc_free(&b->file_alloc);
    bore_alloc_free(&b->file_ext_alloc);
    bore_alloc_free(&b->toggle_index_alloc);
    bore_alloc_free(&b->data_alloc);
    bore_alloc_free(&b->config_alloc);
    bore_alloc_free(&b->proj_alloc);
    for (i = 0; i < BORE_SEARCH_JOBS; ++i)
    {
        bore_alloc_free(&b->search[i].filedata);
    }
    vim_free(b);
}

char* bore_str(bore_t* b, u32 offset)
{
    return (char*)(b->data_alloc.base + offset);
}

char* bore_rel_path(bore_t* b, u32 offset)
{
    char* slndir = bore_str(b, b->sln_dir);
    char* fn = bore_str(b, offset);
    if (STRNICMP(fn, slndir, b->sln_dir_len) == 0)
        return fn + b->sln_dir_len;
    return fn;
}

static u32 bore_strndup(bore_t* b, const char* s, size_t len)
{
    char* p = (char*)bore_alloc(&b->data_alloc, len + 1);
    memcpy(p, s, len);
    p[len] = 0;
    return p - (char*)b->data_alloc.base;
}

static int bore_str_match_len(const char* target, const char* candidate)
{
    int len = 0;
    while (*target && *candidate && (TOLOWER_LOC(*target) == TOLOWER_LOC(*candidate)))
    {
        ++target;
        ++candidate;
        ++len;
    }
    return len;
}

static int bore_str_match_score(const char* target, const char* candidate)
{
    int score = 0;
    while(*target && *candidate && (TOLOWER_LOC(*target) == TOLOWER_LOC(*candidate)))
    {
        ++target;
        ++candidate;
        ++score;
    }
    if (*candidate == '\0' && *target == '\0')
        ++score;
    return score;
}

static int bore_is_sln_directory(bore_t* b)
{
    return b->sln_dir == b->sln_path;
}

static int bore_is_excluded_file(const char* path)
{
    return bore_is_excluded_file_n(path, -1);
}

static int bore_is_excluded_file_n(const char* path, int len)
{
    const char* ext;
    if (len > 0)
        for (ext = path + len - 1; ext >= path && *ext != '.'; --ext);
    else
        ext = (char*)vim_strrchr((char_u*)path, '.');

    if (0 == ext || *ext != '.')
        return 0;
    ++ext;

    char ext_low[16];
    int i;
    for (i = 0; i < 15 && ext[i]; ++i)
        ext_low[i] = TOLOWER_LOC(ext[i]);
    ext_low[i] = 0;

    /* libraries, objects, executables */
    if (
            0 == STRCMP(ext_low, "a") ||
            0 == STRCMP(ext_low, "aar") ||
            0 == STRCMP(ext_low, "apk") ||
            0 == STRCMP(ext_low, "bin") ||
            0 == STRCMP(ext_low, "dll") ||
            0 == STRCMP(ext_low, "dylib") ||
            0 == STRCMP(ext_low, "exe") ||
            0 == STRCMP(ext_low, "exp") ||
            0 == STRCMP(ext_low, "jar") ||
            0 == STRCMP(ext_low, "jnilib") ||
            0 == STRCMP(ext_low, "lib") ||
            0 == STRCMP(ext_low, "metallib") ||
            0 == STRCMP(ext_low, "msi") ||
            0 == STRCMP(ext_low, "msm") ||
            0 == STRCMP(ext_low, "nupkg") ||
            0 == STRCMP(ext_low, "obj") ||
            0 == STRCMP(ext_low, "pch") ||
            0 == STRCMP(ext_low, "pdb") ||
            0 == STRCMP(ext_low, "prx") ||
            0 == STRCMP(ext_low, "pyc") ||
            0 == STRCMP(ext_low, "so") ||
            0 == STRCMP(ext_low, "sym") ||
            0 == STRCMP(ext_low, "vsix") ||
            0
       ) return 1;

    /* images, fonts */
    if (
            0 == STRCMP(ext_low, "bmp") ||
            0 == STRCMP(ext_low, "cur") ||
            0 == STRCMP(ext_low, "gif") ||
            0 == STRCMP(ext_low, "hdr") ||
            0 == STRCMP(ext_low, "ico") ||
            0 == STRCMP(ext_low, "icns") ||
            0 == STRCMP(ext_low, "jpg") ||
            0 == STRCMP(ext_low, "pdf") ||
            0 == STRCMP(ext_low, "png") ||
            0 == STRCMP(ext_low, "psd") ||
            0 == STRCMP(ext_low, "tga") ||
            0 == STRCMP(ext_low, "ttf") ||
            0 == STRCMP(ext_low, "webp") ||
            0
       ) return 1;

    /* audio */
    if (
            0 == STRCMP(ext_low, "at9") ||
            0 == STRCMP(ext_low, "mp3") ||
            0 == STRCMP(ext_low, "mp4") ||
            0 == STRCMP(ext_low, "sfx") ||
            0 == STRCMP(ext_low, "wav") ||
            0
       ) return 1;

    /* data, profiling, caches */
    if (
            0 == STRCMP(ext_low, "blob") ||
            0 == STRCMP(ext_low, "cache") ||
            0 == STRCMP(ext_low, "cbor") ||
            0 == STRCMP(ext_low, "cnv") ||
            0 == STRCMP(ext_low, "dat") ||
            0 == STRCMP(ext_low, "db") ||
            0 == STRCMP(ext_low, "faiss") ||
            0 == STRCMP(ext_low, "fatbin") ||
            0 == STRCMP(ext_low, "icu") ||
            0 == STRCMP(ext_low, "locres") ||
            0 == STRCMP(ext_low, "nib") ||
            0 == STRCMP(ext_low, "pgc") ||
            0 == STRCMP(ext_low, "pgd") ||
            0 == STRCMP(ext_low, "profdata") ||
            0 == STRCMP(ext_low, "profraw") ||
            0 == STRCMP(ext_low, "res") ||
            0 == STRCMP(ext_low, "spv") ||
            0
       ) return 1;

    /* UE assets */
    if (
            0 == STRCMP(ext_low, "fbx") ||
            0 == STRCMP(ext_low, "uasset") ||
            0 == STRCMP(ext_low, "umap") ||
            0 == STRCMP(ext_low, "utrace") ||
            0
       ) return 1;

    /* archives */
    if (
            0 == STRCMP(ext_low, "7z") ||
            0 == STRCMP(ext_low, "cab") ||
            0 == STRCMP(ext_low, "gz") ||
            0 == STRCMP(ext_low, "tgz") ||
            0 == STRCMP(ext_low, "zip") ||
            0
       ) return 1;

    /* crypto, keys */
    if (
            0 == STRCMP(ext_low, "keystore") ||
            0 == STRCMP(ext_low, "p12") ||
            0 == STRCMP(ext_low, "p7s") ||
            0
       ) return 1;

    return 0;
}

/*
 * Returns TRUE if the path needs a GetFileAttributesW check to confirm
 * it is a real file (not a directory or assembly reference).
 * Paths with a normal file extension (1-4 chars) are trusted.
 */
static int bore_requires_fileattr(const char* path, int len)
{
    const char* fname = path + len;
    const char* dot;
    int ext_len;

    /* Find filename part (after last separator) */
    while (fname > path && fname[-1] != '\\' && fname[-1] != '/')
        --fname;

    if (fname == path)
        return 1; /* no path separator — not a real file path */

    dot = (char*)vim_strrchr((char_u*)fname, '.');
    if (!dot)
        return 1; /* no extension */

    ext_len = (int)(path + len - dot - 1);
    if (ext_len >= 1 && ext_len <= 4)
        return 0; /* normal extension like .cs, .cpp, .h, .json */

    return 1; /* long or empty extension */
}

static int bore_is_excluded_dir(const WCHAR* name)
{
    if (name[0] == L'.')
        return 1;
    if (0 == _wcsicmp(name, L"bin")) return 1;
    if (0 == _wcsicmp(name, L"lib")) return 1;
    if (0 == _wcsicmp(name, L"obj")) return 1;
    if (0 == _wcsicmp(name, L"x64")) return 1;
    if (0 == _wcsicmp(name, L"Binaries")) return 1;
    if (0 == _wcsicmp(name, L"Content")) return 1;
    if (0 == _wcsicmp(name, L"DerivedDataCache")) return 1;
    if (0 == _wcsicmp(name, L"Documentation")) return 1;
    if (0 == _wcsicmp(name, L"Intermediate")) return 1;
    if (0 == _wcsicmp(name, L"Saved")) return 1;
    if (0 == _wcsicmp(name, L"ThirdParty")) return 1;
    return 0;
}

/*
 * Expand wildcard pattern under 'wdir' using FindFirstFileExW.
 * Works in wide chars; 'wdir' is mutable with trailing backslash.
 * Supports **, * globs, and literal path segments.
 */
static void bore_expand_wildcard_files_r(bore_t* b, int proj_index,
    WCHAR* wdir, int wdir_len, const char* pattern, int depth)
{
    WCHAR wpath[BORE_MAX_PATH];
    WIN32_FIND_DATAW fd;
    HANDLE hFind;
    const char* sep;
    const char* rest;
    int seg_len, is_globstar;

    if (depth > 64)
        return;

    /* Split pattern into first segment and rest */
    sep = strchr(pattern, '\\');
    if (!sep) sep = strchr(pattern, '/');
    seg_len = sep ? (int)(sep - pattern) : (int)strlen(pattern);
    rest = sep ? sep + 1 : NULL;
    is_globstar = (seg_len == 2 && pattern[0] == '*' && pattern[1] == '*');

    if (is_globstar && bore_visit_and_insert(wdir, wdir_len, pattern))
        return;

    if (is_globstar && rest && !strchr(rest, '\\') && !strchr(rest, '/'))
    {
        /*
         * Optimized **\<leaf> (e.g. **\*.cs): single enumeration of '*'
         * handles both subdirs and file matching in one pass.
         */
        WCHAR wrest[BORE_MAX_PATH];
        char fullpath_utf8[BORE_MAX_PATH];
        int dir_utf8_len;
        const WCHAR* ext_pattern;

        MultiByteToWideChar(CP_UTF8, 0, rest, -1, wrest, BORE_MAX_PATH);
        ext_pattern = wcschr(wrest, L'.');
        dir_utf8_len = WideCharToMultiByte(CP_UTF8, 0, wdir, wdir_len, fullpath_utf8, BORE_MAX_PATH, 0, 0);

        memcpy(wpath, wdir, wdir_len * sizeof(WCHAR));
        memcpy(wpath + wdir_len, L"*", 2 * sizeof(WCHAR));

        hFind = FindFirstFileExW(wpath, FindExInfoBasic, &fd,
            FindExSearchNameMatch, NULL, FIND_FIRST_EX_LARGE_FETCH);
        if (hFind == INVALID_HANDLE_VALUE)
            return;
        do
        {
            int name_len;
            if (fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY)
            {
                if (fd.dwFileAttributes & FILE_ATTRIBUTE_REPARSE_POINT)
                    continue;
                if (bore_is_excluded_dir(fd.cFileName))
                    continue;
                name_len = (int)wcslen(fd.cFileName);
                if (wdir_len + name_len + 1 >= BORE_MAX_PATH)
                    continue;
                memcpy(wdir + wdir_len, fd.cFileName, name_len * sizeof(WCHAR));
                wdir[wdir_len + name_len] = L'\\';
                wdir[wdir_len + name_len + 1] = 0;
                bore_expand_wildcard_files_r(b, proj_index, wdir, wdir_len + name_len + 1, pattern, depth + 1);
            }
            else if (ext_pattern && dir_utf8_len > 0)
            {
                const WCHAR* ext_file = wcsrchr(fd.cFileName, L'.');
                if (ext_file && 0 == _wcsicmp(ext_pattern, ext_file))
                {
                    name_len = WideCharToMultiByte(CP_UTF8, 0, fd.cFileName, -1,
                        fullpath_utf8 + dir_utf8_len, BORE_MAX_PATH - dir_utf8_len, 0, 0);
                    if (name_len > 0 && !bore_is_excluded_file(fullpath_utf8))
                    {
                        bore_file_t* f = (bore_file_t*)bore_alloc(&b->file_alloc, sizeof(bore_file_t));
                        f->file = bore_strndup(b, fullpath_utf8, dir_utf8_len + name_len - 1);
                        f->proj_index = proj_index;
                        ++b->file_count;
                    }
                }
            }
        }
        while (FindNextFileW(hFind, &fd));
        wdir[wdir_len] = 0;
        FindClose(hFind);
    }
    else if (is_globstar)
    {
        /* General ** — match rest at current level, then recurse into subdirs */
        if (rest)
            bore_expand_wildcard_files_r(b, proj_index, wdir, wdir_len, rest, depth);

        memcpy(wpath, wdir, wdir_len * sizeof(WCHAR));
        memcpy(wpath + wdir_len, L"*", 2 * sizeof(WCHAR));
        hFind = FindFirstFileExW(wpath, FindExInfoBasic, &fd,
            FindExSearchLimitToDirectories, NULL, FIND_FIRST_EX_LARGE_FETCH);
        if (hFind == INVALID_HANDLE_VALUE)
            return;
        do
        {
            int name_len;
            if (!(fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY))
                continue;
            if (fd.dwFileAttributes & FILE_ATTRIBUTE_REPARSE_POINT)
                continue;
            if (bore_is_excluded_dir(fd.cFileName))
                continue;
            name_len = (int)wcslen(fd.cFileName);
            if (wdir_len + name_len + 1 >= BORE_MAX_PATH)
                continue;
            memcpy(wdir + wdir_len, fd.cFileName, name_len * sizeof(WCHAR));
            wdir[wdir_len + name_len] = L'\\';
            wdir[wdir_len + name_len + 1] = 0;
            bore_expand_wildcard_files_r(b, proj_index, wdir, wdir_len + name_len + 1, pattern, depth + 1);
        }
        while (FindNextFileW(hFind, &fd));
        wdir[wdir_len] = 0;
        FindClose(hFind);
    }
    else if (rest)
    {
        /* Non-leaf segment — enumerate matching dirs, recurse with rest */
        memcpy(wpath, wdir, wdir_len * sizeof(WCHAR));
        MultiByteToWideChar(CP_UTF8, 0, pattern, seg_len, wpath + wdir_len, BORE_MAX_PATH - wdir_len);
        wpath[wdir_len + seg_len] = 0;
        hFind = FindFirstFileExW(wpath, FindExInfoBasic, &fd,
            FindExSearchLimitToDirectories, NULL, FIND_FIRST_EX_LARGE_FETCH);
        if (hFind == INVALID_HANDLE_VALUE)
            return;
        do
        {
            int name_len;
            if (!(fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY))
                continue;
            if (fd.dwFileAttributes & FILE_ATTRIBUTE_REPARSE_POINT)
                continue;
            if (fd.cFileName[0] == L'.' && (fd.cFileName[1] == 0 ||
                (fd.cFileName[1] == L'.' && fd.cFileName[2] == 0)))
                continue;
            name_len = (int)wcslen(fd.cFileName);
            if (wdir_len + name_len + 1 >= BORE_MAX_PATH)
                continue;
            memcpy(wdir + wdir_len, fd.cFileName, name_len * sizeof(WCHAR));
            wdir[wdir_len + name_len] = L'\\';
            wdir[wdir_len + name_len + 1] = 0;
            bore_expand_wildcard_files_r(b, proj_index, wdir, wdir_len + name_len + 1, rest, depth + 1);
        }
        while (FindNextFileW(hFind, &fd));
        wdir[wdir_len] = 0;
        FindClose(hFind);
    }
    else
    {
        /* Leaf segment — enumerate matching files */
        char fullpath_utf8[BORE_MAX_PATH];
        int dir_utf8_len;

        memcpy(wpath, wdir, wdir_len * sizeof(WCHAR));
        MultiByteToWideChar(CP_UTF8, 0, pattern, seg_len, wpath + wdir_len, BORE_MAX_PATH - wdir_len);
        wpath[wdir_len + seg_len] = 0;

        dir_utf8_len = WideCharToMultiByte(CP_UTF8, 0, wdir, wdir_len, fullpath_utf8, BORE_MAX_PATH, 0, 0);
        if (dir_utf8_len <= 0)
            return;
        hFind = FindFirstFileExW(wpath, FindExInfoBasic, &fd,
            FindExSearchNameMatch, NULL, FIND_FIRST_EX_LARGE_FETCH);
        if (hFind == INVALID_HANDLE_VALUE)
            return;
        do
        {
            int name_len;
            if (fd.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY)
                continue;
            name_len = WideCharToMultiByte(CP_UTF8, 0, fd.cFileName, -1,
                fullpath_utf8 + dir_utf8_len, BORE_MAX_PATH - dir_utf8_len, 0, 0);
            if (name_len > 0 && !bore_is_excluded_file(fullpath_utf8))
            {
                bore_file_t* f = (bore_file_t*)bore_alloc(&b->file_alloc, sizeof(bore_file_t));
                f->file = bore_strndup(b, fullpath_utf8, dir_utf8_len + name_len - 1);
                f->proj_index = proj_index;
                ++b->file_count;
            }
        }
        while (FindNextFileW(hFind, &fd));
        FindClose(hFind);
    }
}

static void bore_load_vcxproj_files(bore_t* b, int proj_index, const char* path)
{
    FILE* f;
    char buf[BORE_MAX_PATH];
    char filename_buf[BORE_MAX_PATH];
    char* filename_part;
    char* ext_part;
    int path_len;
    int skipFile = 0;
    BOOL is_csproj;

    f = fopen(path, "rb");
    if (!f)
        return;

    strcpy(filename_buf, path);
    filename_part = (char*)vim_strrchr((char_u*)filename_buf, '\\') + 1;
    path_len = filename_part - filename_buf;
    ext_part = (char*)vim_strrchr((char_u*)filename_buf, '.');
    is_csproj = ext_part > filename_part && 0 == STRNCMP((char*)ext_part, ".csproj", 7);

    while (0 == vim_fgets((char_u*)buf, sizeof(buf), f))
    {
        filename_part = strstr(buf, "Include=\"");
        if (filename_part)
        {
            /* Only process source file tags, skip assembly/project references */
            if (!strstr(buf, "<Compile ")
                && !strstr(buf, "<ClCompile ")
                && !strstr(buf, "<ClInclude ")
                && !strstr(buf, "<None ")
                && !strstr(buf, "<Content ")
                && !strstr(buf, "<CustomBuild ")
                && !strstr(buf, "<MASM ")
                && !strstr(buf, "<Natvis "))
                continue;
            filename_part += 9;
            char* end = strchr(filename_part, '"');
            if (end)
            {
                char* fn;
                int len = end - filename_part;
                filename_part[len] = 0;

                /* Skip unresolved MSBuild variables */
                if (strchr(filename_part, '$'))
                    continue;
                /* Skip build configurations (contain |) */
                if (strchr(filename_part, '|'))
                    continue;

                vim_strncpy(filename_buf + path_len, filename_part, len);
                if (len >= 2 && filename_part[1] == ':')
                {
                    fn = filename_part;
                }
                else
                {
                    fn = filename_buf;
                    len += path_len;
                }
                char* wildcard = (char*)vim_strchr((char_u*)fn, '*');
                if (!wildcard)
                {
                    skipFile = bore_is_excluded_file_n(fn, len);
                    if (!skipFile)
                    {
                        DWORD attr;
                        DWORD* pattr = bore_requires_fileattr(fn, len) ? &attr : NULL;
                        if (FAIL != bore_canonicalize(fn, buf, pattr)
                            && (!pattr || !(FILE_ATTRIBUTE_DIRECTORY & attr)))
                        {
                            bore_file_t* files = (bore_file_t*)bore_alloc(&b->file_alloc, sizeof(bore_file_t));
                            files->file = bore_strndup(b, buf, strlen(buf));
                            files->proj_index = proj_index;
                            ++b->file_count;
                        }
                    }
                    continue;
                }

                WCHAR wdir[BORE_MAX_PATH];
                WCHAR wtmp[BORE_MAX_PATH];
                char dir_buf[BORE_MAX_PATH];
                const char* last_sep = wildcard;
                int dir_len, wdir_len;
                while (last_sep > fn && last_sep[-1] != '\\' && last_sep[-1] != '/')
                    --last_sep;
                dir_len = (int)(last_sep - fn);
                vim_strncpy(dir_buf, fn, dir_len);
                MultiByteToWideChar(CP_UTF8, 0, dir_buf, -1, wtmp, BORE_MAX_PATH);
                wdir_len = (int)GetFullPathNameW(wtmp, BORE_MAX_PATH, wdir, NULL);
                if (wdir_len <= 0 || wdir_len >= BORE_MAX_PATH - 1)
                    continue;
                if (wdir[wdir_len - 1] != L'\\')
                    wdir[wdir_len++] = L'\\';
                wdir[wdir_len] = 0;
                bore_expand_wildcard_files_r(b, proj_index, wdir, wdir_len, last_sep, 0);
            }
        }
    }

    fclose(f);

    if (is_csproj)
    {
        WCHAR wdir[BORE_MAX_PATH];
        WCHAR wtmp[BORE_MAX_PATH];
        int wdir_len;
        filename_buf[path_len] = 0;
        MultiByteToWideChar(CP_UTF8, 0, filename_buf, -1, wtmp, BORE_MAX_PATH);
        wdir_len = (int)GetFullPathNameW(wtmp, BORE_MAX_PATH, wdir, NULL);
        if (wdir_len > 0 && wdir_len < BORE_MAX_PATH - 1)
        {
            if (wdir[wdir_len - 1] != L'\\')
                wdir[wdir_len++] = L'\\';
            wdir[wdir_len] = 0;
            bore_expand_wildcard_files_r(b, proj_index, wdir, wdir_len, "**\\*.cs", 0);
        }
    }
}

typedef struct bore_guid_map_t
{
    char child[36];
    char parent[36];
} bore_guid_map_t;

static int bore_extract_projects_and_files_from_sln(bore_t* b, const char* sln_path)
{
    regmatch_T regmatch;
    FILE* f;
    char buf[BORE_MAX_PATH];
    char buf2[BORE_MAX_PATH];
    int result = FAIL;
    int state = 0;
    int sln_path_dir_len = (char*)vim_strrchr((char_u*)sln_path, '\\') - sln_path + 1;

    regmatch.regprog = vim_regcomp((char_u*)"^Project(\"{.\\{-}}\") = \"\\(.\\{-}\\)\", \"\\(.\\{-}\\)\", \"{\\(.\\{-}\\)}\"", RE_MAGIC + RE_STRING);
    regmatch.rm_ic = 0;

    f = fopen(sln_path, "rb");
    if (!f)
    {
        goto done;
    }

    int guid_map_count = 0;
    bore_alloc_t guid_map_alloc;
    bore_prealloc(&guid_map_alloc, 256*(sizeof(bore_guid_map_t)));

    while (0 == vim_fgets((char_u*)buf, sizeof(buf), f))
    {
        if (state == 0)
        {
            if ('\t' == buf[0] || ' ' == buf[0])
            {
                if (strstr(buf, "GlobalSection(NestedProjects) = preSolution"))
                    state = 2;
                else if (strstr(buf, "GlobalSection(SolutionConfigurationPlatforms) = preSolution"))
                    state = 3;
            }
            else if (vim_regexec_nl(&regmatch, buf, (colnr_T)0))
            {
                state = 1;
                bore_proj_t* proj = (bore_proj_t*)bore_alloc(&b->proj_alloc, sizeof(bore_proj_t));
                ++b->proj_count;
                proj->project_sln_name = bore_strndup(b, regmatch.startp[1], regmatch.endp[1] - regmatch.startp[1]);
                proj->project_sln_guid = bore_strndup(b, regmatch.startp[3], regmatch.endp[3] - regmatch.startp[3]);
                proj->project_sln_path = 0;

                if (0 == STRNCMP(regmatch.startp[1], regmatch.startp[2], regmatch.endp[2] - regmatch.startp[2]))
                {
                    proj->project_file_path = 0; // project is only a solution filter
                }
                else
                {
                    vim_strncpy(buf2, regmatch.startp[2], regmatch.endp[2] - regmatch.startp[2]);
                    if (FAIL != bore_canonicalize(buf2, buf, 0))
                        proj->project_file_path = bore_strndup(b, buf, strlen(buf));
                    else
                        proj->project_file_path = 0;
                }

                // TODO-pkack: copy and modify string in one step
                // msbuild expects all '.' in project names to be changed to '_'
                char* c = bore_str(b, proj->project_sln_name);
                for (; c && 0 != *c; ++c)
                {
                    if ('.' == *c)
                        *c = '_';
                }
            }
        }
        else if (state == 1)
        {
            if (strstr(buf, "ProjectSection(SolutionItems) = preProject"))
            {
                // skip
            }
            else if (strstr(buf, "EndProjectSection"))
            {
                state = 0;
            }
            else
            {
                char* ends = strstr(buf, " = ");
                if (ends)
                {
                    DWORD attr = 0;
                    int skipFile = 0;

                    *ends = 0;
                    skipFile = bore_is_excluded_file(&buf[2]); // "\t\t"
                    if (!skipFile && FAIL != bore_canonicalize(&buf[2], buf, &attr))
                    {
                        if (!(FILE_ATTRIBUTE_DIRECTORY & attr))
                        {
                            bore_file_t* files = (bore_file_t*)bore_alloc(&b->file_alloc, sizeof(bore_file_t));
                            files->file = bore_strndup(b, buf, strlen(buf));
                            files->proj_index = b->proj_count - 1;
                            ++b->file_count;
                        }
                    }
                }
                else
                {
                    state = 0;
                }
            }
        }
        else if (state == 2)
        {
            if (strstr(buf, "EndGlobalSection"))
            {
                state = 0;
            }
            else
            {
                char* ends = strstr(buf, "} = {");
                if (ends)
                {
                    *ends = 0;
                    size_t len = strlen(buf + 3); // "\t\t{"
                    bore_guid_map_t* proj_guid = (bore_guid_map_t*)bore_alloc(&guid_map_alloc, sizeof(bore_guid_map_t));
                    ++guid_map_count;
                    memcpy(proj_guid->child, buf + 3, len < 36 ? len : 36);
                    len = strlen(ends + 5);
                    memcpy(proj_guid->parent, ends + 5, len < 36 ? len : 36);
                }
                else
                {
                    state = 0;
                }
            }
        }
        // Solution configurations
        else if (state == 3)
        {
            if (strstr(buf, "EndGlobalSection"))
            {
                state = 0;
            }
            else
            {
		// \t\tRelease|Win32 = Release|Win32
                char* ends = strstr(buf, " = ");
                char* div = strchr(buf + 2, '|');
                if (ends && div && div < ends)
                {
                    *ends = 0;
                    *div = 0;
                    bore_sln_config_t* sln_config = (bore_sln_config_t*)bore_alloc(&b->config_alloc, sizeof(bore_sln_config_t));
                    ++b->config_count;
                    sln_config->config = bore_strndup(b, buf + 2, div - buf - 2);
                    sln_config->platform = bore_strndup(b, div + 1, ends - div - 1);
                }
                else
                {
                    state = 0;
                }
            }
        }
    }

    // Project filter solution tree lookup
    {
        bore_proj_t* proj = (bore_proj_t*)b->proj_alloc.base;
        bore_guid_map_t* guid_map = (bore_guid_map_t*)guid_map_alloc.base;
        int i, j, k;

        for (i = 0; i < b->proj_count; ++i)
        {
            if (0 == proj[i].project_sln_path)
            {
                for (j = 0; j < guid_map_count; ++j)
                {
                    if (0 == STRNCMP(bore_str(b, proj[i].project_sln_guid), guid_map[j].child, 36))
                    {
                        for (k = 0; k < i; ++k)
                        {
                            if (0 == STRNCMP(guid_map[j].parent, bore_str(b, proj[k].project_sln_guid), 36))
                            {
                                size_t len = strlen(bore_str(b, proj[k].project_sln_name));
                                vim_strncpy(buf, bore_str(b, proj[k].project_sln_name), len);
                                buf[len] = '\\';
                                strcpy(buf + len + 1, bore_str(b, proj[i].project_sln_name));
                                proj[i].project_sln_name = bore_strndup(b, buf, strlen(buf));
                                break;
                            }
                        }
                        if (k < i)
                            break;
                    }
                }
            }
        }
    }

    fclose(f);
    vim_free(regmatch.regprog);
    bore_alloc_free(&guid_map_alloc);

    result = OK;

done:
    return result;
}

static int bore_find_dir_proj_for_file(bore_t* b, char* fn)
{
    bore_proj_t* projects = (bore_proj_t*)b->proj_alloc.base;
    int best_score = 0;
    int best_i = 0;
    int i;
    char* rel_path_start = fn + b->sln_dir_len;
    if (strchr(rel_path_start, '\\'))
    {
        for (i = 1; i < b->proj_count; ++i)
        {
            int score = bore_str_match_score(rel_path_start, bore_str(b, projects[i].project_sln_name));
            if (score > best_score)
            {
                best_score = score;
                best_i = i;
            }
        }
    }
    return best_i;
}

static int bore_extract_projects_and_files_from_dir(bore_t* b, const char* sln_path)
{
    BOOL is_git_repo;
    {
        ++emsg_silent;
        char *cmd = "git rev-parse --is-inside-work-tree";
        char* res = get_cmd_output(cmd, NULL, SHELL_READ & SHELL_SILENT, NULL);
        is_git_repo = res && !STRNCMP(res, "true", 4);
        --emsg_silent;
    }
    char* subdir_cmd = is_git_repo ? "git ls-tree -d --name-only HEAD" : "dir /b /ad";
    char* files_cmd = is_git_repo ? "git ls-files" : "dir /s /b /a-d";

    size_t sln_path_len = strlen(sln_path);
    char buf[BORE_MAX_PATH];
    char* output;
    char *line;
    DWORD attr;
    int skipFile;
    int len;
    int i;

    output = get_cmd_output(subdir_cmd, 0, SHELL_READ & SHELL_SILENT, &len);
    if (!output)
        goto done;

    // add root dir as base project
    {
        bore_proj_t* proj = (bore_proj_t*)bore_alloc(&b->proj_alloc, sizeof(bore_proj_t));
        ++b->proj_count;
        proj->project_sln_name = bore_strndup(b, ".", 1);
        proj->project_sln_guid = 0;
        proj->project_sln_path = proj->project_sln_name;
        proj->project_file_path = b->sln_path;
    }

    // add all first level sub dirs as projects
    for (i = 0; i < len; ++i)
    {
        line = output + i;
        while (i < len && output[i] != '\r' && output[i] != '\n')
            ++i;
        output[i] = 0;
        if (output[i+1] == '\n')
            ++i;

        if (FAIL != bore_canonicalize(line, buf, &attr))
        {
            if ((FILE_ATTRIBUTE_DIRECTORY & attr))
            {
                bore_proj_t* proj = (bore_proj_t*)bore_alloc(&b->proj_alloc, sizeof(bore_proj_t));
                ++b->proj_count;
                proj->project_sln_name = bore_strndup(b, buf + sln_path_len, strlen(buf + sln_path_len));
                proj->project_sln_guid = 0;
                proj->project_sln_path = proj->project_sln_name;
                proj->project_file_path = bore_strndup(b, buf, strlen(buf));
            }
        }
    }

    output = get_cmd_output(files_cmd, 0, SHELL_READ & SHELL_SILENT, &len);
    if (!output)
        goto done;

    // add every listed file
    for (i = 0; i < len; ++i)
    {
        line = output + i;
        while (i < len && output[i] != '\r' && output[i] != '\n')
            ++i;
        output[i] = 0;
        if (output[i+1] == '\n')
            ++i;

        skipFile = bore_is_excluded_file(line);
        if (!skipFile && FAIL != bore_canonicalize(line, buf, &attr))
        {
            if (!(FILE_ATTRIBUTE_DIRECTORY & attr))
            {
                int proj_index = bore_find_dir_proj_for_file(b, buf);
                bore_file_t* files = (bore_file_t*)bore_alloc(&b->file_alloc, sizeof(bore_file_t));
                files->file = bore_strndup(b, buf, strlen(buf));
                files->proj_index = proj_index;
                ++b->file_count;
            }
        }
    }

done:
    return OK;
}

static int bore_extract_files_from_projects(bore_t* b)
{
    bore_proj_t* proj = (bore_proj_t*)b->proj_alloc.base;
    int i;

    bore_visited_reset();

    for (i = 0; i < b->proj_count; ++i)
    {
        if (proj[i].project_file_path)
        {
            bore_load_vcxproj_files(b, i, bore_str(b, proj[i].project_file_path));
        }
    }

    bore_visited_reset();

    return OK;
}

static int bore_find_filename(void* ctx, const void* vx, const void* vy)
{
    bore_t* b = (bore_t*)ctx;
    char* x_path = (char*)vx;
    bore_file_t* y = (bore_file_t*)vy;
    const char* y_path = bore_str(b, y->file);
    const int i = bore_str_match_len(x_path, y_path);
    BOOL xi_is_file = x_path[i] == '\0' || !strchr(x_path + i, '\\');
    BOOL yi_is_file = y_path[i] == '\0' || !strchr(y_path + i, '\\');
    // group-directories-first
    if (xi_is_file ^ yi_is_file)
        return yi_is_file - xi_is_file;
    // _stricmp result
    return TOLOWER_LOC(x_path[i]) - TOLOWER_LOC(y_path[i]);
}

static int bore_sort_files(void* ctx, const void* vx, const void* vy)
{
    bore_t* b = (bore_t*)ctx;
    const bore_file_t* x = (bore_file_t*)vx;
    const bore_file_t* y = (bore_file_t*)vy;
    const char* fn = bore_str(b, x->file);
    return bore_find_filename(b, fn, y);
}

static int bore_sort_filenames(const void* ctx, const void* vx, const void* vy)
{
    char x_path[BORE_MAX_PATH];
    char y_path[BORE_MAX_PATH];
    const char* cur_path = (const char*)ctx;
    const char* x = *(const char**)vx;
    const char* y = *(const char**)vy;
    bore_canonicalize(x, x_path, 0);
    bore_canonicalize(y, y_path, 0);
    const int x_score = bore_str_match_score(cur_path, x_path);
    const int y_score = bore_str_match_score(cur_path, y_path);
    const int diff = y_score - x_score;
    if (diff)
	return diff;
    return STRICMP(x_path + x_score, y_path + y_score);
}

void bore_sortfilenames(char_u** files, int count, char_u* current)
{
    char current_path[BORE_MAX_PATH];
    if (FAIL == bore_canonicalize(current, current_path, 0))
        return;
    BORE_VIMPROFILE_INIT;
    BORE_VIMPROFILE_START;
    qsort_s(&files[0], count, sizeof(char_u*), bore_sort_filenames, current_path);
    BORE_VIMPROFILE_STOP("bore_sortfilenames");
}

typedef struct bore_match_sort_t
{
    bore_t* b;
    const char* cur_file;
} bore_match_sort_t;

static int bore_sort_matches(void* ctx, const void* vx, const void* vy)
{
    bore_t* b = ((bore_match_sort_t*)ctx)->b;
    const char* cur_file = ((bore_match_sort_t*)ctx)->cur_file;
    bore_file_t* files = (bore_file_t*)b->file_alloc.base;
    bore_match_t* x = (bore_match_t*)vx;
    bore_match_t* y = (bore_match_t*)vy;
    if (x->file_index != y->file_index)
    {
        const char* x_path = bore_str(b, files[x->file_index].file);
        const char* y_path = bore_str(b, files[y->file_index].file);
        const int x_score = bore_str_match_score(cur_file, x_path);
        const int y_score = bore_str_match_score(cur_file, y_path);
        const int diff = y_score - x_score;
        if (diff)
            return diff;
        return STRICMP(x_path + x_score, y_path + y_score);
    }
    const int row_diff = x->row - y->row;
    if (row_diff)
        return row_diff;
    return x->column - y->column;
}

static int bore_sort_and_cleanup_files(bore_t* b)
{
    bore_file_t* files = (bore_file_t*)b->file_alloc.base;

    if (b->file_count == 0)
        return OK;

    // sort
    qsort_s(files, b->file_count, sizeof(bore_file_t), bore_sort_files, b);

    // uniq
    {
        bore_file_t* pr = files + 1;
        bore_file_t* pw = files + 1;
        bore_file_t* pend = files + b->file_count;
        int n;
        while(pr < pend)
        {
            if (0 != STRICMP(bore_str(b, pr->file), bore_str(b, (pr-1)->file)))
            {
                *pw++ = *pr++;
            }
            else
            {
                ++pr;
            }
        }
        n = pw - files;

        // resize file-array
        bore_alloc_trim(&b->file_alloc, sizeof(bore_file_t)*(b->file_count - n));
        b->file_count = n;
    }

    return OK;
}

static int bore_build_extension_list(bore_t* b)
{
    bore_file_t* files = (bore_file_t*)b->file_alloc.base;
    bore_alloc(&b->file_ext_alloc, b->file_count * sizeof(u32));
    u32* ext_hash = (u32*)b->file_ext_alloc.base;
    u32 i;
    for (i = 0; i < (u32)b->file_count; ++i)
    {
        char* path = bore_str(b, files[i].file);
        u32 path_len = (u32)strlen(path);
        char* ext = vim_strrchr(path, '.');

        ext = ext ? ext + 1 : path + path_len;
        ext_hash[i] = bore_string_hash(ext);
    }

    return OK;
}

static int bore_sort_toggle_entry(const void* vx, const void* vy)
{
    const bore_toggle_entry_t* x = (const bore_toggle_entry_t*)vx;
    const bore_toggle_entry_t* y = (const bore_toggle_entry_t*)vy;
    if (x->basename_hash > y->basename_hash)
        return 1;
    else if (x->basename_hash < y->basename_hash)
        return -1;
    else
        return x->extension_index - y->extension_index;
}

static int bore_build_toggle_index(bore_t* b)
{
    bore_file_t* files = (bore_file_t*)b->file_alloc.base;
    u32* file_ext = (u32*)b->file_ext_alloc.base;
    u32 i;
    u32 seq[] =
    {
        bore_string_hash("cpp"),
        bore_string_hash("cxx"),
        bore_string_hash("c"),
        bore_string_hash("cc"),
        bore_string_hash("inl"),
        bore_string_hash("inc"),
        bore_string_hash("hpp"),
        bore_string_hash("hxx"),
        bore_string_hash("h"),
        bore_string_hash("hh"),
        bore_string_hash("pro"),
        bore_string_hash("asm"),
        bore_string_hash("s"),
    };
    bore_prealloc(&b->toggle_index_alloc, b->file_count * sizeof(bore_toggle_entry_t));
    b->toggle_entry_count = 0;
    for (i = 0; i < (u32)b->file_count; ++i)
    {
        int j;
        int ext_index = -1;
        for (j = 0; j < sizeof(seq)/sizeof(seq[0]); ++j)
            if (seq[j] == file_ext[i])
            {
                ext_index = j;
                break;
            }

        if (-1 == ext_index)
            continue;

        char* path = bore_str(b, files[i].file);
        u32 path_len = (u32)strlen(path);
        char* ext = vim_strrchr(path, '.');
        char* basename = vim_strrchr(path, '\\');

        ext = ext ? ext + 1 : path + path_len;
        basename = basename ? basename + 1 : path;

        bore_toggle_entry_t* e = (bore_toggle_entry_t*)bore_alloc(&b->toggle_index_alloc,
            sizeof(bore_toggle_entry_t));
        e->file = files[i].file;
        e->extension_index = ext_index;
        e->basename_hash = bore_string_hash_n(basename, (int)(ext - basename));
        b->toggle_entry_count++;
    }
    qsort(b->toggle_index_alloc.base, b->toggle_entry_count, sizeof(bore_toggle_entry_t),
            bore_sort_toggle_entry);

    return OK;
}

static int bore_write_filelist_to_file(bore_t* b)
{
    FILE* f;
    char* tmp_file;
    int i;
    tmp_file = vim_tempname('b', TRUE);
    if (!tmp_file)
        return FAIL;
    f = fopen(tmp_file, "w");
    if (!f)
        return FAIL;
    for (i = 0; i < b->file_count; ++i)
    {
        char *fn = bore_rel_path(b, ((bore_file_t*)b->file_alloc.base)[i].file);
        fprintf(f, "%s\n", fn);
    }
    fclose(f);
    b->sln_filelist = bore_strndup(b, tmp_file, strlen(tmp_file));
    return OK;
}

static void bore_load_ini(bore_ini_t* ini)
{
    SYSTEM_INFO sys_info;
    GetSystemInfo(&sys_info);
    ini->cpu_cores = (int)sys_info.dwNumberOfProcessors;
    ini->borebuf_height = 30;
}

static int bore_extract_sln_from_path(bore_t* b, const char* path)
{
    char buf[BORE_MAX_PATH];
    DWORD path_attr = 0;
    if (FAIL == bore_canonicalize((char*)path, buf, &path_attr))
        return FAIL;

    size_t path_len = strlen(buf);
    b->sln_dir = bore_strndup(b, buf, path_len + 1); // trailing backslash
    char* sln_dir_str = bore_str(b, b->sln_dir);

    if (path_attr & FILE_ATTRIBUTE_DIRECTORY)
    {
        b->sln_path = b->sln_dir;

        char* pc = vim_strrchr(sln_dir_str, '.');
        // Special case. If the solution path is .git folder, then assume
        // code paths start one level up from that
        if (pc && 0 == STRNCMP(pc, ".git", 4) && (pc[4] == '\\' || pc[4] == 0))
            *(pc - 1) = 0; // Remove trailing backslash
        else
        {
            pc = sln_dir_str + path_len - 1;
            if (*pc == '\\')
                *pc = 0; // Remove trailing backslash
        }

        // set solution name to deepest directory name
        pc = vim_strrchr(sln_dir_str, '\\');
        if (pc)
            ++pc;
        else
            pc = sln_dir_str;
        b->sln_name = bore_strndup(b, pc, strlen(pc));

        // Add trailing backslash
        pc = sln_dir_str + strlen(sln_dir_str);
        *pc++ = '\\';
        *pc = 0;
    }
    else
    {
        b->sln_path = bore_strndup(b, buf, path_len);

        char* pc = vim_strrchr(sln_dir_str, '\\');

        // set solution name to file name part of path
        if (pc)
        {
            b->sln_name = b->sln_path + (pc - sln_dir_str) + 1;
            pc[1] = 0; // Keep trailing backslash
        }
        else
        {
            b->sln_name = b->sln_path;
        }
    }

    b->sln_dir_len = strlen(bore_str(b, b->sln_dir));
    return OK;
}

static int bore_match_sln_config(bore_t* b, char* str)
{
    const char* config = str;
    const char* platform = str;
    char* div = strchr(str, '|');

    if (NULL == div)
        div = strchr(str, ' ');

    if (NULL != div)
    {
        *div = 0;
        platform = div + 1;
    }

    // best match
    bore_sln_config_t* sln_configs = (bore_sln_config_t*)b->config_alloc.base;
    int best_score = 0;
    int best_i = -1;
    int i;
    for (i = 0; i < b->config_count; ++i)
    {
        int config_score = bore_str_match_score(config, bore_str(b, sln_configs[i].config));
        int platform_score = bore_str_match_score(platform, bore_str(b, sln_configs[i].platform));
        int total_score = config_score + platform_score;
        if (total_score > best_score)
        {
            best_score = total_score;
            best_i = i;
        }
    }
    return best_i;
}

static int bore_match_proj(bore_t* b, char* str)
{
    bore_proj_t* projects = (bore_proj_t*)b->proj_alloc.base;
    int best_score = 0;
    int best_i = -1;
    int i;
    for (i = 0; i < b->proj_count; ++i)
    {
        int score = bore_str_match_score(str, bore_str(b, projects[i].project_sln_name));
        if (score > best_score)
        {
            best_score = score;
            best_i = i;
        }
    }
    return best_i;
}

static void bore_set_proj(bore_t* b, int proj_index)
{
    char buf[BORE_MAX_PATH];
    bore_proj_t* projects = (bore_proj_t*)b->proj_alloc.base;

    if (proj_index >=0)
        sprintf(buf, "let g:bore_proj_path=\'%s\'",
            bore_rel_path(b, projects[proj_index].project_file_path));
    else
        strcpy(buf, "let g:bore_proj_path=\'\'");
    do_cmdline_cmd(buf);
}

static void bore_set_sln_config(bore_t* b, int sln_config)
{
    char buf[BORE_MAX_PATH];
    bore_sln_config_t* sln_configs = (bore_sln_config_t*)b->config_alloc.base;

    b->sln_config = sln_config;
    if (b->sln_config >=0)
        sprintf(buf, "let g:bore_sln_config=\'%s|%s\'",
            bore_str(b, sln_configs[b->sln_config].config),
            bore_str(b, sln_configs[b->sln_config].platform));
    else
        strcpy(buf, "let g:bore_sln_config=\'\'");
    do_cmdline_cmd(buf);
}

static void bore_init_sln_config(bore_t* b)
{
    int sln_config = -1;
    if (b->config_count > 0)
    {
        sln_config = bore_match_sln_config(b, "Release|x64");
        if (sln_config < 0)
        {
            sln_config = bore_match_sln_config(b, "Win32");
            if (sln_config < 0)
            {
                sln_config = 0; // no match, pick the first one
            }
        }
    }
    bore_set_sln_config(b, sln_config);
}

struct bore_async_execute_context_t
{
    HANDLE wait_thread;
    PROCESS_INFORMATION spawned_process;
    HANDLE result_handle;
    DWORD completed;
    DWORD duration;
    DWORD exit_code;
    char title[256];
};

static struct bore_async_execute_context_t g_bore_async_execute_context;

static void bore_load_sln(const char* path)
{
    g_bore_async_execute_context.wait_thread = INVALID_HANDLE_VALUE;
    g_bore_async_execute_context.result_handle = INVALID_HANDLE_VALUE;

    char buf[BORE_MAX_PATH];
    int i;
    char* c;
    bore_t* b = (bore_t*)alloc(sizeof(bore_t));
    memset(b, 0, sizeof(bore_t));

    bore_prealloc(&b->data_alloc, 8*1024*1024);
    bore_prealloc(&b->file_alloc, sizeof(bore_file_t)*64*1024);
    bore_prealloc(&b->proj_alloc, sizeof(bore_proj_t)*256);
    bore_prealloc(&b->config_alloc, sizeof(bore_proj_t)*8);

    for (i = 0; i < BORE_SEARCH_JOBS; ++i)
    {
        bore_prealloc(&b->search[i].filedata, 1*1024*1024);
    }

    // Allocate something small, so that we can use offset 0 as NULL
    c = (char*)bore_alloc(&b->data_alloc, sizeof(char));
    *c = 0;

    if (FAIL == bore_extract_sln_from_path(b, path))
        goto fail;

    sprintf(buf, "cd %s", bore_str(b, b->sln_dir));
    ++msg_silent;
    do_cmdline_cmd(buf);
    --msg_silent;

    if (!g_bore || STRICMP(bore_str(g_bore, g_bore->sln_name), bore_str(b, b->sln_name)))
    {
        serverSetName(bore_str(b, b->sln_name));
    }

    bore_load_ini(&b->ini);

    BORE_VIMPROFILE_INIT;

    if (bore_is_sln_directory(b))
    {
        BORE_VIMPROFILE_START;
        if (FAIL == bore_extract_projects_and_files_from_dir(b, bore_str(b, b->sln_path)))
            goto fail;
        BORE_VIMPROFILE_STOP("bore_extract_projects_and_files_from_dir");
    }
    else
    {
        BORE_VIMPROFILE_START;
        if (FAIL == bore_extract_projects_and_files_from_sln(b, bore_str(b, b->sln_path)))
            goto fail;
        BORE_VIMPROFILE_STOP("bore_extract_projects_and_files_from_sln");

        BORE_VIMPROFILE_START;
        if (FAIL == bore_extract_files_from_projects(b))
            goto fail;
        BORE_VIMPROFILE_STOP("bore_extract_files_from_projects");
    }

    BORE_VIMPROFILE_START;
    bore_init_sln_config(b);
    BORE_VIMPROFILE_STOP("bore_init_sln_config");

    BORE_VIMPROFILE_START;
    if (FAIL == bore_sort_and_cleanup_files(b))
        goto fail;
    BORE_VIMPROFILE_STOP("bore_sort_and_cleanup_files");

    BORE_VIMPROFILE_START;
    if (FAIL == bore_build_extension_list(b))
        goto fail;
    BORE_VIMPROFILE_STOP("bore_build_extension_list");

    BORE_VIMPROFILE_START;
    if (FAIL == bore_build_toggle_index(b))
        goto fail;
    BORE_VIMPROFILE_STOP("bore_build_toggle_index");

    BORE_VIMPROFILE_START;
    if (FAIL == bore_write_filelist_to_file(b))
        goto fail;
    BORE_VIMPROFILE_STOP("bore_write_filelist_to_file");

    sprintf(buf, "let g:bore_base_dir=\'%s\'", bore_str(b, b->sln_dir));
    do_cmdline_cmd(buf);

    sprintf(buf, "let g:bore_filelist_file=\'%s\'", bore_str(b, b->sln_filelist));
    do_cmdline_cmd(buf);

    bore_set_proj(b, -1);

    bore_free(g_bore);
    g_bore = b;
    return;

fail:
    bore_free(b);
    semsg(_("Could not open solution %s"), path);
    return;
}

static void bore_print_sln(DWORD elapsed)
{
    if (g_bore)
    {
        if (elapsed)
        {
            vim_snprintf(IObuff, IOSIZE, "%s; %d projects; %d files; %u ms",
                bore_str(g_bore, g_bore->sln_path),
                g_bore->proj_count,
                g_bore->file_count, elapsed);
        }
        else
        {
            vim_snprintf(IObuff, IOSIZE, "%s; %d projects; %d files",
                bore_str(g_bore, g_bore->sln_path),
                g_bore->proj_count,
                g_bore->file_count);
        }
        msg(IObuff);
    }
}

static int bore_canonicalize(const char* src, char* dst, DWORD* attr)
{
    WCHAR wbuf[BORE_MAX_PATH];
    WCHAR wbuf2[BORE_MAX_PATH];
    DWORD fnresult;
    int result = MultiByteToWideChar(CP_UTF8, 0, src, -1, wbuf, BORE_MAX_PATH);
    if (result <= 0)
        return FAIL;
    fnresult = GetFullPathNameW(wbuf, BORE_MAX_PATH, wbuf2, 0);
    if (!fnresult)
        return FAIL;
    if (attr)
    {
        *attr = GetFileAttributesW(wbuf);
        if (*attr == INVALID_FILE_ATTRIBUTES)
            return FAIL;
    }
    result = WideCharToMultiByte(CP_UTF8, 0, wbuf2, -1, dst, BORE_MAX_PATH, 0, 0);
    if (!result)
        return FAIL;
    return OK;
}

static u32 bore_string_hash(const char *str)
{
    return bore_string_hash_n(str, -1);
}

static u32 bore_string_hash_n(const char *str, int n)
{
    u32 h;
    u8 *p = (u8*)str;
    u8 *pend = p + n;

    h = 0;
    for (; p != pend && *p != '\0'; p++)
        h = 33 * h + TOLOWER_LOC(*p);
    return h + (h >> 5);
}

static void bore_display_search_result(bore_t* b, const char* arg, const char* filename, int found)
{
    exarg_T eap;
    char* title = (char*)alloc(100);
    vim_snprintf(title, 100, "borefind %s; %d%s matching lines", arg, found > 0 ? found : -found, found < 0 ? " (truncated)" : "");

    memset(&eap, 0, sizeof(eap));
    eap.cmdidx = CMD_cgetfile;
    eap.arg = (char*)filename;
    eap.cmdlinep = &title;
    ex_cfile(&eap);

    memset(&eap, 0, sizeof(eap));
    eap.cmdidx = CMD_cwindow;
    ex_copen(&eap);

    vim_free(title);
}

static void bore_save_match_to_file(bore_t* b, FILE* cf, const bore_match_t* match, int match_count)
{
    int i;
    for (i = 0; i < match_count; ++i, ++match)
    {
        char* fn = bore_rel_path(b, ((bore_file_t*)(b->file_alloc.base))[match->file_index].file);
        fprintf(cf, "%s:%d:%d:%s\n", fn, match->row, match->column + 1, match->line);
    }
}

static int bore_find(bore_t* b, const char* arg, bore_search_t* search)
{
    int found = 0;
    int display_count = 0;
    char_u *tmp = vim_tempname('f', TRUE);
    FILE* cf = 0;
    bore_match_t* match = 0;
    int truncated = 0;

    match = (bore_match_t*)alloc(search->match_count * sizeof(bore_match_t));

    int threadCount = 8;
    const char_u* threadCountStr = get_var_value((char_u *)"g:bore_search_thread_count");
    if (threadCountStr)
    {
        threadCount = atoi(threadCountStr);
    }

    BORE_VIMPROFILE_INIT;
    BORE_VIMPROFILE_START;

    found = bore_dofind(b, threadCount, &truncated, match, search->match_count, search);
    if (0 == found)
        goto fail;

    if (found <= BORE_MAX_QUICKFIX_ITEMS)
    {
        display_count = found;
    }
    else
    {
        display_count = BORE_MAX_QUICKFIX_ITEMS;
        truncated = 1;
    }

    BORE_VIMPROFILE_STOP("bore_dofind");

    if (search->options & BS_SORTRESULT)
    {
        BORE_VIMPROFILE_START;
        bore_file_t* files = (bore_file_t*)b->file_alloc.base;
        bore_match_sort_t match_sort_context;
        match_sort_context.b = b;
        match_sort_context.cur_file = bore_str(b, files[search->file_index].file);
        qsort_s(match, found, sizeof(bore_match_t), bore_sort_matches, &match_sort_context);
        BORE_VIMPROFILE_STOP("bore_sort_search_result");
    }

    BORE_VIMPROFILE_START;

    cf = mch_fopen((char *)tmp, "wb");
    if (cf == NULL)
    {
        semsg(_(e_cant_open_file_str), tmp);
        goto fail;
    }
    bore_save_match_to_file(b, cf, match, display_count);

    fclose(cf);

    bore_display_search_result(b, arg, tmp, truncated ? -found : found);
    mch_remove(tmp);

    BORE_VIMPROFILE_STOP("bore_display_search_result");

fail:
    vim_free(tmp);
    vim_free(match);
    if (cf) fclose(cf);
    return truncated ? -found : found;
}

// Display filename in the borebuf.
// Window height is at least minheight (if possible)
// mappings is a null-terminated array of strings with buffer mappings of the form "<key> <command>"
static void bore_show_borebuf(bore_t* b, const char* filename, int minheight, const char** mappings)
{
    char_u  maparg[512];
    win_T   *wp;
    int    empty_fnum = 0;
    int    alt_fnum = 0;
    buf_T  *buf;
    FILE   *filelist_fd = 0;
    int    n;

#ifdef FEAT_GUI
    need_mouse_correct = TRUE;
#endif

    // Re-use an existing help window or open a new one.
    if (!curwin->w_buffer->b_borebuf)
    {
        FOR_ALL_WINDOWS(wp)
            if (wp->w_buffer != NULL && wp->w_buffer->b_borebuf)
                break;
        if (wp != NULL && wp->w_buffer->b_nwindows > 0)
            win_enter(wp, TRUE);
        else
        {
	    // Split off help window; put it at far top if no position
	    // specified, the current window is vertically split and
	    // narrow.
	    n = WSP_HELP;
	    if (cmdmod.cmod_split == 0 && curwin->w_width != Columns
		    && curwin->w_width < 80)
		n |= p_sb ? WSP_BOT : WSP_TOP;
	    if (win_split(0, n) == FAIL)
		goto erret;

	    if (curwin->w_height < p_hh)
		win_setheight((int)p_hh);

            alt_fnum = curbuf->b_fnum;
            // Piggyback on the help window which has the properties we want for borebuf too.
            // (readonly, can't insert text, etc)
            (void)do_ecmd(0, (char*)filename, NULL, NULL, ECMD_LASTL,
		    ECMD_HIDE + ECMD_SET_HELP,
                    NULL);  // buffer is still open, don't store info
            if ((cmdmod.cmod_flags & CMOD_KEEPALT) == 0)
                curwin->w_alt_fnum = alt_fnum;
            empty_fnum = curbuf->b_fnum;

            // This is the borebuf
            curwin->w_buffer->b_borebuf = 1;
        }
    }

    // Press enter to open the file on the current line
    while(*mappings)
    {
        sprintf(maparg, "<buffer> %s", *mappings);
        if (0 != do_map(MAPTYPE_MAP, maparg, MODE_NORMAL, FALSE))
            goto erret;
        ++mappings;
    }

    if (!p_im)
        restart_edit = 0;           /* don't want insert mode in help file */

    /* Delete the empty buffer if we're not using it.  Careful: autocommands
     * may have jumped to another window, check that the buffer is not in a
     * window. */
    if (empty_fnum != 0 && curbuf->b_fnum != empty_fnum)
    {
        buf = buflist_findnr(empty_fnum);
        if (buf != NULL && buf->b_nwindows == 0)
            wipe_buffer(buf, TRUE);
    }

    /* keep the previous alternate file */
    if (alt_fnum != 0 && curwin->w_alt_fnum == empty_fnum && ((cmdmod.cmod_flags & CMOD_KEEPALT) == 0))
        curwin->w_alt_fnum = alt_fnum;

    return;
erret:
    emsg(_("Could not open borebuf"));
}

static void bore_print_build()
{
    if (1 == g_bore_async_execute_context.completed)
    {
        if (0 == g_bore_async_execute_context.exit_code)
        {
            vim_snprintf(IObuff, IOSIZE,
                "%s; success; %d seconds",
                g_bore_async_execute_context.title,
                g_bore_async_execute_context.duration);
            msg_attr(IObuff, HL_ATTR(HLF_R));
        }
        else
        {
            vim_snprintf(IObuff, IOSIZE,
                "%s; failed with exit code %d; %d seconds",
                g_bore_async_execute_context.title,
                g_bore_async_execute_context.exit_code,
                g_bore_async_execute_context.duration);
            msg_attr(IObuff, HL_ATTR(HLF_E));
        }
    }
    else if (0 == g_bore_async_execute_context.completed)
    {
        vim_snprintf(IObuff, IOSIZE,
            "%s; running; %d seconds...",
            g_bore_async_execute_context.title,
            g_bore_async_execute_context.duration);
        msg(IObuff);
    }
    else
    {
        vim_snprintf(IObuff, IOSIZE,
            "%s; failed to launch",
            g_bore_async_execute_context.title);
        msg_attr(IObuff, HL_ATTR(HLF_E));
    }
}

void bore_async_execute_update(DWORD flags)
{
    DWORD first = flags & (1 << 31);
    DWORD completed = flags & (1 << 30);
    DWORD bytes_read = 0;
    DWORD bytes_avail = 0;
    int errors = 0;
    char buffer[4096];

    BORE_VIMPROFILE_INIT;
    BORE_VIMPROFILE_START;

    int	saved_need_wait_return = need_wait_return;
    int	saved_msg_nowait = msg_nowait;
    need_wait_return = FALSE;
    msg_nowait = TRUE;

    for (;;)
    {
        BOOL result = PeekNamedPipe(
            g_bore_async_execute_context.result_handle,
            NULL,
            0,
            NULL,
            &bytes_avail,
            NULL);

        if (!result)
        {
            if (!completed)
                msg_attr(_("bore_async_execute_update: Failed to peek pipe"), HL_ATTR(HLF_E));
            break;
        }
        else if (bytes_avail == 0)
        {
            if (!completed)
                msg_attr(_("bore_async_execute_update: No available data in pipe"), HL_ATTR(HLF_E));
            break;
        }

        result = ReadFile(
            g_bore_async_execute_context.result_handle,
            &buffer[1],
            sizeof(buffer) - 3,
            &bytes_read,
            NULL);

        if (!result)
        {
            msg_attr(_("bore_async_execute_update: Read file error"), HL_ATTR(HLF_E));
            goto done;
        }
        else if (bytes_read == 0)
        {
            msg(_("bore_async_execute_update: No bytes read"));
            goto done;
        }

        // TODO-pkack: Handle partial read lines and bytes_avail > 4093 correctly
        // format as string expression
        buffer[0] = '\'';
        buffer[bytes_read + 1] = '\'';
        buffer[bytes_read + 2] = '\0';

        // TODO-pkack: Is there a way to make cgetexpr/caddexpr handle output the same way as cgetfile/caddfile
        // quick and dirty replace of ' with " instead of escaping correctly
        char* c = buffer + 1;
        char* end = c + bytes_read;
        for (; c != end; ++c)
            if (*c == '\'')
                *c = '\"';

        // add output as error expressions
        char* title = (char*)alloc(100);
        vim_snprintf(title, 100, "borebuild");
        exarg_T eap;
        memset(&eap, 0, sizeof(eap));
        eap.cmdidx = (first && !errors) ? CMD_cgetexpr : CMD_caddexpr;
        eap.cmdlinep = &title;
        eap.arg = buffer;
        ex_cexpr(&eap);
        vim_free(title);

        ++errors;
        if (bytes_read == bytes_avail)
            break;
    }

    if (first && errors)
    {
        exarg_T eap;
        memset(&eap, 0, sizeof(eap));
        eap.cmdidx = CMD_cwindow;
        ex_copen(&eap);
    }
    update_screen(UPD_VALID);

done:
    if (completed)
    {
        CloseHandle(g_bore_async_execute_context.wait_thread);
        CloseHandle(g_bore_async_execute_context.spawned_process.hThread);
        CloseHandle(g_bore_async_execute_context.spawned_process.hProcess);
        CloseHandle(g_bore_async_execute_context.result_handle);
        g_bore_async_execute_context.wait_thread = INVALID_HANDLE_VALUE;
        g_bore_async_execute_context.spawned_process.hThread = INVALID_HANDLE_VALUE;
        g_bore_async_execute_context.spawned_process.hProcess = INVALID_HANDLE_VALUE;
        g_bore_async_execute_context.result_handle = INVALID_HANDLE_VALUE;
        g_bore_async_execute_context.completed = 1;
        bore_print_build();
    }

    need_wait_return = saved_need_wait_return;
    msg_nowait = saved_msg_nowait;

    BORE_VIMPROFILE_STOP("bore_async_update");
}

static DWORD WINAPI bore_async_execute_wait_thread(LPVOID param)
{
    extern HWND s_hwnd;
    DWORD result;
    DWORD bytes_avail;
    DWORD first = 1;
    DWORD completed = 0;

    do
    {
        result = WaitForSingleObject(g_bore_async_execute_context.spawned_process.hProcess, 1000);
        ++g_bore_async_execute_context.duration;

        if (result == WAIT_TIMEOUT)
        {
            BOOL peek_success = PeekNamedPipe(
                g_bore_async_execute_context.result_handle,
                NULL,
                0,
                0,
                &bytes_avail,
                NULL);

            if (!peek_success || 0 == bytes_avail)
                continue;
        }
        else
        {
            GetExitCodeProcess(
                g_bore_async_execute_context.spawned_process.hProcess,
                &g_bore_async_execute_context.exit_code);
            completed = 1;
        }

        assert(sizeof(WPARAM) == sizeof(&bore_async_execute_update));
        WPARAM wparam = (WPARAM)&bore_async_execute_update;
        LPARAM lparam = (result & 0x3FFFFFFF) | (first << 31) | (completed << 30);
        PostMessage(s_hwnd, WM_USER + 1234, wparam, lparam);

        first = 0;
    } while (completed == 0);

    return 0;
}

static void bore_async_execute(char* title, const char* cmdline)
{
    if (g_bore_async_execute_context.wait_thread != INVALID_HANDLE_VALUE)
    {
        emsg(_("bore_async_execute: Busy. Cannot launch another process."));
        return;
    }
    g_bore_async_execute_context.completed = 0;
    g_bore_async_execute_context.duration = 0;
    g_bore_async_execute_context.exit_code = 0;
    vim_strncpy(
        g_bore_async_execute_context.title,
        title,
        sizeof(g_bore_async_execute_context.title));

    autowrite_all();

    exarg_T eap;
    memset(&eap, 0, sizeof(eap));
    eap.cmdidx = CMD_cwindow;
    ex_cclose(&eap);

    HANDLE output_handle;
    HANDLE error_handle;

    SECURITY_ATTRIBUTES sa_attr = {0};
    sa_attr.nLength = sizeof(sa_attr);
    sa_attr.bInheritHandle = TRUE;
    sa_attr.lpSecurityDescriptor = NULL;

    BOOL result = CreatePipe(
        &g_bore_async_execute_context.result_handle,
        &output_handle,
        &sa_attr,
        0);

    if (!result)
    {
        emsg(_("bore_async_execute: Failed to create pipe"));
        goto fail;
    }

    result = SetHandleInformation(
        g_bore_async_execute_context.result_handle,
        HANDLE_FLAG_INHERIT,
        0);

    if (!result)
    {
        emsg(_("bore_async_execute: Failed to remove inheritable flag for read handle"));
        goto fail;
    }

    result = DuplicateHandle(
        GetCurrentProcess(),
        output_handle,
        GetCurrentProcess(),
        &error_handle,
        0,
        TRUE,
        DUPLICATE_SAME_ACCESS);

    if (!result)
    {
        emsg(_("bore_async_execute: Failed to duplicate stdout write handle for stderr"));
        goto fail;
    }

    STARTUPINFO startup_info = {0};
    char cmd[1024];

    startup_info.cb = sizeof(startup_info);
    startup_info.dwFlags = STARTF_USESTDHANDLES;
    startup_info.hStdInput = GetStdHandle(STD_INPUT_HANDLE);
    startup_info.hStdOutput = output_handle;
    startup_info.hStdError = error_handle;

    if (-1 == _snprintf_s(cmd, sizeof(cmd), sizeof(cmd), "cmd.exe /c \"%s\"", cmdline))
    {
        emsg(_("bore_async_execute: Command line is too long"));
        goto fail;
    }

    memset(
            &g_bore_async_execute_context.spawned_process,
            0,
            sizeof(g_bore_async_execute_context.spawned_process));

    BOOL process_created = CreateProcess(
            NULL,
            cmd,
            NULL,
            &sa_attr,
            TRUE,
            CREATE_NO_WINDOW,
            NULL,
            NULL,
            &startup_info,
            &g_bore_async_execute_context.spawned_process);

    if (!process_created)
    {
        emsg(_("bore_async_execute: Failed to spawn process"));
        goto fail;
    }

    CloseHandle(output_handle);
    CloseHandle(error_handle);

    DWORD thread_id = 0;

    g_bore_async_execute_context.wait_thread = CreateThread(
            NULL,
            4096,
            bore_async_execute_wait_thread,
            &g_bore_async_execute_context,
            0,
            &thread_id);

    if (g_bore_async_execute_context.wait_thread == INVALID_HANDLE_VALUE)
    {
        emsg(_("bore_async_execute: Failed to spawn wait thread"));
        goto fail;
    }

    msg(g_bore_async_execute_context.title);
    return;

fail:
    CloseHandle(output_handle);
    CloseHandle(error_handle);
    CloseHandle(g_bore_async_execute_context.wait_thread);
    CloseHandle(g_bore_async_execute_context.spawned_process.hThread);
    CloseHandle(g_bore_async_execute_context.spawned_process.hProcess);
    CloseHandle(g_bore_async_execute_context.result_handle);
    g_bore_async_execute_context.wait_thread = INVALID_HANDLE_VALUE;
    g_bore_async_execute_context.spawned_process.hThread = INVALID_HANDLE_VALUE;
    g_bore_async_execute_context.spawned_process.hProcess = INVALID_HANDLE_VALUE;
    g_bore_async_execute_context.result_handle = INVALID_HANDLE_VALUE;
    g_bore_async_execute_context.completed = -1;
    g_bore_async_execute_context.duration = -1;
    g_bore_async_execute_context.exit_code = -1;
}


#endif

/* Only do the following when the feature is enabled.  Needed for "make
 * depend". */
#if defined(FEAT_BORE) || defined(PROTO)

void ex_boresln(exarg_T *eap)
{
    if (*eap->arg == NUL)
    {
        bore_print_sln(0);
    }
    else
    {
        DWORD start = GetTickCount();
        DWORD elapsed;
        bore_load_sln((char*)eap->arg);
        elapsed = GetTickCount() - start;
        bore_print_sln(elapsed);
    }
}

bore_file_t* bore_find_file(char* fn)
{
    char path[BORE_MAX_PATH];

    if (FAIL == bore_canonicalize(fn, path, 0))
        return NULL;

    bore_file_t* file = (bore_file_t*)bsearch_s(
        path,
        g_bore->file_alloc.base,
        g_bore->file_count,
        sizeof(bore_file_t),
        bore_find_filename,
        g_bore);

    return file;
}

void borefind_parse_options(bore_t* b, char* arg, bore_search_t* search)
{
    // Usage: [option(s)] what
    //   -i ignore case
    //   -p project only (based on current buffer)
    //   -e ext1,ext2,...,ext9
    //      filters the search based on a list of file extensions
    //   -h exludes huge files
    //   -
    //   -u
    //      an empty (or any unknown) option will force the remainder to be treated as the search string

    bore_file_t* file = NULL;
    char* opt = NULL;
    char* what = arg;
    char* what_ext = NULL;
    int options = BS_NONE;
    u32 file_index = ~0u;

    for (; *arg; ++arg)
    {
        if (NUL == opt)
        {
            if ('-' == *arg)
            {
                // found new option marker
                ++arg;
                if (*arg == 'e' && arg[1] == ' ')
                {
                    // found extension option argument start, loop until next space
                    opt = arg;
                    what_ext = &opt[2];
                    arg += 2;
                }
                else if (*arg == 'h' && arg[1] == ' ')
                {
                    options |= BS_HUGEFILES;
                    ++arg;
                }
                else if (*arg == 'i' && arg[1] == ' ')
                {
                    options |= BS_IGNORECASE;
                    ++arg;
                }
                else if (*arg == 'p' && arg[1] == ' ')
                {
                    options |= BS_PROJECT;
                    ++arg;
                }
                else
                {
                    // empty or unknown option, treat the rest as the search string
                    what = arg + 1;
                    break;
                }
            }
            else
            {
                // no option found, treat the rest as the search string
                what = arg;
                break;
            }
        }
        else if (' ' == *arg)
        {
            // end current option argument string and search for next option
            opt = NUL;
            *arg = '\0';
        }
    }

    // convert search string to lower case
    if (options & BS_IGNORECASE)
    {
        // _strlwr_s(what, search.what_len);
        char* c = what;
        for (; *c; ++c)
            *c = TOLOWER_LOC(*c);
    }

    // lookup current buffer, use for scoring and project filtering
    if (NULL != curbuf->b_fname && '\0' != curbuf->b_fname)
    {
        file = bore_find_file(curbuf->b_fname);
        if (NULL != file)
        {
            file_index = file - (bore_file_t*)b->file_alloc.base;
            options |= BS_SORTRESULT; // add sort result option
        }
        else
        {
            options &= ~BS_PROJECT; // clear project filter option
        }
    }

    search->what = what;
    search->what_len = (int) strlen(what);
    search->options = options;
    search->file_index = file_index;
    search->match_count = BORE_MAX_MATCH_TOTAL;
    search->ext_count = 0;

    // parse comma separated list of file extensions into list of hashes
    if (what_ext)
    {
        int len = 0;
        char* ext = what_ext;
        char* c;
        for (c = ext; search->ext_count < BORE_MAX_SEARCH_EXTENSIONS; ++c)
        {
            if (*c == ',' || *c == '\0')
            {
                search->ext[search->ext_count++] = bore_string_hash_n(ext, len);
                ext = c + 1;
                len = 0;
            }
            else
            {
                ++len;
            }

            if (*c == '\0')
                break;
        }
    }

}

void ex_borefind(exarg_T *eap)
{
    if (!g_bore)
    {
        emsg(_("Load a solution first with boresln"));
    }
    else
    {
        DWORD start = GetTickCount();
        DWORD elapsed;
        bore_search_t search;
        size_t arg_size = strlen(eap->arg) + 1;
        char* arg = lalloc(arg_size, TRUE);
        memcpy(arg, eap->arg, arg_size);

        borefind_parse_options(g_bore, arg, &search);
        int found = bore_find(g_bore, (char*)eap->arg, &search);
        elapsed = GetTickCount() - start;
        vim_snprintf(IObuff, IOSIZE, "%d%s matching lines; borefind %s; %u ms",
            found > 0 ? found : -found,
            found < 0 ? " (truncated)" : "",
            (char*)eap->arg, elapsed);
        if (found)
            msg(IObuff);
        else
            emsg(IObuff);

        vim_free(arg);
    }
}

void ex_boreopen(exarg_T *eap)
{
    if (!g_bore)
        emsg(_("Load a solution first with boresln"));
    else
    {
        const char* mappings[] =
        {
            "q <C-w>q<CR>",
            "<CR> :ZZBoreopenselection<CR>",
            "<2-LeftMouse> :ZZBoreopenselection<CR>",
            0};
        bore_show_borebuf(g_bore, bore_str(g_bore, g_bore->sln_filelist), g_bore->ini.borebuf_height, mappings);
    }
}

void bore_open_file_buffer(char_u* fn)
{
    buf_T* buf;

    buf = buflist_findname_exp(fn);
    if (NULL == buf)
        goto edit;

    if (NULL != buf->b_ml.ml_mfp && NULL != buf_jump_open_win(buf))
        goto verify;

    set_curbuf(buf, DOBUF_GOTO);

verify:
    if (buf != curbuf)
edit:
    {
        exarg_T ea;
        memset(&ea, 0, sizeof(ea));
        ea.arg = fn;
        ea.cmdidx = CMD_edit;
        do_exedit(&ea, NULL);
    }
}

char_u* bore_statusline(int flags)
{
    bore_sln_config_t* config;
    bore_proj_t* proj;
    bore_file_t* file;
    BOOL has_data = FALSE;

    if (!g_bore || !flags)
        return NULL;

    STRCPY(IObuff, "[");
    // project
    if (NULL != curbuf->b_fname && '\0' != curbuf->b_fname[0])
    {
        if (0x04 & flags)
        {
            file = bore_find_file(curbuf->b_fname);
            if (file != NULL)
            {
                proj = (bore_proj_t*)g_bore->proj_alloc.base + file->proj_index;
                STRCAT(IObuff, bore_str(g_bore, proj->project_sln_name));
                has_data = TRUE;
            }
        }
    }
    if (g_bore->sln_config >= 0)
    {
        config = (bore_sln_config_t*)g_bore->config_alloc.base + g_bore->sln_config;
        // configuration
        if (0x02 & flags)
        {
            if (has_data)
                STRCAT(IObuff, "|");
            STRCAT(IObuff, bore_str(g_bore, config->config));
            has_data = TRUE;
        }
        // platform
        if (0x01 & flags)
        {
            if (has_data)
                STRCAT(IObuff, "|");
            STRCAT(IObuff, bore_str(g_bore, config->platform));
            has_data = TRUE;
        }
    }
    if (!has_data)
        return NULL;
    STRCAT(IObuff, "]");
    return IObuff;
}

static bore_print_proj(bore_t* b, int proj_index)
{
    const bore_proj_t* projects = (bore_proj_t*)b->proj_alloc.base;
    int i;

    if (proj_index < 0)
    {
        for (i = 0; i < b->proj_count; ++i)
        {
            vim_snprintf(IObuff, IOSIZE, "%s|%s",
                bore_str(b, projects[i].project_sln_name),
                bore_str(b, projects[i].project_file_path));
            msg(IObuff);
        }
    }
    else
    {
        vim_snprintf(IObuff, IOSIZE, "%s|%s",
            bore_str(b, projects[proj_index].project_sln_name),
            bore_str(b, projects[proj_index].project_file_path));
        msg(IObuff);
    }
}

void ex_boreproj(exarg_T *eap)
{
    if (!g_bore)
    {
        emsg(_("boreproj: Load a solution first with boresln"));
    }
    else
    {
        int print_all = eap->forceit;
        int proj_index = -1;
        char_u* arg = NULL;
        bore_file_t* file;

        if (!print_all)
        {
            // Specififed project name argument
            if (NULL != eap->arg && '\0' != eap->arg[0])
            {
                arg = eap->arg;
                proj_index = bore_match_proj(g_bore, arg);
            }
            // Current buffer
            else if (NULL != curbuf->b_fname && '\0' != curbuf->b_fname)
            {
                arg = curbuf->b_fname;
                file = bore_find_file(arg);
                if (NULL != file)
                    proj_index = file->proj_index;
            }
            if (proj_index >= 0)
                bore_set_proj(g_bore, proj_index);
            else
                semsg(_("boreproj: Failed to lookup project: %s"), arg);
        }
        bore_print_proj(g_bore, proj_index);
    }
}

static bore_print_sln_config(bore_t* b, int print_all)
{
    const bore_sln_config_t* sln_configs = (bore_sln_config_t*)g_bore->config_alloc.base;

    if (print_all)
    {
        int i;
        for (i = 0; i < g_bore->config_count; ++i)
        {
            BOOL is_active = (g_bore->sln_config == i);
            vim_snprintf(IObuff, IOSIZE, "%s %s|%s",
                is_active ? "*" : " ",
                bore_str(g_bore, sln_configs[i].config),
                bore_str(g_bore, sln_configs[i].platform));
            if (is_active)
                msg_attr(IObuff, HL_ATTR(HLF_D));
            else
                msg(IObuff);
        }
    }
    else
    {
        vim_snprintf(IObuff, IOSIZE, "%s|%s",
            bore_str(g_bore, sln_configs[g_bore->sln_config].config),
            bore_str(g_bore, sln_configs[g_bore->sln_config].platform));
        msg(IObuff);
    }
}

void ex_boreconfig(exarg_T *eap)
{
    if (!g_bore)
    {
        emsg(_("boreconfig: Load a solution first with boresln"));
    }
    else if (bore_is_sln_directory(g_bore))
    {
        emsg(_("boreconfig: Directories are not supported, load an actual solution first with boresln"));
    }
    else
    {
        int print_all = eap->forceit;
        if (NULL != eap->arg && '\0' != eap->arg[0])
        {
            int sln_config = bore_match_sln_config(g_bore, eap->arg);
            if (sln_config >= 0)
            {
                bore_set_sln_config(g_bore, sln_config);
            }
            else
            {
                semsg(_("boreconfig: No matching entry for: %s"), eap->arg);
                print_all = 1;
            }
        }
        bore_print_sln_config(g_bore, print_all);
    }
}

void ex_boretoggle(exarg_T *eap)
{
    if (!g_bore)
        emsg(_("Load a solution first with boresln"));
    else
    {
        char path[BORE_MAX_PATH];
        const char* ext;
        const char* basename;
        size_t path_len;
        u32 basename_hash;
        u32 ext_hash;
        const bore_toggle_entry_t* e_begin = (const bore_toggle_entry_t*)g_bore->toggle_index_alloc.base;
        const bore_toggle_entry_t* e = e_begin;
        const bore_toggle_entry_t* e_end = e + g_bore->toggle_entry_count;
        const bore_toggle_entry_t* e_buf;
        const bore_toggle_entry_t* e_best;
        int e_best_score;

        if (FAIL == bore_canonicalize(curbuf->b_fname, path, 0))
            return;

        path_len = strlen(path);

        ext = vim_strrchr(path, '.');
        ext = ext ? ext + 1 : path + path_len;
        ext_hash = bore_string_hash(ext);

        basename = vim_strrchr(path, '\\');
        basename = basename ? basename + 1 : path;
        basename_hash = bore_string_hash_n(basename, ext - basename);

        // find first entry with identical basename using binary search
        while (e_begin < e_end)
        {
            e = e_begin + ((e_end - e_begin) / 2);
            if (e->basename_hash < basename_hash)
                e_begin = e + 1;
            else
                e_end = e;
        }

        if (e_begin->basename_hash != basename_hash || e_begin != e_end)
            return;

        // set first match and restore e_end
        e = e_begin;
        e_end = (const bore_toggle_entry_t*)g_bore->toggle_index_alloc.base + g_bore->toggle_entry_count;

        // Find the entry of this buffer's file
        for (; e != e_end && e->basename_hash == basename_hash; ++e)
            if (0 == STRICMP(bore_str(g_bore, e->file), path))
                break;

        if (e == e_end || e->basename_hash != basename_hash)
            return;

        // Find what ext to toggle to
        e_buf = e;
        for(;;)
        {
            ++e;
            if (e == e_end || e->basename_hash != basename_hash)
                e = e_begin;
            if (e == e_buf)
                return; // no match
            if (e->extension_index != e_buf->extension_index)
            {
                break;
            }
        }

        // Find the best matching ext
        e_best = e;
        e_best_score = bore_str_match_score(path, bore_str(g_bore, e->file));
        ++e;
        for(; e != e_end && e_best->extension_index == e->extension_index; ++e)
        {
            int score = bore_str_match_score(path, bore_str(g_bore, e->file));
            if (score > e_best_score)
            {
                e_best_score = score;
                e_best = e;
            }
        }

        {
            char *fn = bore_rel_path(g_bore, e_best->file);
            bore_open_file_buffer(fn);
        }
    }
}

void ex_borebuild(exarg_T *eap)
{
    if (!g_bore)
    {
        emsg(_("borebuild: Load a solution first with boresln"));
    }
    else if (bore_is_sln_directory(g_bore))
    {
        emsg(_("borebuild: Directories are not supported, load an actual solution first with boresln"));
    }
    else if (-1 == g_bore->sln_config)
    {
        emsg(_("borebuild: Set a solution configuration first with boreconfig"));
    }
    else if (!mch_can_exe("msbuild", NULL, TRUE))
    {
        emsg(_("borebuild: Failed to find msbuild executable in path"));
    }
    else if (eap->cmdidx == CMD_borebuildinfo)
    {
        bore_print_build();
    }
    else
    {
        char cmd[1024];
        char title[1024];
        bore_file_t* file = NULL;
        int proj_index = -1;
        bore_sln_config_t* sln_config = (bore_sln_config_t*)g_bore->config_alloc.base + g_bore->sln_config;
        bore_proj_t* project = (bore_proj_t*)g_bore->proj_alloc.base;
        const char* configuration = bore_str(g_bore, sln_config->config);
        const char* platform = bore_str(g_bore, sln_config->platform);
        char_u* arg = "";

        if (eap->cmdidx == CMD_borebuildfile)
        {
            // Specififed source file argument
            if (NULL != eap->arg && '\0' != eap->arg[0])
            {
                arg = eap->arg;
                file = bore_find_file(arg);
            }
            // Current buffer
            else if (NULL != curbuf->b_fname && '\0' != curbuf->b_fname)
            {
                arg = curbuf->b_fname;
                file = bore_find_file(arg);
            }
            if (NULL == file)
            {
                semsg(_("borebuildfile: Failed to lookup file: %s"), arg);
                return;
            }
            proj_index = file->proj_index;
        }
        else if (eap->cmdidx == CMD_borebuildproj)
        {
            // Specififed project name argument
            if (NULL != eap->arg && '\0' != eap->arg[0])
            {
                arg = eap->arg;
                proj_index = bore_match_proj(g_bore, arg);
            }
            // Current buffer
            else if (NULL != curbuf->b_fname && '\0' != curbuf->b_fname)
            {
                arg = curbuf->b_fname;
                file = bore_find_file(arg);
                if (NULL != file)
                    proj_index = file->proj_index;
            }
            if (proj_index < 0)
            {
                semsg(_("borebuildproj: Failed to lookup project: %s"), arg);
                return;
            }
        }

        // TODO-pkack: Can target Build/Rebuild/Clean be specified for a specific project?
        // The following MSDN example does not work
        // https://msdn.microsoft.com/en-us/library/ms171486.aspx
        // msbuild SlnFolders.sln /t:NotInSlnfolder:Rebuild;NewFolder\InSolutionFolder:Clean
        // Note: '.' in project names must be replaced with '_' for msbuild targets

        project += proj_index;
        if (eap->cmdidx == CMD_borebuildfile)
        {
            char* proj_file = bore_rel_path(g_bore, project->project_file_path);
            char* src_file = bore_rel_path(g_bore, file->file);

            vim_snprintf(cmd, 1024,
                "msbuild %s /t:ClCompile /p:SelectedFiles=\"%s\" /p:Configuration=%s /p:Platform=%s " \
                "/v:q /nologo /fl /flp:ShowTimestamp;verbosity=normal",
                proj_file, src_file, configuration, platform);
        }
        else
        {
            char* sln_file = bore_rel_path(g_bore, g_bore->sln_path);
            char* projectRefs = (eap->cmdidx == CMD_borebuildprojonly) ? "false" : "true";
            char* target;
            if (eap->cmdidx == CMD_borebuildproj)
                target = bore_str(g_bore, project->project_sln_name);
            else
                target = eap->forceit ? "Rebuild" : "Build";

            vim_snprintf(cmd, 1024,
                "msbuild %s /t:%s /p:Configuration=%s /p:Platform=%s " \
                "/p:BuildProjectReferences=%s " \
                "/v:q /nologo /fl /flp:ShowTimestamp;verbosity=normal " \
                "/m:%d /p:MultiProcessorCompilation=true;CL_MPCount=%d",
                sln_file, target, configuration, platform, projectRefs,
                g_bore->ini.cpu_cores, g_bore->ini.cpu_cores);
        }

        char* c = strstr(cmd, " /v:");
        if (c)
            vim_strncpy(title, cmd, c - cmd);
        else
            title[0] = '\0';

        bore_async_execute(title, cmd);
    }
}


// Internal functions

// Open the file on the current row in the current buffer
void ex_Boreopenselection(exarg_T *eap)
{
    char_u* fn;
    if (!g_bore)
        return;
    fn = vim_strsave(ml_get_curline());
    if (!fn)
        return;

    win_close(curwin, TRUE);

    bore_open_file_buffer(fn);
    vim_free(fn);
}

#endif
