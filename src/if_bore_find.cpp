/* vi:set ts=8 sts=4 sw=4 et: */

#ifdef FEAT_BORE

extern "C" {
#include "if_bore.h"
#include "vim.h"
}
#include <windows.h>
#include <winnt.h>

//#define BORE_CVPROFILE

#ifdef BORE_CVPROFILE
#pragma comment(lib, "Advapi32.lib")
#include "C:\Program Files\Microsoft Visual Studio\18\Professional\Common7\IDE\Extensions\hzwiclye.s1a\SDK\Native\Inc\cvmarkers.h"
// Add {551695CB-80AC-4C14-9858-ECB94348D43E} in ConcurrencyVisualizer / Advanced Settings / Markers
PCV_PROVIDER g_provider;
PCV_MARKERSERIES g_series1;
int g_cv_initialized;

#define BORE_CVBEGINSPAN(str) CvEnterSpanA(g_series1, &span, str)
#define BORE_CVENDSPAN() do { CvLeaveSpan(span); span = 0; } while(0)
#define BORE_CVINITSPAN PCV_SPAN span = 0
#define BORE_CVDEINITSPAN do { if (span) CvLeaveSpan(span); } while(0)
#else
#define BORE_CVBEGINSPAN(str)
#define BORE_CVENDSPAN()
#define BORE_CVINITSPAN
#define BORE_CVDEINITSPAN
#endif

#define BTSOUTPUT(j) if (p != out_end) *p++ = j; else goto done;
struct exact_string_search_t
{
    virtual int search(const char* text, int text_len, const char* what, int what_len, int* out, const int* out_end) const = 0;
};

struct quick_search_t : public exact_string_search_t
{
    quick_search_t(const char *what, int what_len)
    {
        /* Preprocessing */
        pre_qs_bc((const unsigned char*)what, what_len, m_qs_bc);
    }

    virtual int search (const char* text, int text_len, const char* what, int what_len, int* out, const int* out_end) const
    {
        int j;
        const unsigned char* x = (const unsigned char*)what;
        int m = what_len;
        const unsigned char* y = (const unsigned char*)text;
        int n = text_len;
        int* p = out;

        j = 0;
        while (j <= n - m)
        {
            if (memcmp(x, y + j, m) == 0)
                BTSOUTPUT(j);
            j += m_qs_bc[y[j + m]];               /* shift */
        }

done:
        return p - out;
    }

private:
    enum { ASIZE = 256 };
    int m_qs_bc[ASIZE];
    void pre_qs_bc(const unsigned char *x, int m, int qs_bc[])
    {
        int i;

        for (i = 0; i < ASIZE; ++i)
            qs_bc[i] = m + 1;
        for (i = 0; i < m; ++i)
            qs_bc[x[i]] = m - i;
    }
};

struct old_search_t : public exact_string_search_t
{
    virtual int search(const char* text, int text_len, const char* what, int what_len, int* out, const int* out_end) const
    {
        // http://www-igm.univ-mlv.fr/~lecroq/string/index.html
        const char* y = text;
        int n = text_len;
        const char* x = what;
        int m = what_len;
        int* p = out;
        int j, k, ell;

        /* Preprocessing */
        if (x[0] == x[1])
        {
            k = 2;
            ell = 1;
        }
        else
        {
            k = 1;
            ell = 2;
        }

        /* Searching */
        j = 0;
        while (j <= n - m)
        {
            if (x[1] != y[j + 1])
                j += k;
            else
            {
                if (memcmp(x + 2, y + j + 2, m - 2) == 0 && x[0] == y[j])
                {
                    BTSOUTPUT(j);
                }
                j += ell;
            }
        }
done:
        return p - out;
    }
};

#undef BTSOUTPUT

/*
 * Case-insensitive strstr: find needle in haystack ignoring case.
 */
static const char* bore_stristr(const char* haystack, const char* needle, int needle_len)
{
    if (needle_len == 0) return haystack;
    for (; *haystack; ++haystack)
    {
        if (TOLOWER_LOC(*haystack) == TOLOWER_LOC(*needle))
        {
            const char* h = haystack + 1;
            const char* n = needle + 1;
            const char* nend = needle + needle_len;
            while (n < nend && *h && TOLOWER_LOC(*h) == TOLOWER_LOC(*n))
            {
                ++h;
                ++n;
            }
            if (n == nend)
                return haystack;
        }
    }
    return NULL;
}

/*
 * Check if a line matches a wildcard pattern (fragments separated by *).
 * Returns 1 if all fragments appear in order in the line.
 * The pattern string is the original search input (e.g. "StrA*StrB").
 * If case_insensitive is set, uses case-insensitive matching.
 */
static int bore_wildcard_match_line(const char* line, const char* pattern, int case_insensitive)
{
    const char* pos = line;
    const char* p = pattern;

    while (*p)
    {
        /* Find next fragment (between * characters) */
        const char* frag_start = p;
        while (*p && *p != '*')
            ++p;
        int frag_len = (int)(p - frag_start);

        /* Skip empty fragments (leading/trailing/consecutive *) */
        if (frag_len > 0)
        {
            const char* found;
            if (case_insensitive)
                found = bore_stristr(pos, frag_start, frag_len);
            else
            {
                /* Use a bounded search */
                for (found = pos; *found; ++found)
                {
                    if (0 == memcmp(found, frag_start, frag_len))
                        break;
                }
                if (!*found) found = NULL;
            }
            if (!found)
                return 0;
            pos = found + frag_len;
        }

        /* Skip the * */
        if (*p == '*')
            ++p;
    }
    return 1;
}

static void bore_resolve_match_location(int file_index, const char* p, u32 filesize,
        bore_match_t* match, bore_match_t* match_end, int* offset, int offset_count)
{
    const int* offset_end = offset + offset_count;
    const char* pbegin = p;
    const char* linebegin = p;
    const char* fileend = p + filesize;
    int line = 1;

    while(offset < offset_end && match < match_end)
    {
        const char* pend = pbegin + *offset;
        while (p < pend)
        {
            if (*p++ == '\n')
            {
                ++line;
                linebegin = p;
            }
        }
        const char* lineend = pend;
        while (lineend < fileend && *lineend != '\r' && *lineend != '\n')
            ++lineend;
        size_t linelen = lineend - linebegin;
        if (linelen > sizeof(match->line) - 1)
            linelen = sizeof(match->line) - 1;
        match->file_index = file_index;
        match->row = line;
        match->column = p - linebegin;
        memcpy(match->line, linebegin, linelen);
        match->line[linelen] = 0;
        ++match;
        ++offset;
    }
}

struct search_context_t
{
    bore_t* b;
    LONG* remaining_file_count;
    bore_alloc_t filedata;
    bore_alloc_t filedata_lowercase;
    const exact_string_search_t* string_search;
    const char* wildcard_pattern;  /* full pattern with *, or NULL if no wildcards */
    const char* search_str;       /* the string to Quick Search (longest fragment or full) */
    int search_str_len;
    bore_search_t* search;
    bore_match_t* match;
    LONG match_size;
    LONG* match_count;
    int was_truncated;
};

static void search_one_file(struct search_context_t* search_context, const char* filename, int file_index)
{
    HANDLE file_handle = INVALID_HANDLE_VALUE;
    bore_search_result_t search_result = {0};
    BORE_CVINITSPAN;

    char* start = NULL;
    int size = 0;

    {
        BORE_CVBEGINSPAN("opn"); // CvEnterSpanA(g_series1, &span, "op %s", filename);
        WCHAR fn[BORE_MAX_PATH];
        int result = MultiByteToWideChar(CP_UTF8, 0, filename, -1, fn, BORE_MAX_PATH);
        if (result == 0)
        {
            goto skip;
        }

        file_handle = CreateFileW(fn, GENERIC_READ, FILE_SHARE_READ, 0, OPEN_EXISTING, FILE_FLAG_SEQUENTIAL_SCAN, 0);
        if (file_handle == INVALID_HANDLE_VALUE)
        {
            goto skip;
        }
        BORE_CVENDSPAN();
    }

    {
        BORE_CVBEGINSPAN("rd"); // CvEnterSpanA(g_series1, &span, "rd %s", filename);


        DWORD filesize = GetFileSize(file_handle, 0);
        if (filesize == INVALID_FILE_SIZE)
            goto skip;

        if (!(search_context->search->options & BS_HUGEFILES) && (filesize > BORE_HUGEFILE_SIZE))
            goto skip;

        search_context->filedata.cursor = search_context->filedata.base;
        bore_alloc(&search_context->filedata, filesize);

        {
            char* p = (char*)search_context->filedata.base;
            DWORD remaining = filesize;
            while(remaining)
            {
                DWORD readbytes;
                if(!ReadFile(file_handle, p + filesize - remaining, remaining, &readbytes, 0))
                    goto skip;
                remaining -= readbytes;
            }
        }

        if (search_context->search->options & BS_IGNORECASE)
        {
            search_context->filedata_lowercase.cursor = search_context->filedata_lowercase.base;
            bore_alloc(&search_context->filedata_lowercase, filesize);

            char* dst = (char*)search_context->filedata_lowercase.base;
            u8* src = search_context->filedata.base;
            u8* end = src + filesize;
            for ( ; src < end; ++src, ++dst)
                *dst = TOLOWER_LOC(*src);

            start = (char*)search_context->filedata_lowercase.base;
            size = search_context->filedata_lowercase.cursor - search_context->filedata_lowercase.base;
        }
        else
        {
            start = (char*)search_context->filedata.base;
            size = search_context->filedata.cursor - search_context->filedata.base;
        }

        BORE_CVENDSPAN();
    }


    {
        BORE_CVBEGINSPAN("srch");

        // Search for the text (longest fragment if wildcard, full string otherwise)
        int match_offset[BORE_MAX_MATCH_PER_FILE];
        int match_in_file = search_context->string_search->search(
                start,
                size,
                search_context->search_str,
                search_context->search_str_len,
                &match_offset[0],
                &match_offset[BORE_MAX_MATCH_PER_FILE]);

        // Fill the result with the line's text, etc.
        bore_resolve_match_location(
                file_index,
                (char*)search_context->filedata.base,
                search_context->filedata.cursor - search_context->filedata.base,
                &search_result.result[0],
                &search_result.result[BORE_MAX_MATCH_PER_FILE],
                match_offset,
                match_in_file);

        // Post-filter for wildcard patterns
        if (search_context->wildcard_pattern && match_in_file > 0)
        {
            int was_capped = (match_in_file == BORE_MAX_MATCH_PER_FILE);
            int ci = search_context->search->options & BS_IGNORECASE;
            int write = 0;
            for (int r = 0; r < match_in_file; ++r)
            {
                if (bore_wildcard_match_line(search_result.result[r].line,
                        search_context->wildcard_pattern, ci))
                {
                    if (write != r)
                        search_result.result[write] = search_result.result[r];
                    ++write;
                }
            }
            match_in_file = write;
            /* If Quick Search hit the per-file cap, we may have missed
             * wildcard matches beyond the cap — signal truncation. */
            if (was_capped && write > 0)
                search_context->was_truncated = 1;
        }
        else if (match_in_file == BORE_MAX_MATCH_PER_FILE)
            search_context->was_truncated = 1;

        search_result.hits = match_in_file;

        BORE_CVENDSPAN();
    }

    {
        BORE_CVBEGINSPAN("wr");

        LONG start_index = InterlockedExchangeAdd(search_context->match_count, search_result.hits);

        int n = search_result.hits;
        if (start_index + n >= search_context->match_size)
        {
            search_context->was_truncated = 2; // Out of space. Signal quit.
            n = search_context->match_size - start_index;
        }

        if (n > 0)
            memcpy(&search_context->match[start_index], search_result.result, sizeof(bore_match_t) * n);

        BORE_CVENDSPAN();
    }

skip:
    if (file_handle != INVALID_HANDLE_VALUE)
    {
        CloseHandle(file_handle);
    }
    BORE_CVDEINITSPAN;
}

static DWORD WINAPI search_worker(struct search_context_t* search_context)
{
    bore_file_t* const files = (bore_file_t*)search_context->b->file_alloc.base;
    u32 proj_index =
        search_context->search->options & BS_PROJECT &&
        ~0u != search_context->search->file_index ?
        files[search_context->search->file_index].proj_index :
        ~0u;

    for (;;)
    {
        LONG file_index = InterlockedDecrement(search_context->remaining_file_count);
        if (file_index < 0)
            break;

        // skip files based on file extension filter
        if (search_context->search->ext_count > 0)
        {
            u32 file_ext = *((u32*)search_context->b->file_ext_alloc.base + file_index);
            int i;
            for (i = 0; i < search_context->search->ext_count; ++i)
            {
                if (file_ext == search_context->search->ext[i])
                    break;
            }

            if (i == search_context->search->ext_count)
                continue;
        }

        // skip files based on project filter
        if (proj_index != ~0u && proj_index != files[file_index].proj_index)
            continue;

        search_one_file(search_context, bore_str(search_context->b, files[file_index].file), file_index);

        if (search_context->was_truncated > 1)
            break;

    }
    return 0;
}

int bore_dofind(bore_t* b, int thread_count, int* truncated_, bore_match_t* match, int match_size, bore_search_t* search)
{
#ifdef BORE_CVPROFILE
    if (!g_cv_initialized)
    {
        GUID guid = { 0x551695cb, 0x80ac, 0x4c14, 0x98, 0x58, 0xec, 0xb9, 0x43, 0x48, 0xd4, 0x3e };
        CvInitProvider(&guid, &g_provider);
        CvCreateMarkerSeriesA(g_provider, "bore_find", &g_series1);
        g_cv_initialized = 1;
    }
#endif

    LONG file_count = b->file_count;
    *truncated_ = 0;

    /* Wildcard support: if pattern contains *, find the longest fragment
     * for Quick Search and store the full pattern for post-filtering. */
    const char* wildcard_pattern = NULL;
    const char* search_str = search->what;
    int search_len = search->what_len;

    if (strchr(search->what, '*'))
    {
        wildcard_pattern = search->what;
        const char* p = search->what;
        const char* best = p;
        int best_len = 0;
        while (*p)
        {
            const char* frag = p;
            while (*p && *p != '*')
                ++p;
            int frag_len = (int)(p - frag);
            if (frag_len > best_len)
            {
                best = frag;
                best_len = frag_len;
            }
            if (*p == '*')
                ++p;
        }
        search_str = best;
        search_len = best_len;
    }

    quick_search_t string_search(search_str, search_len);

    if (thread_count < 1)
    {
        thread_count = 1;
    }
    else if (thread_count > 32)
    {
        thread_count = 32;
    }

    HANDLE threads[32] = {0};
    search_context_t search_contexts[32] = {0};
    LONG match_count = 0;
    for (int i = 0; i < thread_count; ++i)
    {
        search_contexts[i].b = b;
        search_contexts[i].remaining_file_count = &file_count;
        bore_prealloc(&search_contexts[i].filedata, 100000);
        bore_prealloc(&search_contexts[i].filedata_lowercase, 100000);
        search_contexts[i].string_search = &string_search;
        search_contexts[i].search = search;
        search_contexts[i].match = match;
        search_contexts[i].match_size = match_size;
        search_contexts[i].match_count = &match_count;
        search_contexts[i].wildcard_pattern = wildcard_pattern;
        search_contexts[i].search_str = search_str;
        search_contexts[i].search_str_len = search_len;
    }

    for (int i = 0; i < thread_count - 1; ++i)
        threads[i] = CreateThread(0, 0, (LPTHREAD_START_ROUTINE)search_worker, &search_contexts[i], 0, 0);

    search_worker(&search_contexts[thread_count - 1]);

    WaitForMultipleObjects(thread_count - 1, threads, TRUE, INFINITE);

    for (int i = 0; i < thread_count; ++i)
    {
        if (search_contexts[i].was_truncated > *truncated_)
            *truncated_ = search_contexts[i].was_truncated;
    }

    if (*truncated_ > 1)
        match_count = match_size;

    for (int i = 0; i < thread_count; ++i)
    {
        bore_alloc_free(&search_contexts[i].filedata);
        bore_alloc_free(&search_contexts[i].filedata_lowercase);
    }

    return match_count;
}


#endif

