/* vi:set ts=8 sts=4 sw=4 et: */
#pragma once
#include <stdio.h>

#define BORE_MAX_SMALL_PATH 256
#define BORE_MAX_PATH 1024
#define BORE_SEARCH_JOBS 8
#define BORE_SEARCH_RESULTS 8
#define BORE_CACHELINE 64 
#define BORE_MAX_MATCH_PER_FILE 1000
#define BORE_MAX_MATCH_TOTAL 100000
#define BORE_MAX_QUICKFIX_ITEMS 1000
#define BORE_MAX_SEARCH_EXTENSIONS 9
#define BORE_HUGEFILE_SIZE 16 * 1024 * 1024

typedef unsigned char u8;
typedef unsigned int u32;

typedef struct bore_alloc_t
{
    u8* base; // cacheline aligned
    u8* end;
    u8* cursor;
    size_t offset; // for alignment
} bore_alloc_t;

typedef struct bore_sln_config_t
{
    u32 config;
    u32 platform;
} bore_sln_config_t;

typedef struct bore_proj_t
{
    u32 project_sln_name;
    u32 project_sln_guid;
    u32 project_sln_path;
    u32 project_file_path;
} bore_proj_t;

typedef enum
{
    BS_NONE = 0,
    BS_IGNORECASE = 1,
    BS_HUGEFILES = 2,
    BS_PROJECT = 4,
    BS_SORTRESULT = 8,
} bore_search_option_t;

typedef struct bore_search_t
{
    const char* what;
    int what_len;
    int options;
    int match_count;
    u32 file_index;
    int ext_count;
    u32 ext[BORE_MAX_SEARCH_EXTENSIONS]; // (64-28)/4
} bore_search_t;

typedef struct bore_match_t
{
    u32 file_index;
    u32 row;
    u32 column;
    char line[1024 - 12];
} bore_match_t;

typedef struct bore_ini_t
{
    int borebuf_height; // Default height of borebuf window
    int cpu_cores; // Max number of cpu cores to be used
} bore_ini_t;

typedef struct __declspec(align(BORE_CACHELINE)) bore_search_job_t
{
    bore_alloc_t filedata;
    int fileindex;
} bore_search_job_t;

typedef struct __declspec(align(BORE_CACHELINE)) bore_search_result_t
{ 
    int hits;
    bore_match_t result[BORE_MAX_MATCH_PER_FILE];  
} bore_search_result_t;

typedef struct bore_file_t
{
    u32 file;
    u32 proj_index;
} bore_file_t;

typedef struct bore_toggle_entry_t
{
    u32 basename_hash;
    int extension_index;
    u32 file;
    u32 dir_hash;
    u32 parent_dir_hash;
} bore_toggle_entry_t;

typedef struct bore_t
{
    u32 sln_path; // abs path of solution
    u32 sln_dir;  // abs dir of solution
    size_t sln_dir_len;  // len of solution dir
    u32 sln_name; // name of solution
    int sln_config; // current solution configuration to build
    u32 sln_filelist; // name of filelist file for the solution

    // array of bore_sln_config_t (all configurations in the solution)
    int config_count;
    bore_alloc_t config_alloc; 

    // array of bore_proj_t (all projects in the solution)
    int proj_count;
    bore_alloc_t proj_alloc; 

    // array of files in the solution
    int file_count;
    bore_alloc_t file_alloc;      // array of bore_file_t sorted by file name
    bore_alloc_t file_ext_alloc;  // array of extension hashes

    // array of bore_toggle_entry_t;
    int toggle_entry_count;
    bore_alloc_t toggle_index_alloc;

    bore_alloc_t data_alloc; // bulk data (filenames, strings, etc)

    // context used for searching
    bore_search_job_t search[BORE_SEARCH_JOBS];
    bore_search_result_t search_result[BORE_SEARCH_RESULTS];

    bore_ini_t ini;
} bore_t;

void bore_prealloc(bore_alloc_t* p, size_t size);
void* bore_alloc(bore_alloc_t* p, size_t size);
void bore_alloc_trim(bore_alloc_t* p, size_t size);
void bore_alloc_free(bore_alloc_t* p);

char* bore_str(bore_t* b, u32 offset);

int bore_dofind(bore_t* b, int threadCount, int* truncated, bore_match_t* match, int match_size, bore_search_t* search);
