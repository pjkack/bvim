`README.md` for version 9.2 of BVIM: Bore Vi IMproved.

BVIM: gVim 9.2 with Visual Studio extensions
=======================================================

BVIM is a version of gVim which adds a few features which helps working on large Visual Studio projects. The goal is to make all common programming actions take less than 500 ms on a fast machine. It is supported on Windows 7 and above, it builds with Visual Studio 2017 using src/bvim.sln, and it is developed and maintained by Jonas Kjellström and Per-Jonny Käck.

boresln <.sln file | directory>
------------------------------------------------------
Open a solution and build a list of all files that are included in the projects. This must be the first thing done in order to use the other commands. Alternatively a directory can be specified. This will include all files in all sub directories. Opening a git directory will only include files that are already added in the repository, this requires `git` to exist in path.

boreopen
-------------------------------------------------------
Open a help-like window listing all files in the solution. Use `/` to search for the wanted file and press `enter` to open it.
boreopen

boretoggle
-------------------------------------------------------
Cycle between related files in the solution. The order is hardcoded to: cpp cxx c inl hpp hxx h pro asm s ddf

borefind [-i] [-p] [-e ext1,ext2,...,ext9] <string>
-------------------------------------------------------
Do an exact string search through all files in the solution for <string>. At most 100 hits per file is reported and the total hits is capped to 1000. The search is case sensitive by default. Optionally the search can be case insensitive `-i`, restricted to the project of the current buffer `-p`, or limited to a set of file extensions `-e`.

boreconfig[!] [configuration|platform]
------------------------------------------------------
Show or set the currently active solution configuration and platform. Used when executing any of the borebuild commands. `boreconfig!` shows a list with all available configurations. Setting the configuration and project uses a string prefix match, so switching between release and debug is as simple as `:borec r` and `:borec d`.

borebuild<sln|proj|projonly|file|info>[!] [project_name | file]
------------------------------------------------------
Build the whole solution `:borebuildsln`, or specified project `:borebuildproj` with or without references `:borebuildprojonly`, or file `:borebuildfile`, using the currently active configuration. Bang `!` will force a rebuild. `:borebuildinfo` will show the status of the current or last build. Requires `msbuild` to exist in path.

boreproj[!] [project_name | file]
------------------------------------------------------
Show or set the currently active project. Only used to set the `g:bore_proj_path` variable, useful for scripting or commands. `boreproj!` shows a list of all available projects. Setting the project uses a string prefix match to save some typing.

ctoggle, ltoggle
------------------------------------------------------
Toggle (as in show or hide) the quickfix list or location list window easily without any complicated vim scripts. This command is easy to use in a key binding like `
nnoremap <silent><F4> :ctoggle<CR>`.

CTRL-W CTRL-m
------------------------------------------------------
Window command to move cursor between the two largest windows.

bore_ctrlpmatch(...)
------------------------------------------------------
Fast ctrlp matcher function written in c code for ctrlp. A simple algorithm that requires all substrings to match, always producing meaningful results without ranking the hits.
`let g:ctrlp_match_func = { 'match': 'bore_ctrlpmatch' } `

bore_statusline(int flags)
------------------------------------------------------
Use in `statusline` or `titlestring` to display any combination of project `0x04` of current buffer, or active configuration `0x02` and platform `0x01`. Example usage:
```vim
if has('bore')
	set statusline+=%{bore_statusline(4)}
	set titlestring=%{v:servername}%{bore_statusline(3)}\ -\ %f%{bore_statusline(4)}
endif
```

g:bore_base_dir
-------------------------------------------------------
The base directory of the solution file. It is either the directory of the solution file itself, or its parent directory. All bore file paths are relative to this directory. Useful for e.g. writing a single tags file from all solution files.

g:bore_sln_config
-------------------------------------------------------
The currently active solution configuration, i.e. `configuration|platform`.

g:bore_filelist_file
-------------------------------------------------------
The filename of the file which contains a list of relative paths for all files included in the solution. Useful for e.g. building a tags file from all solution files.

g:bore_proj_path
-------------------------------------------------------
The path to the project set by `boreproj`, useful for scripting.

g:bore_search_thread_count
-------------------------------------------------------
The number of threads used by `borefind`. Defaults to 4.
