:: command to build big Vim with/without Python for Windows 7
:: call "%ProgramFiles%\Microsoft Visual Studio\2022\Community\VC\Auxiliary\Build\vcvarsall.bat" x86
set VIM_ADD_FEATURES=FEATURES=BIG GUI=yes DIRECTX=yes COLOR_EMOJI=yes TERMINAL=yes
:: PYTHON=C:\python27 DYNAMIC_PYTHON=yes PYTHON_VER=27
set VIM_REMOVE_FEATURES=CSCOPE=no NETBEANS=no XPM=no
set VIM_FEATURES=%VIM_ADD_FEATURES% %VIM_REMOVE_FEATURES%
nmake -f Make_mvc.mak WINVER=0x0601 %VIM_FEATURES%
pause
