@echo off
rem Starts the lemmata web UI (http://127.0.0.1:7860) and opens it in the browser.
setlocal
cd /d "%~dp0"
set "PYTHONUTF8=1"
set "PATH=%USERPROFILE%\.elan\bin;%PATH%"
set "PYEXE="
if exist ".work\python.txt" set /p PYEXE=<".work\python.txt"
if defined PYEXE goto run
where py >nul 2>nul
if not errorlevel 1 (
  py -3 -m lemmata.webui %*
  goto end
)
set "PYEXE=python"
:run
"%PYEXE%" -m lemmata.webui %*
:end
if errorlevel 1 pause
