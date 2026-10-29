@echo off
rem One-click setup on Windows: double-click this file. Details: scripts\install.ps1
cd /d "%~dp0"
powershell -NoProfile -ExecutionPolicy Bypass -File "%~dp0scripts\install.ps1" %*
if errorlevel 1 (
  echo.
  echo Setup did not finish. Fix the error above and run install.bat again.
)
pause
