# One-click setup for Windows: Python, Git, Lean (elan), Mathlib, the Mathlib name index, PutnamBench,
# the API key, a desktop shortcut, and the web UI. Run it through install.bat (double-click), or:
#   powershell -ExecutionPolicy Bypass -File scripts\install.ps1 [-SkipNameIndex] [-SkipPutnamBench] [-NoShortcut] [-NoWebUI]
# Safe to run again: finished steps are skipped.
param(
    [switch] $SkipNameIndex,
    [switch] $SkipPutnamBench,
    [switch] $NoShortcut,
    [switch] $NoWebUI
)
$ErrorActionPreference = "Stop"
$ProgressPreference = "SilentlyContinue"
[Net.ServicePointManager]::SecurityProtocol = [Net.SecurityProtocolType]::Tls12
$Root = Split-Path -Parent $PSScriptRoot
Set-Location $Root
$PutnamBenchCommit = "c8c8fa28aa1815a85991668ec0b020dd216d631d"

function Step($msg) { Write-Host "`n==> $msg" -ForegroundColor Cyan }
function Ok($msg) { Write-Host "    $msg" -ForegroundColor Green }
function Fail($msg) {
    Write-Host "`nERROR: $msg" -ForegroundColor Red
    exit 1
}
function Have($cmd) { [bool](Get-Command $cmd -ErrorAction SilentlyContinue) }
function Refresh-Path {
    $env:Path = [Environment]::GetEnvironmentVariable("Path", "Machine") + ";" +
                [Environment]::GetEnvironmentVariable("Path", "User")
}
function Run($exe, [string[]] $arguments) {
    & $exe @arguments
    if ($LASTEXITCODE -ne 0) { Fail "'$exe $($arguments -join ' ')' failed (exit code $LASTEXITCODE)" }
}
function Winget-Install($id, $what) {
    if (-not (Have "winget")) {
        Fail "$what is not installed and winget is not available. Install $what manually, then run install.bat again."
    }
    Write-Host "    installing $what with winget..."
    & winget install -e --id $id --scope user --accept-package-agreements --accept-source-agreements
    if ($LASTEXITCODE -ne 0) {
        & winget install -e --id $id --accept-package-agreements --accept-source-agreements
    }
    Refresh-Path
}

# ---------------------------------------------------------------------------------------------------------------
# Mathlib's build tree is deep; long folder names can hit the 260-character path limit of Windows.
$longPaths = (Get-ItemProperty "HKLM:\SYSTEM\CurrentControlSet\Control\FileSystem" -ErrorAction SilentlyContinue).LongPathsEnabled
if ($Root.Length -gt 60 -and $longPaths -ne 1) {
    Write-Host "WARNING: the project folder path is long ($($Root.Length) characters) and Windows long paths are off." -ForegroundColor Yellow
    Write-Host "         If Mathlib fails to download or build, move the folder to e.g. C:\lemmata, or enable long paths:" -ForegroundColor Yellow
    Write-Host "         https://learn.microsoft.com/windows/win32/fileio/maximum-file-path-limitation" -ForegroundColor Yellow
}

Step "Python 3.10 or newer"
function Find-Python {
    foreach ($c in @("py -3", "python", "python3")) {
        $parts = $c -split " "
        $exe = $parts[0]
        $rest = @($parts | Select-Object -Skip 1)
        if (-not (Have $exe)) { continue }
        try {
            # the Microsoft Store "python" stub exits with an error here, so it is skipped
            $out = & $exe @rest -c "import sys; print(sys.executable) if sys.version_info >= (3, 10) else sys.exit(1)" 2>$null
            if ($LASTEXITCODE -eq 0 -and $out) { return ($out | Select-Object -Last 1).Trim() }
        } catch { }
    }
    $local = Get-ChildItem "$env:LOCALAPPDATA\Programs\Python\Python3*\python.exe" -ErrorAction SilentlyContinue |
             Sort-Object FullName -Descending | Select-Object -First 1
    if ($local) { return $local.FullName }
    return $null
}
$Python = Find-Python
if (-not $Python) {
    Winget-Install "Python.Python.3.12" "Python 3.12"
    $Python = Find-Python
}
if (-not $Python) { Fail "Python was installed but cannot be found. Close this window and run install.bat again." }
Ok "using $Python"

# ---------------------------------------------------------------------------------------------------------------
Step "Git"
if (-not (Have "git")) {
    Winget-Install "Git.Git" "Git"
    foreach ($p in @("$env:ProgramFiles\Git\cmd", "$env:LOCALAPPDATA\Programs\Git\cmd")) {
        if (Test-Path "$p\git.exe") { $env:Path = "$p;$env:Path" }
    }
}
if (-not (Have "git")) { Fail "Git was installed but cannot be found. Close this window and run install.bat again." }
Ok (& git --version)

# ---------------------------------------------------------------------------------------------------------------
Step "Lean toolchain manager (elan)"
$ElanBin = Join-Path $env:USERPROFILE ".elan\bin"
if (-not (Test-Path (Join-Path $ElanBin "lake.exe"))) {
    $init = Join-Path $env:TEMP "elan-init.ps1"
    Invoke-WebRequest "https://raw.githubusercontent.com/leanprover/elan/master/elan-init.ps1" -OutFile $init -UseBasicParsing
    & $init -NoPrompt 1 -DefaultToolchain none
    Remove-Item $init -ErrorAction SilentlyContinue
}
$env:Path = "$ElanBin;$env:Path"
if (-not (Test-Path (Join-Path $ElanBin "lake.exe"))) { Fail "elan installation failed." }
Ok "elan is in $ElanBin"

# ---------------------------------------------------------------------------------------------------------------
Step "Mathlib and its prebuilt cache (several GB, the first time takes a while)"
Run "lake" @("exe", "cache", "get")
Ok "Mathlib is ready"

# ---------------------------------------------------------------------------------------------------------------
if (-not $SkipPutnamBench) {
    Step "PutnamBench (only needed for benchmark runs)"
    if (-not (Test-Path "benchmarks\PutnamBench")) {
        New-Item -ItemType Directory -Force "benchmarks" | Out-Null
        Run "git" @("clone", "--quiet", "https://github.com/trishullab/PutnamBench.git", "benchmarks\PutnamBench")
        Run "git" @("-C", "benchmarks\PutnamBench", "-c", "advice.detachedHead=false", "checkout", "--quiet", $PutnamBenchCommit)
    }
    Ok "benchmarks\PutnamBench"
}

# ---------------------------------------------------------------------------------------------------------------
New-Item -ItemType Directory -Force ".work" | Out-Null
if (-not $SkipNameIndex) {
    Step "Mathlib name index (one time, 10-20 minutes)"
    if (-not (Test-Path ".work\mathlib_names.tsv") -or (Get-Item ".work\mathlib_names.tsv").Length -eq 0) {
        Run "lake" @("env", "lean", "scripts\dump_mathlib_names.lean")
    }
    Ok ".work\mathlib_names.tsv"
}

# ---------------------------------------------------------------------------------------------------------------
Step "Checking Lean + Mathlib"
Set-Content -Path ".work\smoke.lean" -Encoding Ascii -Value "import Mathlib`nexample : (2 : Nat) + 2 = 4 := by norm_num"
Run "lake" @("env", "lean", ".work\smoke.lean")
Ok "Lean + Mathlib work"
Set-Content -Path ".work\python.txt" -Encoding Ascii -NoNewline -Value $Python

# ---------------------------------------------------------------------------------------------------------------
Step "DeepSeek API key"
if (-not (Test-Path ".env")) { Copy-Item ".env.example" ".env" }
$env:PYTHONUTF8 = "1"
$hasKey = & $Python -c "from lemmata import llm; print(1 if llm.settings()['api_key'] else 0)"
if ($hasKey -eq "1") {
    Ok "already set in .env"
} else {
    Write-Host "    Get a key at https://platform.deepseek.com (API keys). Press Enter to skip and set it later in the web UI."
    $secure = Read-Host "    DeepSeek API key" -AsSecureString
    $key = [Runtime.InteropServices.Marshal]::PtrToStringAuto([Runtime.InteropServices.Marshal]::SecureStringToBSTR($secure))
    if ($key.Trim()) {
        $key.Trim() | & $Python -c "import sys; from lemmata import dotenv; dotenv.update({'LEMMATA_API_KEY': sys.stdin.readline().strip()})"
        Ok "saved to .env"
    } else {
        Ok "skipped"
    }
}

# ---------------------------------------------------------------------------------------------------------------
if (-not $NoShortcut) {
    Step "Desktop shortcut"
    try {
        $shell = New-Object -ComObject WScript.Shell
        $lnk = $shell.CreateShortcut((Join-Path ([Environment]::GetFolderPath("Desktop")) "Lemmata.lnk"))
        $lnk.TargetPath = Join-Path $Root "start_webui.bat"
        $lnk.WorkingDirectory = $Root
        $lnk.Description = "Lemmata web UI"
        $lnk.Save()
        Ok "Lemmata on the desktop starts the web UI"
    } catch {
        Write-Host "    could not create a shortcut; use start_webui.bat instead"
    }
}

Write-Host "`nSetup finished. Start the web UI any time with start_webui.bat (or the desktop shortcut)." -ForegroundColor Green
if (-not $NoWebUI) {
    Start-Process -FilePath (Join-Path $Root "start_webui.bat") -WorkingDirectory $Root
}
