# This script installs EverParse build dependencies (including Cygwin)
# and builds EverParse.

# Choose a temporary directory name for Cygwin
$tmpRoot = "C:\"
[string] $tmpBaseName = "everparse-cygwin64.tmp"
New-Item -Path $tmpRoot -Name $tmpBaseName -ItemType directory
if (-not $?) {
   $Error
   exit 1
}
$Global:cygwinRoot = (Join-Path $tmpRoot $tmpBaseName)

function global:Invoke-BashCmd
{
    # This function invokes a Bash command via Cygwin bash.
    $Error.Clear()

    Write-Host "Args:" $args

    # Exec command
    $cygwinRoot = $Global:cygwinRoot
    $cygpathExe = "$cygwinRoot\bin\cygpath.exe"
    $cygpath = & $cygpathExe -u ${pwd}
    $bashExe = "$cygwinRoot\bin\bash.exe"
    & $bashExe --login -c "cd $cygpath && $args"

    if (-not $?) {
        Write-Host "*** Error:"
        $Error
        exit 1
    }
}

$Error.Clear()
$LastExitCode = 0

$ProgressPreference = 'SilentlyContinue'

# powershell defaults to TLS 1.0, which many sites don't support.  Switch to 1.2.
[Net.ServicePointManager]::SecurityProtocol = [Net.SecurityProtocolType]::Tls12

# Switch to this script's directory
Set-Location -ErrorAction Stop -LiteralPath $PSScriptRoot

$Error.Clear()
Write-Host "Install Cygwin with git"
Invoke-WebRequest "https://www.cygwin.com/setup-x86_64.exe" -outfile "cygwinsetup.exe"
cmd.exe /c start /wait .\cygwinsetup.exe --root $Global:cygwinRoot -P git,wget --no-desktop --no-shortcuts --no-startmenu --wait --quiet-mode --site https://mirrors.kernel.org/sourceware/cygwin/
if (-not $?) {
    $Error
    exit 1
}
Remove-Item "cygwinsetup.exe"

$Error.Clear()
Write-Host "Install and build everparse dependencies"
Invoke-BashCmd "./everest.sh --yes -j 6 check"
if (-not $?) {
    $Error
    exit 1
}

$Error.Clear()
Write-Host "build everparse"
Invoke-BashCmd "./build-everparse.sh"
if (-not $?) {
    $Error
    exit 1
}

$Error.Clear()
Write-Host "remove our copy of Cygwin"
Remove-Item -Recurse -Force -Path $Global:cygwinRoot
if (-not $?) {
    $Error
    exit 1
}

Write-Host "EverParse is now built."
