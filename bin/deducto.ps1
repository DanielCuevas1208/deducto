$ErrorActionPreference = "Stop"
$root = Split-Path -Parent (Split-Path -Parent $MyInvocation.MyCommand.Path)
& guile -L (Join-Path $root "src") (Join-Path $root "src\main.scm") @args
exit $LASTEXITCODE