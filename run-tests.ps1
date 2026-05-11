# run-tests.ps1 — compile and run the STILL test suite
# Usage: .\run-tests.ps1

$ErrorActionPreference = "Stop"

Write-Host "Compiling test suite..." -ForegroundColor Cyan
ghc -threaded -O1 Tests\Main.hs -o still-tests
if ($LASTEXITCODE -ne 0) {
    Write-Host "Compilation failed." -ForegroundColor Red
    exit 1
}

Write-Host "Running tests..." -ForegroundColor Cyan
.\still-tests
if ($LASTEXITCODE -ne 0) {
    Write-Host "Tests failed." -ForegroundColor Red
    exit 1
}

Write-Host "All tests passed." -ForegroundColor Green
