param([switch] $SkipCacheDownload)

$ErrorActionPreference = 'Stop'

function Invoke-Checked([string] $Program) {
    & $Program @args
    if ($LASTEXITCODE -ne 0) { throw "$Program failed with exit code $LASTEXITCODE" }
}

$pwsh = (Get-Process -Id $PID).Path
$project = Join-Path $PSScriptRoot 'formalization/jsp-000976'
$toolchain = (Get-Content -LiteralPath (Join-Path $PSScriptRoot 'lean-toolchain') -Raw).Trim()
$work = Join-Path $PSScriptRoot '.lake/verify'
$logPath = Join-Path $work 'proof-build.log'
$modules = @(
    'Thinning', 'Rows', 'Statement', 'Geometry', 'Nested', 'StageBounds',
    'Incidence', 'NestedIncidence', 'PaletteMarks', 'DenseCone', 'ChainIdeal',
    'Occurrence', 'MarkFamily', 'PrunedFamilies', 'CompatiblePalette',
    'GroundStep', 'Finish', 'Theorem'
)

New-Item -ItemType Directory -Path $work -Force | Out-Null
[IO.File]::WriteAllText($logPath, '')
$build = Join-Path $work ([Guid]::NewGuid().ToString('N'))
$oldLeanPath = $env:LEAN_PATH
$oldThreads = $env:LEAN_NUM_THREADS
Push-Location $project
try {
    Invoke-Checked elan toolchain install $toolchain 2>&1 | Tee-Object -FilePath $logPath -Append
    if (!$SkipCacheDownload) {
        $sources = $modules | ForEach-Object { Join-Path 'Jsp000976' "$_.lean" }
        $imports = Get-Content -LiteralPath $sources | ForEach-Object {
            if ($_ -match '^(?:public )?import (Mathlib\.[A-Za-z0-9_.]+)$') { $Matches[1] }
        } | Sort-Object -Unique
        Invoke-Checked elan run $toolchain lake exe cache get @imports 2>&1 |
            Tee-Object -FilePath $logPath -Append
    }

    $prefix = 'PROOF_LEAN_PATH='
    $pathLine = @(Invoke-Checked elan run $toolchain lake env $pwsh `
        -NoProfile -Command 'Write-Output "PROOF_LEAN_PATH=$env:LEAN_PATH"' |
        Where-Object { $_ -clike "$prefix*" })
    if ($pathLine.Count -ne 1 -or $pathLine[0].Length -le $prefix.Length) {
        throw 'Lake did not provide a Lean search path'
    }

    New-Item -ItemType Directory -Path (Join-Path $build 'Jsp000976') -Force | Out-Null
    $env:LEAN_PATH = $build + [IO.Path]::PathSeparator + $pathLine[0].Substring($prefix.Length)
    $env:LEAN_NUM_THREADS = '1'
    $leanFlags = @('-j', '1', '-M', '1800', '-DwarningAsError=true')
    foreach ($module in $modules) {
        "Checking Jsp000976.$module" | Tee-Object -FilePath $logPath -Append
        Invoke-Checked elan run $toolchain lean @leanFlags `
            -o (Join-Path $build "Jsp000976/$module.olean") "Jsp000976/$module.lean" 2>&1 |
            Tee-Object -FilePath $logPath -Append
        Invoke-Checked elan run $toolchain leanchecker "Jsp000976.$module" 2>&1 |
            Tee-Object -FilePath $logPath -Append
    }

    Invoke-Checked elan run $toolchain lean @leanFlags `
        -o (Join-Path $build 'Jsp000976.olean') Jsp000976.lean 2>&1 |
        Tee-Object -FilePath $logPath -Append
    $audit = @(Invoke-Checked elan run $toolchain lean @leanFlags Audit.lean 2>&1 |
        Tee-Object -FilePath $logPath -Append)
    $audit | Write-Output
    $expected = "'Jsp000976.erdos_1171' depends on axioms: [propext, Classical.choice, Quot.sound]"
    if ($audit.Count -ne 1 -or $audit[0] -cne $expected) {
        throw 'Unexpected axiom audit for Jsp000976.erdos_1171'
    }
    Write-Output 'Verified Jsp000976.erdos_1171 with only standard Lean axioms.'
} finally {
    $env:LEAN_PATH = $oldLeanPath
    $env:LEAN_NUM_THREADS = $oldThreads
    Pop-Location
    if (Test-Path -LiteralPath $build) { Remove-Item -LiteralPath $build -Recurse -Force }
}
