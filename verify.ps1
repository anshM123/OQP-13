$ErrorActionPreference = 'Stop'

$repoDir = $PSScriptRoot
$officialDir = (Resolve-Path (Join-Path $repoDir '..\formal-conjectures')).Path
$expectedCommit = 'df3f12d7bd06feb3f71ae37abae0ca7cb798d9b1'

Push-Location $officialDir
try {
    $actualCommit = (& git rev-parse HEAD).Trim()
    if ($LASTEXITCODE -ne 0) { throw 'Could not read the formal-conjectures commit.' }
    if ($actualCommit -ne $expectedCommit) {
        throw "Expected formal-conjectures $expectedCommit, found $actualCommit."
    }

    & lake build 'FormalConjectures.OpenQuantumProblems.«13»'
    if ($LASTEXITCODE -ne 0) { throw 'The official OQP 13 module did not build.' }

    $env:LEAN_PATH = "$repoDir;$env:LEAN_PATH"
    $modules = @(
        'QutritMUB',
        'TensorMUB',
        'TensorMUB6',
        'Reduction',
        'LowerBound',
        'LowerBound6',
        'SixRootPairing',
        'Proposition46',
        'Corollary47Audit',
        'Corollary47FixedI',
        'Lemma44Scratch',
        'AxiomAudit'
    )

    foreach ($module in $modules) {
        Write-Host "Lean check: $module"
        $source = Join-Path $repoDir "$module.lean"
        $output = Join-Path $repoDir "$module.olean"
        & lake env lean --root=$repoDir -o $output $source
        if ($LASTEXITCODE -ne 0) { throw "Lean check failed: $module" }
    }
}
finally {
    Pop-Location
}
