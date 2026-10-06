$ErrorActionPreference = 'Stop'

$repoDir = $PSScriptRoot
$officialDir = (Resolve-Path (Join-Path $repoDir '..\formal-conjectures')).Path
$expectedCommit = 'df3f12d7bd06feb3f71ae37abae0ca7cb798d9b1'
$expectedProblemHash = 'D9A1A0D62ABCD66A5A501069155BC4889444F9ECA37D5C1A56AF3062F77F56AD'

Push-Location $officialDir
try {
    $actualCommit = (& git rev-parse HEAD).Trim()
    if ($LASTEXITCODE -ne 0) { throw 'Could not read the formal-conjectures commit.' }
    if ($actualCommit -ne $expectedCommit) {
        throw "Expected formal-conjectures $expectedCommit, found $actualCommit."
    }

    $problemFile = Join-Path $officialDir 'FormalConjectures\OpenQuantumProblems\13.lean'
    $actualProblemHash = (Get-FileHash $problemFile -Algorithm SHA256).Hash
    if ($actualProblemHash -ne $expectedProblemHash) {
        throw "Official OQP 13 source hash mismatch: expected $expectedProblemHash, found $actualProblemHash."
    }

    & lake build 'FormalConjectures.OpenQuantumProblems.«13»'
    if ($LASTEXITCODE -ne 0) { throw 'The official OQP 13 module did not build.' }

    $env:LEAN_PATH = "$repoDir;$env:LEAN_PATH"
    $modules = @(
        'QutritMUB',
        'JamingLemma21',
        'JamingFourierFamilyReduction',
        'TensorMUB',
        'TensorMUB6',
        'Reduction',
        'OverlapConstraint',
        'HadamardBridge',
        'LowerBound',
        'LowerBound6',
        'SixRootPairing',
        'HadamardRootBridge',
        'Proposition46',
        'Corollary47Audit',
        'Corollary47FixedI',
        'Corollary47ArbitraryI',
        'AggregateProductGap',
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
