# IQOQI Open Quantum Problem 13

This repository records formal and computational work on the maximum number of pairwise mutually unbiased orthonormal bases in dimension six.

## Current mathematical status

The dimension-six problem remains open. The target in the supplied Google DeepMind Formal Conjectures file is

```lean
IsMaxMUBCount 6 (answer(sorry))
```

with `IsUnbiased U V` defined by exact equality of every squared overlap to `1 / 6`. The attached `13.lean` matches the official file at Formal Conjectures commit `df3f12d7bd06feb3f71ae37abae0ca7cb798d9b1` (Lean 4.33.1). In that source, both the dimension-six bounds statement and the dimension-six target still contain `sorry`; the file's prose reports the known bounds `3 ≤ μ(6) ≤ 7`. This repository does not claim to have solved the open problem.

## Checked Lean results

[`Reduction.lean`](Reduction.lean) imports the official definitions and proves:

* left multiplication of both bases by the same unitary preserves `IsUnbiased`;
* any four-base family can therefore be normalized so its first basis is the identity;
* assuming three bases exist, proving that no four-base family exists is equivalent to proving that the maximum is three.

The last statement is a reduction, not the missing nonexistence theorem. The lower-bound witness is a premise there; the central unresolved task is still `¬ HasMUBs 6 4`.

Lean's `#print axioms` reports `propext`, `Classical.choice`, and `Quot.sound` for the two top-level reduction theorems. It does not report `sorryAx` for either theorem.

## Verification

The file was checked in the supplied `formal-conjectures` checkout with Lean 4.33.1 and its pinned Mathlib dependencies:

```powershell
cd <formal-conjectures checkout>
git checkout df3f12d7bd06feb3f71ae37abae0ca7cb798d9b1
lake build FormalConjectures.OpenQuantumProblems.«13»
lake env lean "<path to this repository>/Reduction.lean"
```

The official OQP 13 source is [13.lean](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OpenQuantumProblems/13.lean); the IQOQI source problem is [Mutually unbiased bases](https://oqp.iqoqi.oeaw.ac.at/mutually-unbiased-bases).

## Research lead from the attached brief

The brief proposes using the order-six complex Hadamard classification as a starting point. The cited August 2026 preprint does claim a complete classification and links a Lean 4 formalization, but that classification alone does not rule out four MUBs. No interval exclusion, exhaustive search certificate, or proof for the remaining special families is included here. Numerical optimizer minima are not proofs of nonexistence and are not presented as such.

Source: Cárdenes Wuttig and Tindall, [A Complete Classification of Complex Hadamard Matrices of Order Six](https://arxiv.org/abs/2608.18053), especially its data availability section and linked formalization.
