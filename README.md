# IQOQI Open Quantum Problem 13

This repository records formal and computational work on the maximum number of pairwise mutually unbiased orthonormal bases in dimension six.

## Current mathematical status

The dimension-six problem remains open. The target in the supplied Google DeepMind Formal Conjectures file is

```lean
IsMaxMUBCount 6 (answer(sorry))
```

with `IsUnbiased U V` defined by exact equality of every squared overlap to `1 / 6`. The attached `13.lean` matches the official file at Formal Conjectures commit `df3f12d7bd06feb3f71ae37abae0ca7cb798d9b1` (Lean 4.33.1); both copies have SHA-256 `D9A1A0D62ABCD66A5A501069155BC4889444F9ECA37D5C1A56AF3062F77F56AD`. In that source, both the dimension-six bounds statement and the dimension-six target still contain `sorry`; the file's prose reports the known bounds `3 ≤ μ(6) ≤ 7`. This repository independently formalizes the known lower bound `HasMUBs 6 3`, but does not solve the open upper-bound problem.

## Checked Lean results

[`Reduction.lean`](Reduction.lean) imports the official definitions and proves:

* left multiplication of both bases by the same unitary preserves `IsUnbiased`;
* any four-base family can therefore be normalized so its first basis is the identity;
* `HasMUBs 6 4` is equivalent to finding three unitaries `H`, `K`, and `L`, each unbiased
  to the identity and pairwise unbiased to each other, exposing the six transition constraints;
* assuming three bases exist, proving that no four-base family exists is equivalent to proving that the maximum is three.

These are reductions, not the missing nonexistence theorem. The central unresolved task is still
`¬ HasMUBs 6 4`.

The dimension-six lower bound is formalized in [`LowerBound6.lean`](LowerBound6.lean): it tensors
the official qubit Z/X/Y bases with the qutrit computational/Fourier/chirp bases and proves
`OQP13LowerBound6.hasMUBs_6_3 : HasMUBs 6 3`. [`QutritMUB.lean`](QutritMUB.lean) proves the
qutrit Gram and cross-overlap identities; [`TensorMUB6.lean`](TensorMUB6.lean) proves tensor
unitarity and unbiasedness survive the `Fin 2 × Fin 3 ≃ Fin 6` reindexing.
[`SixRootPairing.lean`](SixRootPairing.lean) formalizes a related six-value Newton-identity
lemma: for six unit-modulus values, vanishing first and third power sums yields a permutation of
the six indices that sends each value to its negative, preserving multiplicities; that permutation
has no fixed points. More generally, vanishing odd power sums through degree five is equivalent to
such a permutation without a unit-modulus assumption. The permutation is not shown to be an
involution, and the lemma does not derive the power-sum hypotheses from MUB-triplet constraints or
classify MUB triplets.

[`Proposition46.lean`](Proposition46.lean) formalizes the six-value algebraic step in Proposition
4.6 of the cited triplet paper: for six unit-modulus values whose sum is zero and whose alternating
triple-product sum is zero, it constructs a bijection pairing each even-indexed value with an
opposite odd-indexed value. This is a conditional reduction; the required product identity has not
been derived for every MUB triplet.

[`Corollary47Audit.lean`](Corollary47Audit.lean) checks the displayed hypotheses of the paper's
Corollary 4.7 as printed. Without orthogonality, those hypotheses alone do not imply its pairing
conclusion: an explicit pair of unit vectors satisfies the stated μ(I)-product conditions but has
no compatible opposite pairing. The proof of that corollary invokes Proposition 4.6, which also
requires the ratios to sum to zero. This identifies a missing hypothesis in the standalone wording;
orthogonality of Hadamard columns could supply it in the intended application. It is not a
counterexample among MUBs and does not refute the paper's triplet conjecture.

[`Corollary47FixedI.lean`](Corollary47FixedI.lean) proves the fixed-partition corrected version:
adding the zero-sum orthogonality condition on the coordinatewise ratios lets the two μ-product
identities feed into Proposition 4.6 and yield the claimed pairing. This is the form available for
orthogonal columns of a complex Hadamard matrix; it does not establish the broader hypotheses of
Conjecture 2 from all MUB-cube axioms.

[`AxiomAudit.lean`](AxiomAudit.lean) checks the key results with `#print axioms`. The reduction,
lower-bound, and six-root theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`;
none reports `sorryAx`.

## Verification

The file was checked in the supplied `formal-conjectures` checkout with Lean 4.33.1 and its pinned Mathlib dependencies:

```powershell
cd <this repository>
.\verify.ps1
```

The script checks that the adjacent `formal-conjectures` checkout is at the pinned commit,
builds the official OQP 13 module, compiles the project Lean modules in dependency order, and
prints the axiom report. Generated `.olean` files are ignored by Git.

The official OQP 13 source is [13.lean](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/OpenQuantumProblems/13.lean); the IQOQI source problem is [Mutually unbiased bases](https://oqp.iqoqi.oeaw.ac.at/mutually-unbiased-bases).

## Research lead from the attached brief

The brief proposes using the order-six complex Hadamard classification as a starting point. The cited August 2026 preprint does claim a complete classification and links a Lean 4 formalization, but that classification alone does not rule out four MUBs. No interval exclusion, exhaustive search certificate, or proof for the remaining special families is included here. Numerical optimizer minima are not proofs of nonexistence and are not presented as such.

There is also a constraint-counting correction to the brief's generic MU-vector heuristic. For a phase vector and a fixed Hadamard matrix, the six squared-overlap equations have a sum fixed by unitarity and the vector norm, so at most five are independent. Counting them as six independent equations in five phases does not establish generic nonexistence; any such claim needs a transversality argument or an explicit certified analysis.

The authors' older whole-Fourier-family exclusion was independently rerun from their public C++ source on the i9-275HX. The 82,630-row orthogonality database reproduced exactly (SHA-256 `F304A87CD2FE65B87A130A9FF49EDDC0980AD28A852B98099AF68AF876DB3877`); all 270 parameter-cell outputs matched the authors' published `fab_ubv.txt` line-for-line. The expensive final parameter cell was divided over disjoint row-index ranges, whose counts sum to the authors' totals for that cell (11,857,999 candidate third bases and 650,745 cases requiring a fourth-basis check).

This is a reproduction of a published *partial* exclusion, not a new proof of the full OQP 13 result and not a Lean-verified numerical certificate. The source uses double-precision arithmetic with an epsilon margin. Its mathematical scope is only quartets containing a transition matrix in the two-parameter Fourier family. The unresolved extension is to show that every possible MUB triplet has such a transition, or otherwise exclude compatible quartets across the remaining Hadamard classes.

An adversarial read of Matolcsi et al.'s triplet route found an apparent gap in the compression from Conjecture 2 to Eq. (4.9): Conjecture 2 asks for zero products at each matching permutation, while Eq. (4.9) multiplies two independent permutation sums and includes cross-permutation terms. Nonnegativity justifies the analogous sum for the first condition, but does not alone justify this second compression. No support-alignment lemma is stated around Eqs. (4.8)–(4.9). This is not a counterexample among actual MUB triplets; it means the displayed equivalence needs an additional structural argument or a corrected aggregate identity.

Sources: Cárdenes Wuttig and Tindall, [A Complete Classification of Complex Hadamard Matrices of Order Six](https://arxiv.org/abs/2608.18053); Matolcsi, Matszangosz, Varga, and Weiner, [Triplets of Mutually Unbiased Bases](https://arxiv.org/abs/2503.14752), §4; Jaming, Matolcsi, Móra, Szöllősi, and Weiner, [A generalized Pauli problem and an infinite family of MUB-triplets in dimension 6](https://arxiv.org/abs/0902.0882), with code/data linked from the authors' [documentation page](http://www.math.bme.hu/~matolcsi/docu.htm).
