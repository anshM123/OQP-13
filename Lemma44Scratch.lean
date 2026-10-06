import Mathlib

/-!
Scratch formalization of the Newton-identity part of Lemma 4.4 for six
unimodular complex numbers. This file is exploratory and is not imported by
the OQP project.
-/

open Finset
open MvPolynomial

namespace OQP13Lemma44

noncomputable def esymmVal (z : Fin 6 → ℂ) (k : ℕ) : ℂ :=
  MvPolynomial.aeval z (MvPolynomial.esymm (Fin 6) ℂ k)

noncomputable def powerSum (z : Fin 6 → ℂ) (k : ℕ) : ℂ :=
  ∑ i : Fin 6, z i ^ k

lemma powerSum_eq_eval (z : Fin 6 → ℂ) (k : ℕ) :
    powerSum z k = MvPolynomial.aeval z (MvPolynomial.psum (Fin 6) ℂ k) := by
  simp [powerSum, MvPolynomial.psum]

lemma esymm_one_eq_sum (z : Fin 6 → ℂ) :
    esymmVal z 1 = powerSum z 1 := by
  rw [esymmVal, MvPolynomial.aeval_esymm_eq_multiset_esymm]
  rw [Finset.esymm_map_val z Finset.univ 1]
  simp [powerSum, Finset.powersetCard_one]

lemma esymm_three_eq_of_power_sums
    (z : Fin 6 → ℂ)
    (h1 : powerSum z 1 = 0)
    (h3 : powerSum z 3 = 0) :
    esymmVal z 3 = 0 := by
  have hn := MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin 6) ℂ 3 (by omega)
  have heval := congrArg (MvPolynomial.aeval z) hn
  have hp1 : MvPolynomial.aeval z (MvPolynomial.psum (Fin 6) ℂ 1) = 0 := by
    rw [← powerSum_eq_eval]
    exact h1
  have he1 : esymmVal z 1 = 0 := by
    rw [esymm_one_eq_sum]
    exact h1
  have hfilter :
      {a ∈ HasAntidiagonal.antidiagonal 3 | a.1 ∈ Set.Ioo 0 3} =
        {(1, 2), (2, 1)} := by
    ext a
    rcases a with ⟨a, b⟩
    simp [HasAntidiagonal.mem_antidiagonal, Set.mem_Ioo]
    omega
  -- Newton's third identity specialized at the six values. Its only
  -- lower-degree terms are `e₁ p₂` and `e₂ p₁`.
  have hnewton := heval
  rw [hfilter] at hnewton
  simp [MvPolynomial.psum] at hnewton
  have h1' : (∑ i : Fin 6, z i) = 0 := by simpa [powerSum] using h1
  rw [h1'] at hnewton
  have h3' : (∑ i : Fin 6, z i ^ 3) = 0 := by simpa [powerSum] using h3
  rw [h3'] at hnewton
  norm_num at hnewton
  exact hnewton

end OQP13Lemma44
