import Mathlib

/-!
Audit of the standalone printed hypotheses of Corollary 4.7 in Matolcsi et al.,
*Triplets of Mutually Unbiased Bases*. The explicit unimodular vectors below
satisfy its two displayed μ(I)-product hypotheses for I={0,2,4}, but their
ratios have no opposite pairing across I and its complement. This addresses
only the corollary as printed without an additional orthogonality hypothesis;
it is not a counterexample involving MUBs or to the triplet conjecture.
-/

namespace OQP13Corollary47Audit

abbrev Index := Fin 6
abbrev TripleIndex := Fin 3

def evenIdx (i : TripleIndex) : Index := ⟨2 * i.val, by omega⟩
def oddIdx (i : TripleIndex) : Index := ⟨2 * i.val + 1, by omega⟩

def aVec : Index → ℂ := fun _ => 1
def bVec : Index → ℂ := fun i => if i.val = 0 then -1 else 1

noncomputable def ratio (i : Index) : ℂ := aVec i / bVec i

/- The μ(I)-product for I={0,2,4}; μ is -1 on I and +1 on Iᶜ. -/
noncomputable def muProduct (v : Index → ℂ) : ℂ :=
  (v 0)⁻¹ * (v 2)⁻¹ * (v 4)⁻¹ * v 1 * v 3 * v 5

lemma aVec_unimodular : ∀ i, Complex.normSq (aVec i) = 1 := by
  intro i
  simp [aVec]

lemma bVec_unimodular : ∀ i, Complex.normSq (bVec i) = 1 := by
  intro i
  by_cases h : i.val = 0 <;> simp [bVec, h]

lemma aVec_muProduct : muProduct aVec = 1 := by
  simp [muProduct, aVec]

lemma bVec_muProduct : muProduct bVec = -1 := by
  simp [muProduct, bVec]

lemma even_ratio (i : TripleIndex) : ratio (evenIdx i) =
    if i.val = 0 then -1 else 1 := by
  fin_cases i <;> norm_num [ratio, evenIdx, aVec, bVec]

lemma odd_ratio (i : TripleIndex) : ratio (oddIdx i) = 1 := by
  fin_cases i <;> norm_num [ratio, oddIdx, aVec, bVec]

theorem no_compatible_opposite_pairing :
    ¬ ∃ σ : TripleIndex ≃ TripleIndex,
      ∀ i, ratio (evenIdx i) + ratio (oddIdx (σ i)) = 0 := by
  rintro ⟨σ, hσ⟩
  have h := hσ ⟨1, by omega⟩
  norm_num [even_ratio, odd_ratio] at h

theorem printed_hypotheses_without_pairing :
    (∀ i, Complex.normSq (aVec i) = 1) ∧
    (∀ i, Complex.normSq (bVec i) = 1) ∧
    muProduct aVec = 1 ∧ muProduct bVec = -1 ∧
    (¬ ∃ σ : TripleIndex ≃ TripleIndex,
      ∀ i, ratio (evenIdx i) + ratio (oddIdx (σ i)) = 0) := by
  exact ⟨aVec_unimodular, bVec_unimodular, aVec_muProduct,
    bVec_muProduct, no_compatible_opposite_pairing⟩

end OQP13Corollary47Audit
