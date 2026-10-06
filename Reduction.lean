import FormalConjectures.OpenQuantumProblems.«13»

/-!
This file is checked against the definitions in the official Formal Conjectures OQP 13.
It proves only the normalization and reduction steps. It does not assert the open
nonexistence of four mutually unbiased bases in dimension six.
-/

namespace OQP13

open OpenQuantumProblem13

theorem relativeUnitary_eq_group {d : ℕ} (U V : UMat d) :
    relativeUnitary U V = ((U⁻¹ * V : UMat d) : Matrix (Fin d) (Fin d) ℂ) := by
  rfl

theorem isUnbiased_left_mul {d : ℕ} (W U V : UMat d)
    (h : IsUnbiased U V) : IsUnbiased (W * U) (W * V) := by
  intro i j
  have heq : relativeUnitary (W * U) (W * V) = relativeUnitary U V := by
    simp [relativeUnitary_eq_group, mul_inv_rev, mul_assoc]
  rw [heq]
  exact h i j

def normalizeFamily {d k : ℕ} (B : Fin k → UMat d) (i₀ : Fin k) : Fin k → UMat d :=
  fun i => (B i₀)⁻¹ * B i

theorem normalizeFamily_at {d k : ℕ} (B : Fin k → UMat d) (i₀ : Fin k) :
    normalizeFamily B i₀ i₀ = 1 := by
  simp [normalizeFamily]

theorem normalizeFamily_isMUB {d k : ℕ} (B : Fin k → UMat d) (i₀ : Fin k)
    (hB : IsMUBFamily B) : IsMUBFamily (normalizeFamily B i₀) := by
  intro i j hij
  exact isUnbiased_left_mul (B i₀)⁻¹ (B i) (B j) (hB hij)

theorem four_iff_normalized :
    HasMUBs 6 4 ↔ ∃ B : Fin 4 → UMat 6, B 0 = 1 ∧ IsMUBFamily B := by
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨normalizeFamily B 0, normalizeFamily_at B 0, normalizeFamily_isMUB B 0 hB⟩
  · rintro ⟨B, _, hB⟩
    exact ⟨B, hB⟩

theorem max_three_iff_no_four (h3 : HasMUBs 6 3) :
    IsMaxMUBCount 6 3 ↔ ¬ HasMUBs 6 4 := by
  constructor
  · intro hmax h4
    have hle := hmax.2 4 h4
    omega
  · intro h4
    refine ⟨h3, ?_⟩
    intro m hm
    by_contra hnot
    have hle : 4 ≤ m := by omega
    obtain ⟨B, hB⟩ := hm
    let C : Fin 4 → UMat 6 := fun i => B (Fin.castLE hle i)
    have hC : IsMUBFamily C := by
      intro i j hij
      apply hB
      intro heq
      exact hij (Fin.castLE_injective hle heq)
    exact h4 ⟨C, hC⟩

end OQP13

#print axioms OQP13.four_iff_normalized
#print axioms OQP13.max_three_iff_no_four
