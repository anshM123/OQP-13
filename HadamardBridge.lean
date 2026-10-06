import Reduction

/-!
# Bridge from official MUB bases to complex Hadamard matrices

The classification literature usually works with complex Hadamard matrices whose entries have
unit modulus. The official OQP 13 file instead represents a basis by a unitary matrix and
expresses unbiasedness using squared overlaps `1 / 6`. Multiplying a relative unitary by
`sqrt 6` converts exactly between these conventions.

This file proves that translation. It does not use or formalize any classification theorem.
-/

namespace OQP13HadamardBridge

open OpenQuantumProblem13

noncomputable def hadamardScale : ℂ := (Real.sqrt 6 : ℝ)

noncomputable def scaledRelative (U V : UMat 6) : Matrix (Fin 6) (Fin 6) ℂ :=
  hadamardScale • relativeUnitary U V

/-- A complex Hadamard matrix in the standard convention: flat unit-modulus entries and
orthogonal columns of squared norm six. -/
def IsComplexHadamard (H : Matrix (Fin 6) (Fin 6) ℂ) : Prop :=
  (∀ i j, Complex.normSq (H i j) = 1) ∧
    star H * H = (6 : ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ)

lemma hadamardScale_star_mul : star hadamardScale * hadamardScale = (6 : ℂ) := by
  simp [hadamardScale, ← Complex.ofReal_mul]

lemma hadamardScale_normSq : Complex.normSq hadamardScale = 6 := by
  have hs : (Complex.normSq hadamardScale : ℂ) = 6 := by
    rw [Complex.normSq_eq_conj_mul_self]
    exact hadamardScale_star_mul
  exact_mod_cast hs

lemma star_smul_mul_smul {n : Type*} [Fintype n] [DecidableEq n]
    (a : ℂ) (A B : Matrix n n ℂ) :
    star (a • A) * (a • B) = (star a * a) • (star A * B) := by
  ext i j
  simp [Matrix.mul_apply, Matrix.star_apply, Finset.mul_sum, mul_assoc, mul_left_comm,
    mul_comm]

lemma scaledRelative_gram (U V : UMat 6) :
    star (scaledRelative U V) * scaledRelative U V =
      (6 : ℂ) • (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
  rw [scaledRelative, star_smul_mul_smul, hadamardScale_star_mul]
  rw [OQP13.relativeUnitary_eq_group]
  rw [Matrix.UnitaryGroup.star_mul_self]

lemma scaledRelative_entry_normSq (U V : UMat 6) (i j : Fin 6)
    (hUV : IsUnbiased U V) :
    Complex.normSq (scaledRelative U V i j) = 1 := by
  have hentry : Complex.normSq (relativeUnitary U V i j) = (6 : ℝ)⁻¹ :=
    (RCLike.normSq_eq_def' _).trans (hUV i j)
  change Complex.normSq (hadamardScale * relativeUnitary U V i j) = 1
  rw [Complex.normSq_mul, hadamardScale_normSq, hentry]
  norm_num

theorem scaledRelative_isComplexHadamard (U V : UMat 6)
    (hUV : IsUnbiased U V) : IsComplexHadamard (scaledRelative U V) := by
  exact ⟨fun i j => scaledRelative_entry_normSq U V i j hUV, scaledRelative_gram U V⟩

theorem scaledRelative_isUnbiased_of_isComplexHadamard (U V : UMat 6)
    (h : IsComplexHadamard (scaledRelative U V)) : IsUnbiased U V := by
  intro i j
  have hentry : Complex.normSq (hadamardScale * relativeUnitary U V i j) = 1 := by
    exact h.1 i j
  rw [Complex.normSq_mul, hadamardScale_normSq] at hentry
  have hnormSq : Complex.normSq (relativeUnitary U V i j) = (6 : ℝ)⁻¹ := by
    have hfrac : Complex.normSq (relativeUnitary U V i j) = 1 / 6 := by
      linarith
    calc
      Complex.normSq (relativeUnitary U V i j) = 1 / 6 := hfrac
      _ = (6 : ℝ)⁻¹ := by norm_num
  exact (RCLike.normSq_eq_def' (relativeUnitary U V i j)).symm.trans hnormSq

theorem scaledRelative_isComplexHadamard_iff (U V : UMat 6) :
    IsComplexHadamard (scaledRelative U V) ↔ IsUnbiased U V := by
  constructor
  · exact scaledRelative_isUnbiased_of_isComplexHadamard U V
  · exact scaledRelative_isComplexHadamard U V

/-- The normalized quartet reduction now supplies six standard complex Hadamard transition
matrices. This is the exact formal interface needed before applying Hadamard-classification
results; it does not say those six transitions can or cannot coexist. -/
theorem four_iff_six_hadamard_transitions :
    HasMUBs 6 4 ↔
      ∃ H K L : UMat 6,
        IsComplexHadamard (scaledRelative 1 H) ∧
        IsComplexHadamard (scaledRelative 1 K) ∧
        IsComplexHadamard (scaledRelative 1 L) ∧
        IsComplexHadamard (scaledRelative H K) ∧
        IsComplexHadamard (scaledRelative H L) ∧
        IsComplexHadamard (scaledRelative K L) := by
  rw [OQP13.four_iff_transition_triple]
  constructor
  · rintro ⟨H, K, L, hH, hK, hL, hHK, hHL, hKL⟩
    exact ⟨H, K, L,
      scaledRelative_isComplexHadamard 1 H hH,
      scaledRelative_isComplexHadamard 1 K hK,
      scaledRelative_isComplexHadamard 1 L hL,
      scaledRelative_isComplexHadamard H K hHK,
      scaledRelative_isComplexHadamard H L hHL,
      scaledRelative_isComplexHadamard K L hKL⟩
  · rintro ⟨H, K, L, hH, hK, hL, hHK, hHL, hKL⟩
    exact ⟨H, K, L,
      scaledRelative_isUnbiased_of_isComplexHadamard 1 H hH,
      scaledRelative_isUnbiased_of_isComplexHadamard 1 K hK,
      scaledRelative_isUnbiased_of_isComplexHadamard 1 L hL,
      scaledRelative_isUnbiased_of_isComplexHadamard H K hHK,
      scaledRelative_isUnbiased_of_isComplexHadamard H L hHL,
      scaledRelative_isUnbiased_of_isComplexHadamard K L hKL⟩

end OQP13HadamardBridge

#print axioms OQP13HadamardBridge.scaledRelative_isComplexHadamard
#print axioms OQP13HadamardBridge.scaledRelative_isComplexHadamard_iff
#print axioms OQP13HadamardBridge.four_iff_six_hadamard_transitions
