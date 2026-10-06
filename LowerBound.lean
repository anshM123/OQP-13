import FormalConjectures.OpenQuantumProblems.«13»

/-! Algebraic lemmas for a primitive cube root of unity.

These facts are ingredients for a possible qutrit-based construction. This
file does not construct three mutually unbiased bases in dimension six. -/

namespace OQP13

noncomputable def cubeRoot : ℂ := ⟨-(1 / 2 : ℝ), Real.sqrt 3 / 2⟩

lemma sqrt_three_sq : (Real.sqrt 3) ^ 2 = 3 := by
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

lemma sqrt_three_half_sq : Real.sqrt 3 / 2 * (Real.sqrt 3 / 2) = 3 / 4 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  nlinarith

lemma cubeRoot_relation : cubeRoot ^ 2 + cubeRoot + 1 = 0 := by
  apply Complex.ext_iff.mpr
  constructor
  · simp [cubeRoot, pow_two, Complex.mul_re]
    nlinarith [sqrt_three_half_sq]
  · simp [cubeRoot, pow_two, Complex.mul_im]
    ring

lemma cubeRoot_star : star cubeRoot = cubeRoot ^ 2 := by
  apply Complex.ext_iff.mpr
  constructor
  · simp [cubeRoot, pow_two, Complex.mul_re]
    nlinarith [sqrt_three_half_sq]
  · simp [cubeRoot, pow_two, Complex.mul_im]
    ring

lemma cubeRoot_pow_three : cubeRoot ^ 3 = 1 := by
  have hfactor : cubeRoot ^ 3 - 1 =
      (cubeRoot - 1) * (cubeRoot ^ 2 + cubeRoot + 1) := by ring
  rw [cubeRoot_relation] at hfactor
  have h : cubeRoot ^ 3 - 1 = 0 := by simpa using hfactor
  exact sub_eq_zero.mp h

end OQP13
