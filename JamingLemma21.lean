import QutritMUB

/-! Exact Lean formalization of Jaming et al., Lemma 2.1 (arXiv:0902.0882v2).

The lemma reduces three squared-modulus constraints for an order-three Fourier block to
one energy equation and one directed cyclic cross-term equation. -/

namespace QutritMUB.JamingLemma21

private lemma normSq_coe (z : ℂ) : (Complex.normSq z : ℂ) = star z * z := by
  calc
    (Complex.normSq z : ℂ) = (starRingEnd ℂ) z * z := by
      rw [Complex.normSq_eq_conj_mul_self]
    _ = star z * z := by rfl

noncomputable def f0 (a b c : ℂ) : ℂ := a + b + c
noncomputable def f1 (a b c : ℂ) : ℂ := a + omega*b + omega^2*c
noncomputable def f2 (a b c : ℂ) : ℂ := a + omega^2*b + omega*c
noncomputable def energy (a b c : ℂ) : ℂ :=
  starRingEnd ℂ a*a + starRingEnd ℂ b*b + starRingEnd ℂ c*c
noncomputable def cyc (a b c : ℂ) : ℂ :=
  a*starRingEnd ℂ b + b*starRingEnd ℂ c + c*starRingEnd ℂ a

attribute [local simp] star_omega omega_conj_sq omega_cube omega_four omega_five omega_six

private lemma expansions (a b c : ℂ) :
    (Complex.normSq (f0 a b c) : ℂ) = energy a b c + cyc a b c + star (cyc a b c) ∧
    (Complex.normSq (f1 a b c) : ℂ) = energy a b c + omega * star (cyc a b c) + omega^2 * cyc a b c ∧
    (Complex.normSq (f2 a b c) : ℂ) = energy a b c + omega^2 * star (cyc a b c) + omega * cyc a b c := by
  constructor
  · rw [normSq_coe]
    simp [f0, energy, cyc, star_add, star_mul]
    ring
  constructor
  · rw [normSq_coe]
    simp [f1, energy, cyc, star_add, star_mul, star_omega]
    simp only [starRingEnd_apply]
    ring_nf
    simp only [omega_cube, omega_four, omega_five, omega_six]
    ring
  · rw [normSq_coe]
    simp [f2, energy, cyc, star_add, star_mul, star_omega]
    simp only [starRingEnd_apply]
    ring_nf
    simp only [omega_cube, omega_four, omega_five, omega_six]
    ring

private lemma omega_sq_ne_omega : omega^2 - omega ≠ 0 := by
  intro h
  have h' : omega^2 = omega := sub_eq_zero.mp h
  have hrel : 2 * omega = -1 := by
    rw [omega_sq_eq] at h'
    linear_combination -h'
  have hsq := congrArg Complex.normSq hrel
  rw [Complex.normSq_mul, omega_normSq] at hsq
  norm_num at hsq

/-- Jaming et al., Lemma 2.1: the three unnormalised order-three Fourier
coefficients have squared modulus 6 exactly when the block energy is 6 and
its directed cyclic cross-term vanishes. -/
theorem jaming_lemma_2_1 (a b c : ℂ) :
    (Complex.normSq (f0 a b c) = 6 ∧
     Complex.normSq (f1 a b c) = 6 ∧
     Complex.normSq (f2 a b c) = 6) ↔
    (energy a b c = 6 ∧ cyc a b c = 0) := by
  constructor
  · rintro ⟨h0, h1, h2⟩
    have h0c : (Complex.normSq (f0 a b c) : ℂ) = 6 := by exact_mod_cast h0
    have h1c : (Complex.normSq (f1 a b c) : ℂ) = 6 := by exact_mod_cast h1
    have h2c : (Complex.normSq (f2 a b c) : ℂ) = 6 := by exact_mod_cast h2
    rcases expansions a b c with ⟨e0, e1, e2⟩
    rw [e0] at h0c
    rw [e1] at h1c
    rw [e2] at h2c
    have h1c' := h1c
    have h2c' := h2c
    rw [omega_sq_eq] at h1c' h2c'
    have hsum : 3 * energy a b c = 18 := by
      linear_combination h0c + h1c' + h2c'
    have hE : energy a b c = 6 := by
      calc
        energy a b c = (3 * energy a b c) / 3 := by ring
        _ = 18 / 3 := by rw [hsum]
        _ = 6 := by norm_num
    have hCplus : cyc a b c + star (cyc a b c) = 0 := by
      rw [hE] at h0c
      linear_combination h0c
    have hFourier1 : omega * star (cyc a b c) + omega^2 * cyc a b c = 0 := by
      rw [hE] at h1c
      linear_combination h1c
    have hFourier1' := hFourier1
    rw [omega_sq_eq] at hFourier1'
    have hFactor : (omega^2 - omega) * cyc a b c = 0 := by
      calc
        (omega^2 - omega) * cyc a b c =
            omega * star (cyc a b c) + omega^2 * cyc a b c := by
              rw [show star (cyc a b c) = -cyc a b c by linear_combination hCplus]
              ring
        _ = 0 := hFourier1
    rcases mul_eq_zero.mp hFactor with hω | hC
    · exact False.elim (omega_sq_ne_omega hω)
    · exact ⟨hE, hC⟩
  · rintro ⟨hE, hC⟩
    rcases expansions a b c with ⟨e0, e1, e2⟩
    constructor
    · have : (Complex.normSq (f0 a b c) : ℂ) = 6 := by
        rw [e0, hE, hC]
        simp
      exact_mod_cast this
    constructor
    · have : (Complex.normSq (f1 a b c) : ℂ) = 6 := by
        rw [e1, hE, hC]
        simp
      exact_mod_cast this
    · have : (Complex.normSq (f2 a b c) : ℂ) = 6 := by
        rw [e2, hE, hC]
        simp
      exact_mod_cast this

#print axioms jaming_lemma_2_1

end QutritMUB.JamingLemma21
