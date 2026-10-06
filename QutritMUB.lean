import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-! Explicit Fourier and quadratic-chirp matrices in dimension three, with their
Gram identities and cross-overlap norms. -/

namespace QutritMUB

noncomputable def omega : ℂ := (-1 + (Real.sqrt 3 : ℝ) * Complex.I) / 2

lemma sqrt3_sq : (Real.sqrt 3 : ℝ) ^ 2 = 3 := by
  rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]

lemma omega_sq_add : omega ^ 2 + omega + 1 = 0 := by
  rw [omega]
  have hs : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by exact_mod_cast sqrt3_sq
  field_simp
  ring_nf
  simp only [Complex.I_sq] at *
  rw [hs]
  ring

lemma omega_sq_eq : omega ^ 2 = -omega - 1 := by
  linear_combination omega_sq_add

lemma star_omega : star omega = omega ^ 2 := by
  have hconj : star omega = -omega - 1 := by
    rw [omega]
    simp
    field_simp
    ring
  calc
    star omega = -omega - 1 := hconj
    _ = omega ^ 2 := omega_sq_eq.symm

lemma omega_cube : omega ^ 3 = 1 := by
  calc
    omega ^ 3 = omega * omega ^ 2 := by ring
    _ = omega * (-omega - 1) := by rw [omega_sq_eq]
    _ = 1 := by linear_combination -omega_sq_add

lemma omega_normSq : Complex.normSq omega = 1 := by
  apply_mod_cast
  calc
    (Complex.normSq omega : ℂ) = (starRingEnd ℂ) omega * omega := by
      rw [Complex.normSq_eq_conj_mul_self]
    _ = star omega * omega := by rfl
    _ = omega ^ 2 * omega := by rw [star_omega]
    _ = 1 := by rw [← pow_succ, omega_cube]

/-- The order-three Fourier matrix, with rows and columns indexed by `Fin 3`. -/
noncomputable def fourier (i j : Fin 3) : ℂ :=
  match i.val, j.val with
  | 0, _ => 1
  | 1, 0 => 1
  | 1, 1 => omega
  | 1, _ => omega ^ 2
  | 2, 0 => 1
  | 2, 1 => omega ^ 2
  | _, _ => omega

/-- A quadratic-chirp basis, whose columns are unbiased to the Fourier basis. -/
noncomputable def chirp (i j : Fin 3) : ℂ :=
  match i.val, j.val with
  | 0, _ => 1
  | 1, 0 => omega
  | 1, 1 => omega ^ 2
  | 1, _ => 1
  | 2, 0 => omega
  | 2, 1 => 1
  | _, _ => omega ^ 2

lemma omega_conj_sq : star (omega ^ 2) = omega := by
  calc
    star (omega ^ 2) = (star omega) ^ 2 := by simp
    _ = (omega ^ 2) ^ 2 := by rw [star_omega]
    _ = omega := by
      calc
        (omega ^ 2) ^ 2 = omega * omega ^ 3 := by ring
        _ = omega := by rw [omega_cube, mul_one]

lemma omega_sq_normSq : Complex.normSq (omega ^ 2) = 1 := by
  apply_mod_cast
  calc
    (Complex.normSq (omega ^ 2) : ℂ) = star (omega ^ 2) * omega ^ 2 := by
      rw [Complex.normSq_eq_conj_mul_self]
      rfl
    _ = omega * omega ^ 2 := by rw [omega_conj_sq]
    _ = 1 := by
      calc
        omega * omega ^ 2 = omega ^ 3 := by ring
        _ = 1 := omega_cube

theorem fourier_entry_normSq (i j : Fin 3) :
    Complex.normSq (fourier i j) = 1 := by
  fin_cases i <;> fin_cases j <;>
    simp [fourier, omega_normSq, omega_sq_normSq]

theorem chirp_entry_normSq (i j : Fin 3) :
    Complex.normSq (chirp i j) = 1 := by
  fin_cases i <;> fin_cases j <;>
    simp [chirp, omega_normSq, omega_sq_normSq]

lemma sum_fin3 (f : Fin 3 → ℂ) :
    (∑ i : Fin 3, f i) = f 0 + f 1 + f 2 := by
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  simp
  ring

lemma omega_four : omega ^ 4 = omega := by
  calc
    omega ^ 4 = omega * omega ^ 3 := by ring
    _ = omega := by rw [omega_cube]; ring

lemma omega_five : omega ^ 5 = omega ^ 2 := by
  calc
    omega ^ 5 = omega ^ 2 * omega ^ 3 := by rw [← pow_add]
    _ = omega ^ 2 := by rw [omega_cube, mul_one]

lemma omega_six : omega ^ 6 = 1 := by
  calc
    omega ^ 6 = omega ^ 3 * omega ^ 3 := by rw [← pow_add]
    _ = 1 := by rw [omega_cube]; norm_num

section GramProofs

attribute [local simp] star_omega omega_conj_sq omega_cube omega_four omega_five omega_six omega_sq_eq

/-- The columns of the Fourier matrix are orthogonal, with squared norm 3. -/
theorem fourier_gram (i j : Fin 3) :
    (∑ k : Fin 3, star (fourier k i) * fourier k j) = if i = j then 3 else 0 := by
  rw [sum_fin3]
  fin_cases i <;> fin_cases j
  all_goals simp [fourier]
  all_goals try ring
  all_goals try linear_combination -2 * omega_sq_add
  all_goals try linear_combination 2 * omega_sq_add

/-- The chirp columns are also orthogonal, with squared norm 3. -/
theorem chirp_gram (i j : Fin 3) :
    (∑ k : Fin 3, star (chirp k i) * chirp k j) = if i = j then 3 else 0 := by
  rw [sum_fin3]
  fin_cases i <;> fin_cases j
  all_goals simp [chirp]
  all_goals try ring
  all_goals try linear_combination -2 * omega_sq_add
  all_goals try linear_combination -omega_sq_add
  all_goals try linear_combination omega_sq_add

end GramProofs

lemma normSq_eq_three_of_star_mul {z : ℂ} (h : star z * z = 3) :
    Complex.normSq z = 3 := by
  have hC : (Complex.normSq z : ℂ) = 3 := by
    calc
      (Complex.normSq z : ℂ) = (starRingEnd ℂ) z * z := by
        rw [Complex.normSq_eq_conj_mul_self]
      _ = star z * z := by rfl
      _ = 3 := h
  exact_mod_cast hC

lemma normSq_one_add_two_omega : Complex.normSq (1 + omega * 2) = 3 := by
  apply normSq_eq_three_of_star_mul
  calc
    star (1 + omega * 2) * (1 + omega * 2) =
        (1 + omega ^ 2 * 2) * (1 + omega * 2) := by simp [star_omega]
    _ = 1 + omega * 2 + omega ^ 2 * 2 + omega ^ 3 * 4 := by ring
    _ = 5 + omega * 2 + omega ^ 2 * 2 := by rw [omega_cube]; ring
    _ = 3 := by linear_combination 2 * omega_sq_add

lemma normSq_two_add_omega_sq : Complex.normSq (2 + omega ^ 2) = 3 := by
  apply normSq_eq_three_of_star_mul
  calc
    star (2 + omega ^ 2) * (2 + omega ^ 2) =
        (2 + omega) * (2 + omega ^ 2) := by simp only [star_add, star_ofNat, omega_conj_sq]
    _ = 4 + omega * 2 + omega ^ 2 * 2 + omega ^ 3 := by ring
    _ = 5 + omega * 2 + omega ^ 2 * 2 := by rw [omega_cube]; ring
    _ = 3 := by linear_combination 2 * omega_sq_add

section CrossOverlapProof

attribute [local simp] star_omega omega_conj_sq omega_cube omega_four omega_five omega_six

lemma fourier_chirp_sum_form (i j : Fin 3) :
    (∑ k : Fin 3, star (fourier k i) * chirp k j) =
      1 + omega * 2 ∨ (∑ k : Fin 3, star (fourier k i) * chirp k j) = 2 + omega ^ 2 := by
  rw [sum_fin3]
  fin_cases i <;> fin_cases j
  · left
    simp [fourier, chirp]
    ; ring
  · right
    simp [fourier, chirp]
    ; ring
  · right
    simp [fourier, chirp]
    ; norm_num
  · right
    simp [fourier, chirp]
    rw [show omega ^ 2 * omega = omega ^ 3 by ring,
      show (omega ^ 2) ^ 2 * omega = omega ^ 5 by ring,
      omega_cube, omega_five]
    ring
  · left
    simp [fourier, chirp]
    rw [show omega ^ 2 * omega ^ 2 = omega ^ 4 by ring,
      show (omega ^ 2) ^ 2 = omega ^ 4 by ring, omega_four]
    ring
  · right
    simp [fourier, chirp]
    rw [show (omega ^ 2) ^ 2 * omega ^ 2 = omega ^ 6 by ring, omega_six]
    ring
  · right
    simp [fourier, chirp]
    rw [show (omega ^ 2) ^ 2 * omega = omega ^ 5 by ring,
      show omega ^ 2 * omega = omega ^ 3 by ring,
      omega_five, omega_cube]
    ring
  · right
    simp [fourier, chirp]
    rw [show (omega ^ 2) ^ 2 * omega ^ 2 = omega ^ 6 by ring, omega_six]
    norm_num
  · left
    simp [fourier, chirp]
    rw [show (omega ^ 2) ^ 2 = omega ^ 4 by ring,
      show omega ^ 2 * omega ^ 2 = omega ^ 4 by ring, omega_four]
    ring

/-- Every entry of the Fourier-to-chirp transition has squared modulus 3. -/
theorem fourier_chirp_flat (i j : Fin 3) :
    Complex.normSq (∑ k : Fin 3, star (fourier k i) * chirp k j) = 3 := by
  rcases fourier_chirp_sum_form i j with h | h
  · rw [h]
    exact normSq_one_add_two_omega
  · rw [h]
    exact normSq_two_add_omega_sq

end CrossOverlapProof
lemma test_relation : 1 + omega + omega ^ 2 = 0 := by
  linear_combination omega_sq_add

end QutritMUB
