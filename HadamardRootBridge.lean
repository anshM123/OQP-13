import SixRootPairing

/-!
Bridge from a normalized 6×6 matrix to the six-root pairing theorem.

The fixed row partition is I = {0,2,4} and Iᶜ = {1,3,5}. We use the
paper's convention μ(I)_r = -1 on I and +1 on Iᶜ. Its amplitude is
`g_H(γ) = Σ_k ∏_r H_{r,k}^{γ_r}` (negative powers mean reciprocals), and
`G_H(γ) = |g_H(γ)|²`, represented by `Complex.normSq`. Since the values
`z_k` below have unit modulus, `g_H(m μ(I)) = star (Σ_k z_k^m)`, so its
G-zero conditions are equivalent to the requested power-sum normSq zeros.

This file assumes only entrywise unit modulus and those two zero conditions;
it does not assert they hold for every MUB Hadamard matrix or prove an upper
bound for dimension six.
-/

namespace OQP13HadamardRootBridge

open OQP13SixRoots

def evenRowProduct (H : Matrix (Fin 6) (Fin 6) ℂ) (k : Fin 6) : ℂ :=
  H 0 k * H 2 k * H 4 k

def oddRowProduct (H : Matrix (Fin 6) (Fin 6) ℂ) (k : Fin 6) : ℂ :=
  H 1 k * H 3 k * H 5 k

noncomputable def rootValue (H : Matrix (Fin 6) (Fin 6) ℂ) (k : Fin 6) : ℂ :=
  evenRowProduct H k / oddRowProduct H k

/-- The paper's sign vector: -1 on {0,2,4} and +1 on {1,3,5}. -/
def muEven (r : Fin 6) : ℤ := if r.val % 2 = 0 then -1 else 1

/-- Signed exponent amplitude at `m μ(I)`. For entrywise phases, this is
exactly the paper's `g_H(m μ(I))`. -/
noncomputable def g (H : Matrix (Fin 6) (Fin 6) ℂ) (m : ℕ) : ℂ :=
  ∑ k : Fin 6, (rootValue H k)⁻¹ ^ m

/-- `G_H(m μ(I)) = |g_H(m μ(I))|²`, represented as squared complex norm. -/
noncomputable def G (H : Matrix (Fin 6) (Fin 6) ℂ) (m : ℕ) : ℝ :=
  Complex.normSq (g H m)

private lemma product_unit {H : Matrix (Fin 6) (Fin 6) ℂ}
    (hH : ∀ r k, Complex.normSq (H r k) = 1) (k : Fin 6) :
    Complex.normSq (evenRowProduct H k) = 1 ∧
      Complex.normSq (oddRowProduct H k) = 1 := by
  constructor <;> simp [evenRowProduct, oddRowProduct, Complex.normSq_mul, hH]

theorem rootValue_unit {H : Matrix (Fin 6) (Fin 6) ℂ}
    (hH : ∀ r k, Complex.normSq (H r k) = 1) :
    ∀ k, Complex.normSq (rootValue H k) = 1 := by
  intro k
  rcases product_unit hH k with ⟨he, ho⟩
  simp [rootValue, he, ho]

private lemma unit_value_inv_eq_star {H : Matrix (Fin 6) (Fin 6) ℂ}
    (hH : ∀ r k, Complex.normSq (H r k) = 1) (k : Fin 6) :
    (rootValue H k)⁻¹ = star (rootValue H k) := by
  have hu := rootValue_unit hH k
  have hn : rootValue H k ≠ 0 := by
    intro hz
    rw [hz] at hu
    norm_num at hu
  have hm := Complex.mul_conj (rootValue H k)
  rw [hu] at hm
  norm_num at hm
  have hstar : star (rootValue H k) * rootValue H k = 1 := by
    simpa [Complex.star_def, mul_comm] using hm
  calc
    (rootValue H k)⁻¹ = (rootValue H k)⁻¹ * 1 := by simp
    _ = (rootValue H k)⁻¹ * (star (rootValue H k) * rootValue H k) := by rw [hstar]
    _ = ((rootValue H k)⁻¹ * rootValue H k) * star (rootValue H k) := by ring
    _ = star (rootValue H k) := by simp [hn]

private lemma g_eq_star_powerSum (H : Matrix (Fin 6) (Fin 6) ℂ)
    (hH : ∀ r k, Complex.normSq (H r k) = 1) (m : ℕ) :
    g H m = star (powerSum (rootValue H) m) := by
  unfold g powerSum
  calc
    (∑ k : Fin 6, (rootValue H k)⁻¹ ^ m) =
        ∑ k : Fin 6, (star (rootValue H k)) ^ m := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [unit_value_inv_eq_star hH k]
    _ = star (∑ k : Fin 6, (rootValue H k) ^ m) := by
          calc
            (∑ k : Fin 6, (star (rootValue H k)) ^ m) =
                ∑ k : Fin 6, star ((rootValue H k) ^ m) := by simp
            _ = star (∑ k : Fin 6, (rootValue H k) ^ m) := by
              simpa [Complex.star_def] using
                (map_sum (starRingEnd ℂ)
                  (fun k : Fin 6 => (rootValue H k) ^ m) Finset.univ).symm

/-- `G_H(μ(I)) = 0` iff the first quotient-root power sum has squared norm 0. -/
theorem G_first_iff_root_sum_normSq_zero (H : Matrix (Fin 6) (Fin 6) ℂ)
    (hH : ∀ r k, Complex.normSq (H r k) = 1) :
    G H 1 = 0 ↔ Complex.normSq (powerSum (rootValue H) 1) = 0 := by
  rw [G, g_eq_star_powerSum H hH]
  simp

/-- `G_H(3μ(I)) = 0` iff the third quotient-root power sum has squared norm 0. -/
theorem G_third_iff_root_cube_sum_normSq_zero (H : Matrix (Fin 6) (Fin 6) ℂ)
    (hH : ∀ r k, Complex.normSq (H r k) = 1) :
    G H 3 = 0 ↔ Complex.normSq (powerSum (rootValue H) 3) = 0 := by
  rw [G, g_eq_star_powerSum H hH]
  simp

/-- The two paper-style G-zero conditions imply a multiplicity-preserving
permutation pairing the six column values with their negatives, with no fixed
points. -/
theorem G_conditions_give_opposite_pairing
    (H : Matrix (Fin 6) (Fin 6) ℂ)
    (hH : ∀ r k, Complex.normSq (H r k) = 1)
    (hG1 : G H 1 = 0) (hG3 : G H 3 = 0) :
    ∃ σ : Fin 6 ≃ Fin 6,
      (∀ k, rootValue H (σ k) = -rootValue H k) ∧
      (∀ k, σ k ≠ k) := by
  have h1sq : Complex.normSq (powerSum (rootValue H) 1) = 0 :=
    G_first_iff_root_sum_normSq_zero H hH |>.mp hG1
  have h3sq : Complex.normSq (powerSum (rootValue H) 3) = 0 :=
    G_third_iff_root_cube_sum_normSq_zero H hH |>.mp hG3
  have h1 : powerSum (rootValue H) 1 = 0 := Complex.normSq_eq_zero.mp h1sq
  have h3 : powerSum (rootValue H) 3 = 0 := Complex.normSq_eq_zero.mp h3sq
  exact unit_roots_first_third_sums_pair_without_fixed_points
    (rootValue H) (rootValue_unit hH) h1 h3

end OQP13HadamardRootBridge

#print axioms OQP13HadamardRootBridge.G_conditions_give_opposite_pairing
