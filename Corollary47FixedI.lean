import Proposition46

/-!
Fixed-index-set formalization of the corrected Corollary 4.7 argument from
Matolcsi et al., *Triplets of Mutually Unbiased Bases*.  The index set is
`{0,2,4}` in Lean's zero-based indexing.

The extra orthogonality premise is explicit: it supplies the zero-sum
assumption needed by Proposition 4.6.  The theorem does not derive that premise
from the two product identities alone.
-/

namespace OQP13Corollary47FixedI

def evenProduct (z : Fin 6 → ℂ) : ℂ := z 0 * z 2 * z 4
def oddProduct (z : Fin 6 → ℂ) : ℂ := z 1 * z 3 * z 5

/-- The `μ({0,2,4})` product, written as odd-coordinate product divided by
the even-coordinate product. For unimodular entries this is exactly the
product with exponent `-1` on `{0,2,4}` and `+1` on its complement. -/
noncomputable def muEvenProduct (z : Fin 6 → ℂ) : ℂ :=
  oddProduct z / evenProduct z

private lemma coord_ne_zero {z : Fin 6 → ℂ}
    (hz : ∀ i, Complex.normSq (z i) = 1) (i : Fin 6) : z i ≠ 0 := by
  intro h
  have hi := hz i
  rw [h] at hi
  norm_num at hi

/-- Fixed-index-set version of Corollary 4.7. The quotient vector is unimodular,
has zero sum by the orthogonality hypothesis, and its even/odd triple products
are opposite by the two `μ({0,2,4})` assumptions. Proposition 4.6 then gives an
explicit bijection pairing each even coordinate with an opposite odd coordinate. -/
theorem fixed_even_odd_pairing
    (a b : Fin 6 → ℂ)
    (ha : ∀ i, Complex.normSq (a i) = 1)
    (hb : ∀ i, Complex.normSq (b i) = 1)
    (horth : ∑ i : Fin 6, a i / b i = 0)
    (lam : ℂ) (hlam : Complex.normSq lam = 1)
    (haμ : muEvenProduct a = lam)
    (hbμ : muEvenProduct b = -lam) :
    ∃ σ : Fin 3 ≃ Fin 3,
      ∀ i, (a ⟨2 * i.val, by omega⟩ / b ⟨2 * i.val, by omega⟩) +
        (a ⟨2 * (σ i).val + 1, by omega⟩ /
          b ⟨2 * (σ i).val + 1, by omega⟩) = 0 := by
  let x : Fin 6 → ℂ := fun i => a i / b i
  have hxunit : ∀ i, Complex.normSq (x i) = 1 := by
    intro i
    simp only [x, Complex.normSq_div, ha i, hb i]
    norm_num
  have hlamne : lam ≠ 0 := by
    intro h
    rw [h] at hlam
    norm_num at hlam
  have hEvenA : evenProduct a ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (coord_ne_zero ha 0) (coord_ne_zero ha 2))
      (coord_ne_zero ha 4)
  have hOddB : oddProduct b ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (coord_ne_zero hb 1) (coord_ne_zero hb 3))
      (coord_ne_zero hb 5)
  have hprod : evenProduct x + oddProduct x = 0 := by
    have hratio : oddProduct x / evenProduct x = -1 := by
      have haμ' : oddProduct a = lam * evenProduct a :=
        (div_eq_iff hEvenA).mp haμ
      have hEvenB : evenProduct b ≠ 0 := by
        exact mul_ne_zero (mul_ne_zero (coord_ne_zero hb 0) (coord_ne_zero hb 2))
          (coord_ne_zero hb 4)
      have hbμ' : oddProduct b = -lam * evenProduct b :=
        (div_eq_iff hEvenB).mp hbμ
      dsimp [x, oddProduct, evenProduct]
      field_simp [coord_ne_zero ha 0, coord_ne_zero ha 2, coord_ne_zero ha 4,
        coord_ne_zero hb 0, coord_ne_zero hb 2, coord_ne_zero hb 4,
        coord_ne_zero ha 1, coord_ne_zero ha 3, coord_ne_zero ha 5,
        coord_ne_zero hb 1, coord_ne_zero hb 3, coord_ne_zero hb 5]
      simp only [evenProduct, oddProduct] at haμ' hbμ' ⊢
      linear_combination (b 0 * b 2 * b 4) * haμ' +
        (a 0 * a 2 * a 4) * hbμ'
    have hEvenX : evenProduct x ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero
        (div_ne_zero (coord_ne_zero ha 0) (coord_ne_zero hb 0))
        (div_ne_zero (coord_ne_zero ha 2) (coord_ne_zero hb 2)))
        (div_ne_zero (coord_ne_zero ha 4) (coord_ne_zero hb 4))
    have := (div_eq_iff hEvenX).mp hratio
    linear_combination this
  have hsum : (∑ i : Fin 6, x i) = 0 := by
    simpa [x] using horth
  obtain ⟨σ, hσ⟩ := OQP13Proposition46.proposition_4_6_pairing
    x hxunit hsum hprod
  refine ⟨σ, ?_⟩
  intro i
  simpa [x] using hσ i

end OQP13Corollary47FixedI

#print axioms OQP13Corollary47FixedI.fixed_even_odd_pairing
