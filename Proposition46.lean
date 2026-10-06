import Mathlib

/-!
Formalization of the six-unimodular-number pairing assertion used in
Proposition 4.6 of Matolcsi et al., *Triplets of Mutually Unbiased Bases*.

For three unit complex numbers on each side, equal sum and opposite products
force the multiset on one side to equal the negatives of the other side.
The main theorem below states this as an explicit bijection.
-/

namespace OQP13Proposition46

private lemma unit_star_mul (z : ℂ) (hz : Complex.normSq z = 1) :
    star z * z = 1 := by
  have h := Complex.mul_conj z
  rw [hz] at h
  norm_num at h
  simpa [Complex.star_def, mul_comm] using h

private lemma e2_eq_star_sum_mul_prod (a b c : ℂ)
    (ha : Complex.normSq a = 1) (hb : Complex.normSq b = 1)
    (hc : Complex.normSq c = 1) :
    a * b + b * c + c * a = (star a + star b + star c) * (a * b * c) := by
  have hA : star a * (a * b * c) = b * c := by
    calc
      star a * (a * b * c) = (star a * a) * (b * c) := by ring
      _ = b * c := by rw [unit_star_mul a ha]; ring
  have hB : star b * (a * b * c) = c * a := by
    calc
      star b * (a * b * c) = (star b * b) * (c * a) := by ring
      _ = c * a := by rw [unit_star_mul b hb]; ring
  have hC : star c * (a * b * c) = a * b := by
    calc
      star c * (a * b * c) = (star c * c) * (a * b) := by ring
      _ = a * b := by rw [unit_star_mul c hc]; ring
  rw [add_mul, add_mul]
  rw [hA, hB, hC]
  ring

private lemma cubic_poly_eq_of_coeffs (a b c d e f : ℂ)
    (hsum : a + b + c = -d + -e + -f)
    (hprod : a * b * c = (-d) * (-e) * (-f))
    (he2 : a * b + b * c + c * a = (-d) * (-e) + (-e) * (-f) + (-f) * (-d)) :
    (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b) *
        (Polynomial.X - Polynomial.C c) =
      (Polynomial.X - Polynomial.C (-d)) * (Polynomial.X - Polynomial.C (-e)) *
        (Polynomial.X - Polynomial.C (-f)) := by
  have hpoly : ∀ (u v w : ℂ),
      (Polynomial.X - Polynomial.C u) * (Polynomial.X - Polynomial.C v) *
        (Polynomial.X - Polynomial.C w) =
      Polynomial.X ^ 3 - Polynomial.C (u + v + w) * Polynomial.X ^ 2 +
        Polynomial.C (u * v + v * w + w * u) * Polynomial.X -
        Polynomial.C (u * v * w) := by
    intro u v w
    have hh : (Polynomial.X - Polynomial.C u) * (Polynomial.X - Polynomial.C v) *
        (Polynomial.X - Polynomial.C w) =
        Polynomial.X ^ 3 - (Polynomial.C u + Polynomial.C v + Polynomial.C w) *
          Polynomial.X ^ 2 + (Polynomial.C u * Polynomial.C v +
          Polynomial.C v * Polynomial.C w + Polynomial.C w * Polynomial.C u) *
          Polynomial.X - Polynomial.C u * Polynomial.C v * Polynomial.C w := by ring
    simpa [map_add, map_mul] using hh
  rw [hpoly a b c, hpoly (-d) (-e) (-f)]
  rw [hsum, he2, hprod]

def triple (a b c : ℂ) (i : Fin 3) : ℂ :=
  if i.val = 0 then a else if i.val = 1 then b else c

private lemma triple_sum (a b c : ℂ) :
    (∑ i : Fin 3, triple a b c i) = a + b + c := by
  simp [triple, Fin.sum_univ_succ]
  ring

private lemma triple_prod (a b c : ℂ) :
    (∏ i : Fin 3, triple a b c i) = a * b * c := by
  simp [triple, Fin.prod_univ_succ]
  ring

private lemma triple_neg (a b c : ℂ) (i : Fin 3) :
    triple (-a) (-b) (-c) i = -triple a b c i := by
  by_cases h0 : i.val = 0 <;> by_cases h1 : i.val = 1
  all_goals simp [triple, h0, h1]

private lemma even_eval (x : Fin 6 → ℂ) (i : Fin 3) :
    x ⟨2 * i.val, by omega⟩ = triple (x 0) (x 2) (x 4) i := by
  fin_cases i <;> rfl

private lemma odd_eval (x : Fin 6 → ℂ) (i : Fin 3) :
    x ⟨2 * i.val + 1, by omega⟩ = triple (x 1) (x 3) (x 5) i := by
  fin_cases i <;> rfl

private lemma sum_fin_six (x : Fin 6 → ℂ) :
    (∑ i : Fin 6, x i) = x 0 + x 1 + x 2 + x 3 + x 4 + x 5 := by
  simp [Fin.sum_univ_succ]
  ring

private noncomputable def cubicOfTriple (a b c : ℂ) : Polynomial ℂ :=
  ∏ i : Fin 3, (Polynomial.X - Polynomial.C (triple a b c i))

private lemma cubicOfTriple_eq (a b c : ℂ) :
  cubicOfTriple a b c =
      (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C b) *
        (Polynomial.X - Polynomial.C c) := by
  simp [cubicOfTriple, triple, Fin.prod_univ_succ] <;> ring

private lemma roots_cubicOfTriple (a b c : ℂ) :
    (cubicOfTriple a b c).roots =
      (Finset.univ : Finset (Fin 3)).val.map (triple a b c) := by
  simpa [cubicOfTriple, Finset.prod] using
    (Polynomial.roots_multiset_prod_X_sub_C
      ((Finset.univ : Finset (Fin 3)).val.map (triple a b c)))

private lemma triple_map_equiv {L R : Fin 3 → ℂ}
    (hm : (Finset.univ : Finset (Fin 3)).val.map L =
      (Finset.univ : Finset (Fin 3)).val.map R) :
    ∃ σ : Fin 3 ≃ Fin 3, ∀ i, R (σ i) = L i := by
  let s : Multiset (Fin 3) := (Finset.univ : Finset (Fin 3)).val
  have hm' : s.map L = s.map R := by simpa [s] using hm
  let pos := Multiset.mapEquiv s L
  let neg := Multiset.mapEquiv s R
  let e : s ≃ s := pos.trans ((Multiset.cast hm').trans neg.symm)
  have he (x : s) : R (e x) = L x := by
    have htrans : neg (e x) = Multiset.cast hm' (pos x) := by simp [e]
    have hval : (neg (e x) : ℂ) = (Multiset.cast hm' (pos x) : ℂ) :=
      congrArg (fun y : s.map R => (y : ℂ)) htrans
    simpa [neg, pos] using hval
  let eFin : Fin 3 ≃ s :=
    { toFun := fun i => ⟨i, ⟨0, by simp [s]⟩⟩
      invFun := fun i => i.1
      left_inv := fun _ => rfl
      right_inv := fun i => by
        rcases i with ⟨val, idx⟩
        have hidx : idx = ⟨0, by simp [s]⟩ := by
          apply Fin.ext
          have hbound := idx.isLt
          simp [s] at hbound ⊢
          omega
        subst idx
        rfl }
  refine ⟨eFin.trans (e.trans eFin.symm), ?_⟩
  intro i
  change R (eFin.symm (e (eFin i))) = L i
  calc
    R (eFin.symm (e (eFin i))) = R (e (eFin i)).1 := rfl
    _ = L (eFin i).1 := he (eFin i)
    _ = L i := rfl

theorem complementary_triples_pair
    (a b c d e f : ℂ)
    (ha : Complex.normSq a = 1) (hb : Complex.normSq b = 1)
    (hc : Complex.normSq c = 1) (hd : Complex.normSq d = 1)
    (he : Complex.normSq e = 1) (hf : Complex.normSq f = 1)
    (hsum : a + b + c = -(d + e + f))
    (hprod : a * b * c = -(d * e * f)) :
    ∃ σ : Fin 3 ≃ Fin 3,
      ∀ i, triple d e f (σ i) = -triple a b c i := by
  have hsum' : a + b + c = -d + -e + -f := by linear_combination hsum
  have hprod' : a * b * c = (-d) * (-e) * (-f) := by linear_combination hprod
  have hunit_neg (z : ℂ) (hz : Complex.normSq z = 1) :
      Complex.normSq (-z) = 1 := by simpa using hz
  have he2a := e2_eq_star_sum_mul_prod a b c ha hb hc
  have he2b := e2_eq_star_sum_mul_prod (-d) (-e) (-f)
    (hunit_neg d hd) (hunit_neg e he) (hunit_neg f hf)
  have hstar : star a + star b + star c = star (-d) + star (-e) + star (-f) := by
    have hh := congrArg star hsum'
    simpa [map_add, map_neg] using hh
  have he2 : a * b + b * c + c * a = (-d) * (-e) + (-e) * (-f) + (-f) * (-d) := by
    calc
      a * b + b * c + c * a = (star a + star b + star c) * (a * b * c) := he2a
      _ = (star (-d) + star (-e) + star (-f)) * ((-d) * (-e) * (-f)) := by rw [hstar, hprod']
      _ = (-d) * (-e) + (-e) * (-f) + (-f) * (-d) := he2b.symm
  have hpoly := cubic_poly_eq_of_coeffs a b c d e f hsum' hprod' he2
  have hpoly' : cubicOfTriple a b c = cubicOfTriple (-d) (-e) (-f) := by
    rw [cubicOfTriple_eq, cubicOfTriple_eq]
    exact hpoly
  have hroots := congrArg Polynomial.roots hpoly'
  have hm : (Finset.univ : Finset (Fin 3)).val.map (triple a b c) =
      (Finset.univ : Finset (Fin 3)).val.map (triple (-d) (-e) (-f)) := by
    calc
      _ = (cubicOfTriple a b c).roots := (roots_cubicOfTriple a b c).symm
      _ = (cubicOfTriple (-d) (-e) (-f)).roots := hroots
      _ = _ := roots_cubicOfTriple (-d) (-e) (-f)
  obtain ⟨σ, hσ⟩ := triple_map_equiv hm
  refine ⟨σ, ?_⟩
  intro i
  have hi := hσ i
  rw [triple_neg d e f (σ i)] at hi
  simpa using congrArg (fun z : ℂ => -z) hi

theorem proposition_4_6_pairing
    (x : Fin 6 → ℂ)
    (hunit : ∀ i, Complex.normSq (x i) = 1)
    (hsum : (∑ i : Fin 6, x i) = 0)
    (hprod : x 0 * x 2 * x 4 + x 1 * x 3 * x 5 = 0) :
    ∃ σ : Fin 3 ≃ Fin 3,
      ∀ i, x ⟨2 * i.val, by omega⟩ +
        x ⟨2 * (σ i).val + 1, by omega⟩ = 0 := by
  have hsum' : x 0 + x 2 + x 4 = -(x 1 + x 3 + x 5) := by
    rw [sum_fin_six] at hsum
    linear_combination hsum
  have hprod' : x 0 * x 2 * x 4 = -(x 1 * x 3 * x 5) := by
    linear_combination hprod
  obtain ⟨σ, hσ⟩ := complementary_triples_pair
    (x 0) (x 2) (x 4) (x 1) (x 3) (x 5)
    (hunit 0) (hunit 2) (hunit 4) (hunit 1) (hunit 3) (hunit 5)
    hsum' hprod'
  refine ⟨σ, ?_⟩
  intro i
  have hi := hσ i
  rw [even_eval x i, odd_eval x (σ i)]
  simpa [add_comm] using (eq_neg_iff_add_eq_zero.mp hi)

end OQP13Proposition46
