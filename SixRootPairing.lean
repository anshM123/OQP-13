import Mathlib

/-!
Standalone Lean verification of the six-root Newton criterion. This proves
coefficient-level evenness and that each indexed root has an opposite among
the indexed roots. It also proves the exact equivalence between vanishing of
the first, third, and fifth power sums and a permutation of the six indices
that pairs each value with its negative; the intermediate multiset equality
retains multiplicities. Under unit modulus, no index is fixed by this
permutation. It does not prove the permutation is an involution.
-/

open Finset
open MvPolynomial

namespace OQP13SixRoots

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

lemma esymmVal_eq_multiset (z : Fin 6 → ℂ) (k : ℕ) :
    esymmVal z k = (Finset.univ.val.map z).esymm k := by
  rw [esymmVal, MvPolynomial.aeval_esymm_eq_multiset_esymm]

lemma esymm_three_eq_of_power_sums
    (z : Fin 6 → ℂ)
    (h1 : powerSum z 1 = 0)
    (h3 : powerSum z 3 = 0) :
    esymmVal z 3 = 0 := by
  have hn := MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin 6) ℂ 3 (by omega)
  have heval := congrArg (MvPolynomial.aeval z) hn
  have hfilter :
      {a ∈ HasAntidiagonal.antidiagonal 3 | a.1 ∈ Set.Ioo 0 3} =
        {(1, 2), (2, 1)} := by
    ext a
    rcases a with ⟨a, b⟩
    simp [HasAntidiagonal.mem_antidiagonal, Set.mem_Ioo]
    omega
  rw [hfilter] at heval
  simp [MvPolynomial.psum] at heval
  rw [show (∑ i : Fin 6, z i) = 0 by simpa [powerSum] using h1] at heval
  rw [show (∑ i : Fin 6, z i ^ 3) = 0 by simpa [powerSum] using h3] at heval
  norm_num at heval
  exact heval

lemma esymm_five_eq_of_power_sums
    (z : Fin 6 → ℂ)
    (h1 : powerSum z 1 = 0)
    (h3 : powerSum z 3 = 0)
    (h5 : powerSum z 5 = 0) :
    esymmVal z 5 = 0 := by
  have he1 : esymmVal z 1 = 0 := by
    rw [esymm_one_eq_sum]
    exact h1
  have he3 : esymmVal z 3 = 0 := esymm_three_eq_of_power_sums z h1 h3
  have hn := MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin 6) ℂ 5 (by omega)
  have heval := congrArg (MvPolynomial.aeval z) hn
  have hfilter :
      {a ∈ HasAntidiagonal.antidiagonal 5 | a.1 ∈ Set.Ioo 0 5} =
        {(1, 4), (2, 3), (3, 2), (4, 1)} := by
    ext a
    rcases a with ⟨a, b⟩
    simp [HasAntidiagonal.mem_antidiagonal, Set.mem_Ioo]
    omega
  rw [hfilter] at heval
  simp [MvPolynomial.psum] at heval
  rw [show (∑ i : Fin 6, z i) = 0 by simpa [powerSum] using h1] at heval
  rw [show (∑ i : Fin 6, z i ^ 3) = 0 by simpa [powerSum] using h3] at heval
  have he3' : MvPolynomial.aeval z (MvPolynomial.esymm (Fin 6) ℂ 3) = 0 := he3
  have he3eval : MvPolynomial.eval z (MvPolynomial.esymm (Fin 6) ℂ 3) = 0 := by
    simpa using he3'
  rw [he3eval] at heval
  rw [show (∑ i : Fin 6, z i ^ 5) = 0 by simpa [powerSum] using h5] at heval
  norm_num at heval
  change MvPolynomial.eval z (MvPolynomial.esymm (Fin 6) ℂ 5) = 0
  exact heval

/-! For six unit roots, the fifth elementary symmetric coefficient is the
product of all roots times the conjugate of their sum. -/

lemma powersetCard_five_eq_univ_erase :
    Finset.powersetCard 5 (Finset.univ : Finset (Fin 6)) =
      Finset.univ.image (fun i : Fin 6 => Finset.univ.erase i) := by
  ext s
  simp only [Finset.mem_powersetCard, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro hs
    have hc : sᶜ.card = 1 := by rw [Finset.card_compl]; simp [hs]
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
    refine ⟨i, ?_⟩
    ext x
    have hx' : x ∈ sᶜ ↔ x = i := by rw [hi]; simp
    have hx : x ∉ s ↔ x = i := by simpa [Finset.mem_compl] using hx'
    simpa using (not_congr hx).symm
  · rintro ⟨i, rfl⟩
    simp [Finset.card_erase_of_mem]

lemma prod_erase_eq_prod_star (z : Fin 6 → ℂ)
    (hunit : ∀ i, Complex.normSq (z i) = 1) (i : Fin 6) :
    (∏ j ∈ (Finset.univ.erase i), z j) =
      (∏ j : Fin 6, z j) * star (z i) := by
  have hi : i ∈ (Finset.univ : Finset (Fin 6)) := Finset.mem_univ i
  have hmul : z i * star (z i) = 1 := by
    have h0 := Complex.mul_conj (z i)
    rw [hunit i] at h0
    norm_num at h0
    simpa [Complex.star_def] using h0
  calc
    (∏ j ∈ (Finset.univ.erase i), z j) =
        (∏ j ∈ (Finset.univ.erase i), z j) * 1 := by simp
    _ = (∏ j ∈ (Finset.univ.erase i), z j) * (z i * star (z i)) := by rw [hmul]
    _ = ((∏ j ∈ (Finset.univ.erase i), z j) * z i) * star (z i) := by ring
    _ = (∏ j : Fin 6, z j) * star (z i) := by
      rw [Finset.prod_erase_mul _ _ hi]

lemma esymm_five_eq_prod_star_sum (z : Fin 6 → ℂ)
    (hunit : ∀ i, Complex.normSq (z i) = 1) :
    esymmVal z 5 = (∏ i : Fin 6, z i) * star (∑ i : Fin 6, z i) := by
  rw [esymmVal, MvPolynomial.aeval_esymm_eq_multiset_esymm,
    Finset.esymm_map_val, powersetCard_five_eq_univ_erase]
  have hinj : Set.InjOn (fun i : Fin 6 => Finset.univ.erase i)
      ↑(Finset.univ : Finset (Fin 6)) := by
    intro i hi j hj hij
    have hx0 : i ∉ Finset.univ.erase i := by simp
    have hij' : Finset.univ.erase i = Finset.univ.erase j := hij
    rw [hij'] at hx0
    simpa using hx0
  rw [Finset.sum_image hinj]
  simp_rw [prod_erase_eq_prod_star z hunit]
  rw [← Finset.mul_sum]
  congr 1
  simpa [Complex.star_def] using (map_sum (starRingEnd ℂ) z Finset.univ).symm

lemma powerSum_five_eq_zero_of_unit_first_third (z : Fin 6 → ℂ)
    (hunit : ∀ i, Complex.normSq (z i) = 1)
    (h1 : powerSum z 1 = 0) (h3 : powerSum z 3 = 0) :
    powerSum z 5 = 0 := by
  have he1 : esymmVal z 1 = 0 := by rw [esymm_one_eq_sum]; exact h1
  have he3 : esymmVal z 3 = 0 := esymm_three_eq_of_power_sums z h1 h3
  have he5 : esymmVal z 5 = 0 := by
    rw [esymm_five_eq_prod_star_sum z hunit]
    simp [show (∑ i : Fin 6, z i) = 0 by simpa [powerSum] using h1]
  have hn := MvPolynomial.psum_eq_mul_esymm_sub_sum (Fin 6) ℂ 5 (by omega)
  have heval := congrArg (MvPolynomial.aeval z) hn
  have hfilter :
      {a ∈ HasAntidiagonal.antidiagonal 5 | a.1 ∈ Set.Ioo 0 5} =
        {(1, 4), (2, 3), (3, 2), (4, 1)} := by
    ext a
    rcases a with ⟨a, b⟩
    simp [HasAntidiagonal.mem_antidiagonal, Set.mem_Ioo]
    omega
  rw [hfilter] at heval
  simp [MvPolynomial.psum] at heval
  rw [show (∑ i : Fin 6, z i) = 0 by simpa [powerSum] using h1] at heval
  rw [show (∑ i : Fin 6, z i ^ 3) = 0 by simpa [powerSum] using h3] at heval
  have he3' : MvPolynomial.aeval z (MvPolynomial.esymm (Fin 6) ℂ 3) = 0 := he3
  have he3eval : MvPolynomial.eval z (MvPolynomial.esymm (Fin 6) ℂ 3) = 0 := by
    simpa using he3'
  rw [he3eval] at heval
  have he5' : MvPolynomial.aeval z (MvPolynomial.esymm (Fin 6) ℂ 5) = 0 := he5
  have he5eval : MvPolynomial.eval z (MvPolynomial.esymm (Fin 6) ℂ 5) = 0 := by
    simpa using he5'
  rw [he5eval] at heval
  norm_num at heval
  simpa [powerSum] using heval

noncomputable def rootPolynomial (z : Fin 6 → ℂ) : Polynomial ℂ :=
  ∏ i : Fin 6, (Polynomial.X - Polynomial.C (z i))

lemma roots_even_coefficients (z : Fin 6 → ℂ)
    (h1 : powerSum z 1 = 0) (h3 : powerSum z 3 = 0)
    (h5 : powerSum z 5 = 0) :
    ∀ k : ℕ, k < 6 → k % 2 = 1 → (rootPolynomial z).coeff k = 0 := by
  intro k hk hkodd
  have he1 : esymmVal z 1 = 0 := by rw [esymm_one_eq_sum]; exact h1
  have he3 : esymmVal z 3 = 0 := esymm_three_eq_of_power_sums z h1 h3
  have he5 : esymmVal z 5 = 0 := esymm_five_eq_of_power_sums z h1 h3 h5
  have hcoeff : (rootPolynomial z).coeff k =
      (-1 : ℂ) ^ (6-k) * (Finset.univ.val.map z).esymm (6-k) := by
    simpa [rootPolynomial, Finset.prod] using
      (Multiset.prod_X_sub_C_coeff (Finset.univ.val.map z) (by
        simpa using Nat.le_of_lt hk))
  -- The coefficient is the signed elementary symmetric polynomial of degree `6-k`.
  have heval :
      (Finset.univ.val.map z).esymm (6-k) = esymmVal z (6-k) := by
    symm
    exact esymmVal_eq_multiset z (6-k)
  rw [heval] at hcoeff
  have hdegree : 6-k = 1 ∨ 6-k = 3 ∨ 6-k = 5 := by omega
  rcases hdegree with h | h | h
  · rw [h, he1] at hcoeff
    simpa using hcoeff
  · rw [h, he3] at hcoeff
    simpa using hcoeff
  · rw [h, he5] at hcoeff
    simpa using hcoeff

def IsEvenPoly (p : Polynomial ℂ) : Prop := ∀ x : ℂ, p.eval (-x) = p.eval x

lemma rootPolynomial_isEven (z : Fin 6 → ℂ)
    (h1 : powerSum z 1 = 0) (h3 : powerSum z 3 = 0)
    (h5 : powerSum z 5 = 0) : IsEvenPoly (rootPolynomial z) := by
  intro x
  -- Expand by coefficients; only even powers survive.
  have hcoeff_odd : ∀ k : ℕ, k % 2 = 1 → (rootPolynomial z).coeff k = 0 := by
    intro k hk
    by_cases h : k < 6
    · exact roots_even_coefficients z h1 h3 h5 k h hk
    · have hzero : (rootPolynomial z).coeff k = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have hdeg : (rootPolynomial z).natDegree ≤ 6 := by
          rw [rootPolynomial]
          simp
        omega
      exact hzero
  have hdeg : (rootPolynomial z).natDegree ≤ 6 := by
    rw [rootPolynomial]
    simp
  have hsum (y : ℂ) :
      (rootPolynomial z).eval y = ∑ k ∈ Finset.range 7, (rootPolynomial z).coeff k * y^k := by
    exact Polynomial.eval_eq_sum_range' (by omega) y
  rw [hsum (-x), hsum x]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  by_cases he : k % 2 = 1
  · rw [hcoeff_odd k he]
    simp
  · have heven : k % 2 = 0 := by omega
    rw [neg_pow]
    rw [show (-1 : ℂ) ^ k = 1 by
      have hk2 : ∃ n, k = 2*n := ⟨k/2, by omega⟩
      rcases hk2 with ⟨n, rfl⟩
      norm_num [pow_mul]]
    ring

lemma every_root_has_opposite (z : Fin 6 → ℂ)
    (h1 : powerSum z 1 = 0) (h3 : powerSum z 3 = 0)
    (h5 : powerSum z 5 = 0) :
    ∀ i : Fin 6, ∃ j : Fin 6, z j = -z i := by
  intro i
  have heven := rootPolynomial_isEven z h1 h3 h5
  have hroot : (rootPolynomial z).eval (z i) = 0 := by
    rw [rootPolynomial, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp
  have hnegroot : (rootPolynomial z).eval (-z i) = 0 := by
    rw [heven]
    exact hroot
  have hprod : (∏ j : Fin 6, ((-z i) - z j)) = 0 := by
    simpa [rootPolynomial, Polynomial.eval_prod] using hnegroot
  rcases (Finset.prod_eq_zero_iff).mp hprod with ⟨j, hj, hz⟩
  exact ⟨j, (sub_eq_zero.mp hz).symm⟩

lemma every_unit_root_has_distinct_opposite (z : Fin 6 → ℂ)
    (h1 : powerSum z 1 = 0) (h3 : powerSum z 3 = 0)
    (h5 : powerSum z 5 = 0)
    (hunit : ∀ i, Complex.normSq (z i) = 1) :
    ∀ i : Fin 6, ∃ j : Fin 6, j ≠ i ∧ z j = -z i := by
  intro i
  obtain ⟨j, hj⟩ := every_root_has_opposite z h1 h3 h5 i
  refine ⟨j, ?_, hj⟩
  intro hji
  subst j
  have hzero : z i = 0 := by
    have hsum : z i + z i = 0 := by
      calc
        z i + z i = -z i + z i := congrArg (fun w : ℂ => w + z i) hj
        _ = 0 := by simp
    have hmul : (2 : ℂ) * z i = 0 := by linear_combination hsum
    exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)
  have hunit_i := hunit i
  rw [hzero] at hunit_i
  norm_num at hunit_i

lemma neg_one_pow_eq_one {k : ℕ} (hk : k % 2 = 0) : (-1 : ℂ) ^ k = 1 := by
  have hk2 : ∃ n, k = 2*n := ⟨k/2, by omega⟩
  rcases hk2 with ⟨n, rfl⟩
  norm_num [pow_mul]

lemma rootPolynomial_comp_neg_eq (z : Fin 6 → ℂ)
    (h1 : powerSum z 1 = 0) (h3 : powerSum z 3 = 0)
    (h5 : powerSum z 5 = 0) :
    (rootPolynomial z).comp (-Polynomial.X) = rootPolynomial z := by
  have hodd := roots_even_coefficients z h1 h3 h5
  ext k
  rw [show (-Polynomial.X : Polynomial ℂ) = Polynomial.C (-1) * Polynomial.X by simp]
  rw [Polynomial.comp_C_mul_X_coeff]
  by_cases hk : k % 2 = 1
  · have hcoeff_zero : (rootPolynomial z).coeff k = 0 := by
      by_cases hlt : k < 6
      · exact hodd k hlt hk
      · apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have hdeg : (rootPolynomial z).natDegree ≤ 6 := by
          rw [rootPolynomial]
          simp
        omega
    rw [hcoeff_zero]
    simp
  · have heven : k % 2 = 0 := by omega
    rw [neg_one_pow_eq_one heven]
    ring

lemma root_multiset_eq_neg (z : Fin 6 → ℂ)
    (h1 : powerSum z 1 = 0) (h3 : powerSum z 3 = 0)
    (h5 : powerSum z 5 = 0) :
    (Finset.univ.val.map z) = Finset.univ.val.map (fun i => -z i) := by
  have hroots : (rootPolynomial z).roots = Finset.univ.val.map z := by
    simpa [rootPolynomial, Finset.prod] using
      (Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map z))
  have hcomp := Polynomial.roots_comp_neg_X (rootPolynomial z)
  rw [rootPolynomial_comp_neg_eq z h1 h3 h5] at hcomp
  rw [hroots] at hcomp
  simpa [Multiset.map_map] using hcomp

lemma exists_negating_equiv (z : Fin 6 → ℂ)
    (h1 : powerSum z 1 = 0) (h3 : powerSum z 3 = 0)
    (h5 : powerSum z 5 = 0) :
    ∃ σ : Fin 6 ≃ Fin 6, ∀ i, z (σ i) = -z i := by
  let s : Multiset (Fin 6) := Finset.univ.val
  have hm : s.map z = s.map (fun i => -z i) := by
    simpa [s] using root_multiset_eq_neg z h1 h3 h5
  let pos := Multiset.mapEquiv s z
  let neg := Multiset.mapEquiv s (fun i => -z i)
  let e : s ≃ s := pos.trans ((Multiset.cast hm).trans neg.symm)
  have he (x : s) : z (e x) = -z x := by
    have htrans : neg (e x) = Multiset.cast hm (pos x) := by
      simp [e]
    have hval : (neg (e x) : ℂ) = (Multiset.cast hm (pos x) : ℂ) :=
      congrArg (fun a : s.map (fun i => -z i) => (a : ℂ)) htrans
    have hrel : -z (e x) = z x := by
      simpa [neg, pos] using hval
    simpa using congrArg (fun w : ℂ => -w) hrel
  let eFin : Fin 6 ≃ s :=
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
  change z (eFin.symm (e (eFin i))) = -z i
  calc
    z (eFin.symm (e (eFin i))) = z ((e (eFin i)).1) := rfl
    _ = -z ((eFin i).1) := he (eFin i)
    _ = -z i := rfl

lemma paired_power_sum_zero {z : Fin 6 → ℂ} {σ : Fin 6 ≃ Fin 6}
    (hpair : ∀ i, z (σ i) = -z i) {k : ℕ} (hk : k % 2 = 1) :
    powerSum z k = 0 := by
  have hsum : powerSum z k = ∑ i : Fin 6, z (σ i) ^ k := by
    unfold powerSum
    symm
    exact Equiv.sum_comp σ (fun i => z i ^ k)
  have hneg : (-1 : ℂ) ^ k = -1 := by
    have hdiv := Nat.mod_add_div k 2
    have hkEq : k = 2*(k/2)+1 := by omega
    rw [hkEq]
    norm_num [pow_add, pow_mul]
  have hpowered (i : Fin 6) : z (σ i) ^ k = -(z i ^ k) := by
    rw [hpair i, neg_pow, hneg]
    ring
  have hzero : powerSum z k = -powerSum z k := by
    calc
      powerSum z k = ∑ i : Fin 6, z (σ i) ^ k := hsum
      _ = ∑ i : Fin 6, -(z i ^ k) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hpowered i
      _ = -(∑ i : Fin 6, z i ^ k) := by simp
      _ = -powerSum z k := rfl
  have hmul : (2 : ℂ) * powerSum z k = 0 := by linear_combination hzero
  exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)

theorem odd_power_sums_iff_negating_equiv (z : Fin 6 → ℂ) :
    (powerSum z 1 = 0 ∧ powerSum z 3 = 0 ∧ powerSum z 5 = 0) ↔
      ∃ σ : Fin 6 ≃ Fin 6, ∀ i, z (σ i) = -z i := by
  constructor
  · rintro ⟨h1, h3, h5⟩
    exact exists_negating_equiv z h1 h3 h5
  · rintro ⟨σ, hpair⟩
    refine ⟨paired_power_sum_zero hpair (by norm_num), ?_, ?_⟩
    · exact paired_power_sum_zero hpair (by norm_num)
    · exact paired_power_sum_zero hpair (by norm_num)

lemma negating_equiv_no_fixed_points {z : Fin 6 → ℂ} {σ : Fin 6 ≃ Fin 6}
    (hpair : ∀ i, z (σ i) = -z i)
    (hunit : ∀ i, Complex.normSq (z i) = 1) :
    ∀ i, σ i ≠ i := by
  intro i hfixed
  have hz : z i = -z i := by simpa [hfixed] using hpair i
  have hzero : z i = 0 := by
    have hsum : z i + z i = 0 := by
      calc
        z i + z i = -z i + z i := congrArg (fun w : ℂ => w + z i) hz
        _ = 0 := by simp
    have hmul : (2 : ℂ) * z i = 0 := by linear_combination hsum
    exact (mul_eq_zero.mp hmul).resolve_left (by norm_num)
  have hunit_i := hunit i
  rw [hzero] at hunit_i
  norm_num at hunit_i

theorem unit_roots_first_third_sums_pair_without_fixed_points
    (z : Fin 6 → ℂ) (hunit : ∀ i, Complex.normSq (z i) = 1)
    (h1 : powerSum z 1 = 0) (h3 : powerSum z 3 = 0) :
    ∃ σ : Fin 6 ≃ Fin 6,
      (∀ i, z (σ i) = -z i) ∧ (∀ i, σ i ≠ i) := by
  have h5 := powerSum_five_eq_zero_of_unit_first_third z hunit h1 h3
  obtain ⟨σ, hpair⟩ :=
    (odd_power_sums_iff_negating_equiv z).mp ⟨h1, h3, h5⟩
  exact ⟨σ, hpair, negating_equiv_no_fixed_points hpair hunit⟩

end OQP13SixRoots
