import Corollary47FixedI

/-!
Arbitrary three-element coordinate set version of the corrected Corollary 4.7
pairing. Products and sums are over the subtype of coordinates, so the result
does not depend on a chosen ordering of either set.

The two subset-indexed sum terms are stated explicitly. They are exactly the
decomposition of the global ratio sum over `I` and `Iᶜ`; this avoids hiding a
nontrivial reindexing step in the statement.
-/

namespace OQP13Corollary47ArbitraryI

abbrev Coord (s : Finset (Fin 6)) := {i // i ∈ s}

noncomputable def subsetProduct (z : Fin 6 → ℂ) (s : Finset (Fin 6)) : ℂ :=
  ∏ i : Coord s, z i.1

noncomputable def muProduct (z : Fin 6 → ℂ) (s : Finset (Fin 6)) : ℂ :=
  subsetProduct z sᶜ / subsetProduct z s

private lemma subsetProduct_ne_zero {z : Fin 6 → ℂ} {s : Finset (Fin 6)}
    (hz : ∀ i, Complex.normSq (z i) = 1) : subsetProduct z s ≠ 0 := by
  classical
  have hz0 (i : Fin 6) : z i ≠ 0 := by
    intro h
    have hh := hz i
    rw [h] at hh
    norm_num at hh
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact hz0 i.1

/-- Arbitrary-index-set Corollary 4.7 pairing. The hypotheses say that both
coordinate triples have unit entries, their ratio sum vanishes, and their
complementary-product ratios are opposite. The conclusion is an actual
equivalence between the coordinate set and its complement, pairing every
ratio with its negative.

The cardinality hypotheses expose exactly the finite reindexing needed to
apply Proposition 4.6; for a 3-element subset of `Fin 6`, both follow from
`I.card = 3` by finite-cardinality arithmetic.
-/
theorem arbitrary_three_pairing
    (I : Finset (Fin 6))
    (hI : I.card = 3)
    (a b : Fin 6 → ℂ)
    (ha : ∀ i, Complex.normSq (a i) = 1)
    (hb : ∀ i, Complex.normSq (b i) = 1)
    (hSum : (∑ i : Coord I, a i.1 / b i.1) +
      (∑ i : Coord Iᶜ, a i.1 / b i.1) = 0)
    (lam : ℂ)
    (haμ : muProduct a I = lam)
    (hbμ : muProduct b I = -lam) :
    ∃ e : Coord I ≃ Coord Iᶜ,
      ∀ i, a i.1 / b i.1 + a (e i).1 / b (e i).1 = 0 := by
  classical
  have hCardI : Fintype.card (Coord I) = 3 := by simp [Coord, hI]
  have hCardC : Fintype.card (Coord Iᶜ) = 3 := by
    simpa [Coord, Finset.card_compl, hI]
  let eI : Fin 3 ≃ Coord I :=
    (Fintype.equivFinOfCardEq hCardI).symm
  let eC : Fin 3 ≃ Coord Iᶜ :=
    (Fintype.equivFinOfCardEq hCardC).symm
  let x : Fin 6 → ℂ := fun i => a i / b i
  have hxunit : ∀ i, Complex.normSq (x i) = 1 := by
    intro i
    simp only [x, Complex.normSq_div, ha i, hb i]
    norm_num
  have hI' : (∑ i : Fin 3, x (eI i).1) =
        ∑ i : Coord I, x i.1 := by
    exact Equiv.sum_comp eI (fun q : Coord I => x q.1)
  have hC' : (∑ i : Fin 3, x (eC i).1) =
        ∑ i : Coord Iᶜ, x i.1 := by
    exact Equiv.sum_comp eC (fun q : Coord Iᶜ => x q.1)
  have hprod :
      (∏ i : Fin 3, x (eI i).1) + (∏ i : Fin 3, x (eC i).1) = 0 := by
    have hpA : subsetProduct a Iᶜ = lam * subsetProduct a I := by
      change subsetProduct a Iᶜ / subsetProduct a I = lam at haμ
      have := (div_eq_iff (subsetProduct_ne_zero ha)).mp haμ
      linear_combination this
    have hpB : subsetProduct b Iᶜ = -lam * subsetProduct b I := by
      change subsetProduct b Iᶜ / subsetProduct b I = -lam at hbμ
      have := (div_eq_iff (subsetProduct_ne_zero hb)).mp hbμ
      linear_combination this
    have hprodA : (∏ i : Fin 3, a (eI i).1) = subsetProduct a I := by
      exact Equiv.prod_comp eI (fun q : Coord I => a q.1)
    have hprodAc : (∏ i : Fin 3, a (eC i).1) = subsetProduct a Iᶜ := by
      exact Equiv.prod_comp eC (fun q : Coord Iᶜ => a q.1)
    have hprodB : (∏ i : Fin 3, b (eI i).1) = subsetProduct b I := by
      exact Equiv.prod_comp eI (fun q : Coord I => b q.1)
    have hprodBc : (∏ i : Fin 3, b (eC i).1) = subsetProduct b Iᶜ := by
      exact Equiv.prod_comp eC (fun q : Coord Iᶜ => b q.1)
    have hratioI :
        (∏ i : Fin 3, x (eI i).1) =
          subsetProduct a I / subsetProduct b I := by
      simp [x, ← hprodA, ← hprodB, Finset.prod_div_distrib]
    have hratioC :
        (∏ i : Fin 3, x (eC i).1) =
          subsetProduct a Iᶜ / subsetProduct b Iᶜ := by
      simp [x, ← hprodAc, ← hprodBc, Finset.prod_div_distrib]
    rw [hratioI, hratioC]
    have hcross :
        subsetProduct a I * subsetProduct b Iᶜ +
          subsetProduct a Iᶜ * subsetProduct b I = 0 := by
      rw [hpA, hpB]
      ring
    field_simp [subsetProduct_ne_zero hb]
    ring_nf
    linear_combination hcross
  have hsum3 :
      (∑ i : Fin 3, x (eI i).1) + (∑ i : Fin 3, x (eC i).1) = 0 := by
    rw [hI', hC']
    simpa [x] using hSum
  have hsumScalars :
      x (eI 0).1 + x (eI 1).1 + x (eI 2).1 =
        -(x (eC 0).1 + x (eC 1).1 + x (eC 2).1) := by
    simp [Fin.sum_univ_succ] at hsum3
    linear_combination hsum3
  have hprodScalars :
      x (eI 0).1 * x (eI 1).1 * x (eI 2).1 =
        -(x (eC 0).1 * x (eC 1).1 * x (eC 2).1) := by
    simp [Fin.prod_univ_succ] at hprod
    linear_combination hprod
  obtain ⟨σ, hσ⟩ := OQP13Proposition46.complementary_triples_pair
    (x (eI 0).1) (x (eI 1).1) (x (eI 2).1)
    (x (eC 0).1) (x (eC 1).1) (x (eC 2).1)
    (hxunit _) (hxunit _) (hxunit _) (hxunit _) (hxunit _) (hxunit _)
    hsumScalars hprodScalars
  have evalI (j : Fin 3) :
      OQP13Proposition46.triple (x (eI 0).1) (x (eI 1).1) (x (eI 2).1) j =
        x (eI j).1 := by
    fin_cases j <;> simp [OQP13Proposition46.triple]
  have evalC (j : Fin 3) :
      OQP13Proposition46.triple (x (eC 0).1) (x (eC 1).1) (x (eC 2).1) j =
        x (eC j).1 := by
    fin_cases j <;> simp [OQP13Proposition46.triple]
  refine ⟨eI.symm.trans (σ.trans eC), ?_⟩
  intro i
  obtain ⟨j, rfl⟩ := eI.surjective i
  have hi := hσ j
  rw [evalC] at hi
  rw [evalI] at hi
  have hz : x (eC (σ j)).1 + x (eI j).1 = 0 := by rw [hi]; ring
  simpa [x, add_comm] using hz

end OQP13Corollary47ArbitraryI

#print axioms OQP13Corollary47ArbitraryI.arbitrary_three_pairing
