import JamingLemma21

/-! Reduction of the six equations for a vector unbiased to the standard basis
and the two-parameter Fourier family, following Jaming et al., equations (5)-(14).

The statement is algebraic in the five phase coordinates and Fourier parameters `x`, `y`;
unit-modulus hypotheses are not needed for this six-equations-to-four-identities step. -/

namespace QutritMUB.JamingFourierFamilyReduction

open JamingLemma21

noncomputable def evenA (c3 : ℂ) : ℂ := 1 + c3
noncomputable def evenB (c1 c4 : ℂ) : ℂ := c1 + c4
noncomputable def evenC (c2 c5 : ℂ) : ℂ := c2 + c5

noncomputable def oddA (c3 : ℂ) : ℂ := 1 - c3
noncomputable def oddB (x c1 c4 : ℂ) : ℂ := x * (c4 - c1)
noncomputable def oddC (y c2 c5 : ℂ) : ℂ := y * (c2 - c5)

/-- The six unnormalised Fourier-overlap equations, grouped into even and odd rows. -/
def SixFourierEquations (c1 c2 c3 c4 c5 x y : ℂ) : Prop :=
  Complex.normSq (f0 (evenA c3) (evenB c1 c4) (evenC c2 c5)) = 6 ∧
  Complex.normSq (f1 (evenA c3) (evenB c1 c4) (evenC c2 c5)) = 6 ∧
  Complex.normSq (f2 (evenA c3) (evenB c1 c4) (evenC c2 c5)) = 6 ∧
  Complex.normSq (f0 (oddA c3) (oddB x c1 c4) (oddC y c2 c5)) = 6 ∧
  Complex.normSq (f1 (oddA c3) (oddB x c1 c4) (oddC y c2 c5)) = 6 ∧
  Complex.normSq (f2 (oddA c3) (oddB x c1 c4) (oddC y c2 c5)) = 6

/-- The reduced block energies and cyclic identities obtained from those six equations. -/
def BlockConditions (c1 c2 c3 c4 c5 x y : ℂ) : Prop :=
  (energy (evenA c3) (evenB c1 c4) (evenC c2 c5) = 6 ∧
    cyc (evenA c3) (evenB c1 c4) (evenC c2 c5) = 0) ∧
  (energy (oddA c3) (oddB x c1 c4) (oddC y c2 c5) = 6 ∧
    cyc (oddA c3) (oddB x c1 c4) (oddC y c2 c5) = 0)

/-- Jaming et al.'s six Fourier overlap equations are equivalent to two block-energy
identities and two directed cyclic cross-term identities. -/
theorem six_fourier_equations_iff_block_conditions
    (c1 c2 c3 c4 c5 x y : ℂ) :
    SixFourierEquations c1 c2 c3 c4 c5 x y ↔ BlockConditions c1 c2 c3 c4 c5 x y := by
  dsimp [SixFourierEquations, BlockConditions]
  constructor
  · rintro ⟨he0, he1, he2, ho0, ho1, ho2⟩
    exact ⟨(jaming_lemma_2_1 _ _ _).mp ⟨he0, he1, he2⟩,
      (jaming_lemma_2_1 _ _ _).mp ⟨ho0, ho1, ho2⟩⟩
  · rintro ⟨he, ho⟩
    rcases (jaming_lemma_2_1 _ _ _).mpr he with ⟨he0, he1, he2⟩
    rcases (jaming_lemma_2_1 _ _ _).mpr ho with ⟨ho0, ho1, ho2⟩
    exact ⟨he0, he1, he2, ho0, ho1, ho2⟩

#print axioms six_fourier_equations_iff_block_conditions

end QutritMUB.JamingFourierFamilyReduction
