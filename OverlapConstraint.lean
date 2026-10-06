import Reduction

/-!
# Redundant overlap equation

For two unitary bases, the six squared overlaps in any fixed column of their
relative unitary sum to one. Consequently, for dimension six, any five of the
six exact unbiasedness equations force the sixth. This is the precise
constraint-counting statement; it does not imply that the remaining system
has no solutions.
-/

namespace OQP13OverlapConstraint

open OpenQuantumProblem13

theorem relative_column_normSq_sum (U V : UMat 6) (j : Fin 6) :
    ∑ i : Fin 6, Complex.normSq (relativeUnitary U V i j) = 1 := by
  have hunit : star (relativeUnitary U V) * relativeUnitary U V =
      (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
    rw [OQP13.relativeUnitary_eq_group]
    exact Matrix.UnitaryGroup.star_mul_self (U⁻¹ * V)
  have hentry := congrArg (fun M : Matrix (Fin 6) (Fin 6) ℂ => M j j) hunit
  have hcomplex :
      (∑ i : Fin 6, (Complex.normSq (relativeUnitary U V i j) : ℂ)) = 1 := by
    simpa [Matrix.mul_apply, Matrix.star_apply, Complex.normSq_eq_conj_mul_self] using hentry
  exact_mod_cast hcomplex

theorem last_overlap_forced (U V : UMat 6) (i₀ j : Fin 6)
    (h : ∀ i : Fin 6, i ≠ i₀ →
      ‖relativeUnitary U V i j‖ ^ (2 : ℕ) = (6 : ℝ)⁻¹) :
    ‖relativeUnitary U V i₀ j‖ ^ (2 : ℕ) = (6 : ℝ)⁻¹ := by
  have hsum := relative_column_normSq_sum U V j
  have hsplit :
      Complex.normSq (relativeUnitary U V i₀ j) +
        ∑ i ∈ Finset.univ.erase i₀,
          Complex.normSq (relativeUnitary U V i j) = 1 := by
    calc
      _ = ∑ i : Fin 6, Complex.normSq (relativeUnitary U V i j) :=
        Finset.add_sum_erase Finset.univ
          (fun i : Fin 6 => Complex.normSq (relativeUnitary U V i j)) (Finset.mem_univ i₀)
      _ = 1 := hsum
  have hrest :
      ∑ i ∈ Finset.univ.erase i₀,
        Complex.normSq (relativeUnitary U V i j) = (5 : ℝ) / 6 := by
    calc
      _ = ∑ i ∈ Finset.univ.erase i₀, (6 : ℝ)⁻¹ := by
        apply Finset.sum_congr rfl
        intro i hi
        have hne : i ≠ i₀ := (Finset.mem_erase.mp hi).1
        exact (RCLike.normSq_eq_def' (relativeUnitary U V i j)).trans (h i hne)
      _ = (5 : ℝ) / 6 := by simp; norm_num
  calc
    ‖relativeUnitary U V i₀ j‖ ^ (2 : ℕ) =
        Complex.normSq (relativeUnitary U V i₀ j) :=
      (RCLike.normSq_eq_def' (relativeUnitary U V i₀ j)).symm
    _ = (6 : ℝ)⁻¹ := by
      have hval : Complex.normSq (relativeUnitary U V i₀ j) = (6 : ℝ)⁻¹ := by
        linarith [hsplit, hrest]
      exact hval

end OQP13OverlapConstraint

#print axioms OQP13OverlapConstraint.last_overlap_forced
