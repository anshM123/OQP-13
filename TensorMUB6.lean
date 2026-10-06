import TensorMUB
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Logic.Equiv.Fin.Basic

open scoped Kronecker

namespace OQP13Tensor

/-- The tensor product of two unitary matrices is unitary on product indices. -/
theorem kronecker_mem_unitaryGroup {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    {A : Matrix α α ℂ} {B : Matrix β β ℂ}
    (hA : A ∈ Matrix.unitaryGroup α ℂ) (hB : B ∈ Matrix.unitaryGroup β ℂ) :
    A ⊗ₖ B ∈ Matrix.unitaryGroup (α × β) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hA hB ⊢
  rw [Matrix.star_eq_conjTranspose] at hA hB
  change (A ⊗ₖ B).conjTranspose * (A ⊗ₖ B) = 1
  calc
    (A ⊗ₖ B).conjTranspose * (A ⊗ₖ B)
        = (A.conjTranspose * A) ⊗ₖ (B.conjTranspose * B) := by
            rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]
    _ = 1 := by rw [hA, hB]; simp

/-- Reindexing rows and columns by the same equivalence preserves unitarity. -/
theorem reindex_mem_unitaryGroup {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    {A : Matrix α α ℂ} (hA : A ∈ Matrix.unitaryGroup α ℂ) :
    Matrix.reindex e e A ∈ Matrix.unitaryGroup β ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hA ⊢
  rw [Matrix.star_eq_conjTranspose] at hA
  change (Matrix.reindex e e A).conjTranspose * Matrix.reindex e e A = 1
  calc
    (Matrix.reindex e e A).conjTranspose * Matrix.reindex e e A
        = Matrix.reindex e e (A.conjTranspose * A) := by
            rw [Matrix.conjTranspose_reindex e e]
            simpa only [Matrix.coe_reindexLinearEquiv] using
              (Matrix.reindexLinearEquiv_mul ℂ ℂ e e e A.conjTranspose A)
    _ = 1 := by rw [hA]; simp

/-- Reindexing the two bases preserves their relative-unitary overlap matrix. -/
theorem relative_reindex {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β)
    (A B : Matrix α α ℂ) :
    (Matrix.reindex e e A).conjTranspose * Matrix.reindex e e B =
      Matrix.reindex e e (A.conjTranspose * B) := by
  rw [Matrix.conjTranspose_reindex e e]
  simpa only [Matrix.coe_reindexLinearEquiv] using
    (Matrix.reindexLinearEquiv_mul ℂ ℂ e e e A.conjTranspose B)

/-- The custom unbiasedness condition is invariant under simultaneous reindexing. -/
theorem isUnbiasedMatrix_reindex {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (e : α ≃ β) {d : ℕ}
    {A B : Matrix α α ℂ} (h : IsUnbiasedMatrix d A B) :
    IsUnbiasedMatrix d (Matrix.reindex e e A) (Matrix.reindex e e B) := by
  intro i j
  rw [relative_reindex]
  simpa [Matrix.reindex_apply] using h (e.symm i) (e.symm j)

/-- Product-index tensor matrices and their `Fin 6` reindexing are unitaries. -/
theorem tensor2x3_mem_unitaryGroup
    {A : Matrix (Fin 2) (Fin 2) ℂ} {B : Matrix (Fin 3) (Fin 3) ℂ}
    (hA : A ∈ Matrix.unitaryGroup (Fin 2) ℂ)
    (hB : B ∈ Matrix.unitaryGroup (Fin 3) ℂ) :
    Matrix.reindex (finProdFinEquiv (m := 2) (n := 3))
      (finProdFinEquiv (m := 2) (n := 3)) (A ⊗ₖ B) ∈
        Matrix.unitaryGroup (Fin 6) ℂ := by
  apply reindex_mem_unitaryGroup (finProdFinEquiv (m := 2) (n := 3))
  exact kronecker_mem_unitaryGroup hA hB

/-- Unbiasedness of two local pairs tensors and reindexes to the corresponding
dimension-six unbiasedness statement. -/
theorem isUnbiasedMatrix_tensor2x3_reindex
    {A C : Matrix (Fin 2) (Fin 2) ℂ} {B D : Matrix (Fin 3) (Fin 3) ℂ}
    (hAC : IsUnbiasedMatrix 2 A C) (hBD : IsUnbiasedMatrix 3 B D) :
    IsUnbiasedMatrix 6
      (Matrix.reindex (finProdFinEquiv (m := 2) (n := 3))
        (finProdFinEquiv (m := 2) (n := 3)) (A ⊗ₖ B))
      (Matrix.reindex (finProdFinEquiv (m := 2) (n := 3))
        (finProdFinEquiv (m := 2) (n := 3)) (C ⊗ₖ D)) := by
  have hprod : IsUnbiasedMatrix 6 (A ⊗ₖ B) (C ⊗ₖ D) := by
    simpa using isUnbiasedMatrix_kronecker (α := Fin 2) (β := Fin 3)
      (m := 2) (n := 3) rfl rfl hAC hBD
  exact isUnbiasedMatrix_reindex (finProdFinEquiv (m := 2) (n := 3)) hprod

end OQP13Tensor
