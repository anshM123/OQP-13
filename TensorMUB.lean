import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Complex.Norm

open scoped Kronecker

namespace OQP13Tensor

/-- Entries of the relative unitary of two basis matrices have the MUB norm. -/
def IsUnbiasedMatrix {α : Type*} [Fintype α] (d : ℕ)
    (A B : Matrix α α ℂ) : Prop :=
  ∀ i j, ‖(A.conjTranspose * B) i j‖ ^ (2 : ℕ) = (d : ℝ)⁻¹

/-- The relative matrix of tensor-product bases is the tensor product
of their relative matrices. -/
theorem relative_kronecker {α β : Type*} [Fintype α] [Fintype β]
    (A C : Matrix α α ℂ) (B D : Matrix β β ℂ) :
    (A ⊗ₖ B).conjTranspose * (C ⊗ₖ D) =
      (A.conjTranspose * C) ⊗ₖ (B.conjTranspose * D) := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul]

/-- Tensoring two unbiased matrix pairs multiplies their dimensions. -/
theorem isUnbiasedMatrix_kronecker {α β : Type*} [Fintype α] [Fintype β]
    {m n : ℕ} {A C : Matrix α α ℂ} {B D : Matrix β β ℂ}
    (hm : m = Fintype.card α) (hn : n = Fintype.card β)
    (hA : IsUnbiasedMatrix m A C) (hB : IsUnbiasedMatrix n B D) :
    IsUnbiasedMatrix (Fintype.card α * Fintype.card β) (A ⊗ₖ B) (C ⊗ₖ D) := by
  have hprod : IsUnbiasedMatrix (m * n) (A ⊗ₖ B) (C ⊗ₖ D) := by
    intro x y
    rw [relative_kronecker]
    simp only [Matrix.kroneckerMap_apply, Complex.norm_mul]
    rw [mul_pow]
    rw [hA x.1 y.1, hB x.2 y.2]
    simp [Nat.cast_mul, mul_comm]
  simpa [hm, hn] using hprod

end OQP13Tensor
