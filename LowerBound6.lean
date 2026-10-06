import FormalConjectures.OpenQuantumProblems.«13»
import QutritMUB
import TensorMUB
import TensorMUB6
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Local proof of the known lower bound `HasMUBs 6 3`, by tensoring the qubit
and qutrit MUB families and transporting the index type to `Fin 6`. -/

open scoped Kronecker
open OpenQuantumProblem13

namespace OQP13LowerBound6

noncomputable def qScale : ℂ := ((Real.sqrt 3 : ℝ)⁻¹ : ℂ)

lemma sqrt_three_sq : (Real.sqrt 3 : ℝ) ^ 2 = 3 := by
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

lemma qScale_sq : star qScale * qScale = (3 : ℂ)⁻¹ := by
  simp [qScale]
  field_simp
  exact_mod_cast sqrt_three_sq.symm

noncomputable def fMat : Matrix (Fin 3) (Fin 3) ℂ := QutritMUB.fourier
noncomputable def cMat : Matrix (Fin 3) (Fin 3) ℂ := QutritMUB.chirp

lemma fourier_gram_matrix :
    star fMat * fMat = (3 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  change (∑ k : Fin 3, star (QutritMUB.fourier k i) * QutritMUB.fourier k j) = _
  rw [QutritMUB.fourier_gram]
  simp [Matrix.one_apply]

lemma chirp_gram_matrix :
    star cMat * cMat = (3 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  change (∑ k : Fin 3, star (QutritMUB.chirp k i) * QutritMUB.chirp k j) = _
  rw [QutritMUB.chirp_gram]
  simp [Matrix.one_apply]

lemma star_smul_mul_smul_three (a : ℂ) (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    star (a • A) * (a • B) = (star a * a) • (star A * B) := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_succ]
  ring_nf

lemma scaled_unitary_of_gram {A : Matrix (Fin 3) (Fin 3) ℂ}
    (hA : star A * A = (3 : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) :
    qScale • A ∈ Matrix.unitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  calc
    star (qScale • A) * (qScale • A) = (star qScale * qScale) • (star A * A) :=
      star_smul_mul_smul_three qScale A A
    _ = 1 := by rw [hA, qScale_sq]; simp [smul_smul]

noncomputable def qFourier : UMat 3 :=
  ⟨qScale • fMat, scaled_unitary_of_gram fourier_gram_matrix⟩

noncomputable def qChirp : UMat 3 :=
  ⟨qScale • cMat, scaled_unitary_of_gram chirp_gram_matrix⟩

lemma qScale_norm_sq : ‖qScale‖ ^ (2 : ℕ) = (3 : ℝ)⁻¹ := by
  rw [RCLike.norm_sq_eq_def]
  simp [qScale]
  field_simp
  norm_num [sqrt_three_sq]

lemma scaled_entry_unbiased (z : ℂ) (hz : Complex.normSq z = 1) :
    ‖qScale * z‖ ^ (2 : ℕ) = (3 : ℝ)⁻¹ := by
  calc
    ‖qScale * z‖ ^ (2 : ℕ) = ‖qScale‖ ^ (2 : ℕ) * ‖z‖ ^ (2 : ℕ) := by
      rw [norm_mul, mul_pow]
    _ = (3 : ℝ)⁻¹ := by
      have hz' : ‖z‖ ^ (2 : ℕ) = 1 := by
        calc
          ‖z‖ ^ (2 : ℕ) = Complex.normSq z := by
            simpa using (RCLike.normSq_eq_def' z).symm
          _ = 1 := hz
      rw [qScale_norm_sq, hz']
      norm_num

def qZ : UMat 3 := 1

noncomputable def qutritFamily : Fin 3 → UMat 3 := ![qZ, qFourier, qChirp]

lemma qZ_fourier_unbiased : IsUnbiased qZ qFourier := by
  intro i j
  have hrel : relativeUnitary qZ qFourier = qScale • fMat := by
    ext a b
    simp [relativeUnitary, qZ, qFourier, fMat]
  rw [hrel]
  change ‖qScale * QutritMUB.fourier i j‖ ^ (2 : ℕ) = (3 : ℝ)⁻¹
  exact scaled_entry_unbiased _ (QutritMUB.fourier_entry_normSq i j)

lemma qZ_chirp_unbiased : IsUnbiased qZ qChirp := by
  intro i j
  have hrel : relativeUnitary qZ qChirp = qScale • cMat := by
    ext a b
    simp [relativeUnitary, qZ, qChirp, cMat]
  rw [hrel]
  change ‖qScale * QutritMUB.chirp i j‖ ^ (2 : ℕ) = (3 : ℝ)⁻¹
  exact scaled_entry_unbiased _ (QutritMUB.chirp_entry_normSq i j)

lemma scaled_cross_unbiased (z : ℂ) (hz : Complex.normSq z = 3) :
    ‖(3 : ℂ)⁻¹ * z‖ ^ (2 : ℕ) = (3 : ℝ)⁻¹ := by
  rw [norm_mul, mul_pow]
  have hz' : ‖z‖ ^ (2 : ℕ) = 3 := by
    calc
      ‖z‖ ^ (2 : ℕ) = Complex.normSq z := by
        simpa using (RCLike.normSq_eq_def' z).symm
      _ = 3 := hz
  rw [hz']
  norm_num

lemma qFourier_chirp_unbiased : IsUnbiased qFourier qChirp := by
  intro i j
  have hrel : relativeUnitary qFourier qChirp = (3 : ℂ)⁻¹ • (star fMat * cMat) := by
    rw [relativeUnitary, qFourier, qChirp, star_smul_mul_smul_three, qScale_sq]
  rw [hrel]
  have hentry : (star fMat * cMat) i j =
      ∑ k : Fin 3, star (QutritMUB.fourier k i) * QutritMUB.chirp k j := by
    change (∑ k : Fin 3, star (fMat k i) * cMat k j) = _
    simp [fMat, cMat]
  rw [Matrix.smul_apply, hentry]
  change ‖(3 : ℂ)⁻¹ *
    (∑ k : Fin 3, star (QutritMUB.fourier k i) * QutritMUB.chirp k j)‖ ^
      (2 : ℕ) = (3 : ℝ)⁻¹
  exact scaled_cross_unbiased _ (QutritMUB.fourier_chirp_flat i j)

lemma qutritFamily_isMUB : IsMUBFamily qutritFamily := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> try contradiction
  · simpa [qutritFamily] using qZ_fourier_unbiased
  · simpa [qutritFamily] using qZ_chirp_unbiased
  · simpa [qutritFamily] using (IsUnbiased.symm qZ_fourier_unbiased)
  · simpa [qutritFamily] using qFourier_chirp_unbiased
  · simpa [qutritFamily] using (IsUnbiased.symm qZ_chirp_unbiased)
  · simpa [qutritFamily] using (IsUnbiased.symm qFourier_chirp_unbiased)

private lemma unbiased_to_tensorMatrix {d : ℕ} {U V : UMat d}
    (h : IsUnbiased U V) :
    OQP13Tensor.IsUnbiasedMatrix d (U : Matrix (Fin d) (Fin d) ℂ)
      (V : Matrix (Fin d) (Fin d) ℂ) := by
  intro i j
  simpa [OQP13Tensor.IsUnbiasedMatrix, relativeUnitary, Matrix.star_eq_conjTranspose] using h i j

private lemma unbiased_from_tensorMatrix {d : ℕ} {U V : UMat d}
    (h : OQP13Tensor.IsUnbiasedMatrix d (U : Matrix (Fin d) (Fin d) ℂ)
      (V : Matrix (Fin d) (Fin d) ℂ)) : IsUnbiased U V := by
  intro i j
  simpa [OQP13Tensor.IsUnbiasedMatrix, relativeUnitary, Matrix.star_eq_conjTranspose] using h i j

noncomputable def tensorBasis6 (i : Fin 3) : UMat 6 :=
  ⟨Matrix.reindex (finProdFinEquiv (m := 2) (n := 3))
      (finProdFinEquiv (m := 2) (n := 3))
      ((Qubit.qubitFamily i : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ
        (qutritFamily i : Matrix (Fin 3) (Fin 3) ℂ)),
    OQP13Tensor.tensor2x3_mem_unitaryGroup
      (Qubit.qubitFamily i).2
      (qutritFamily i).2⟩

lemma tensorBasis6_isMUB : IsMUBFamily tensorBasis6 := by
  intro i j hij
  have hq : IsUnbiased (Qubit.qubitFamily i) (Qubit.qubitFamily j) :=
    Qubit.qubitFamily_isMUB hij
  have h3 : IsUnbiased (qutritFamily i) (qutritFamily j) := qutritFamily_isMUB hij
  have hq' := unbiased_to_tensorMatrix hq
  have h3' := unbiased_to_tensorMatrix h3
  have hTensor := OQP13Tensor.isUnbiasedMatrix_tensor2x3_reindex hq' h3'
  exact unbiased_from_tensorMatrix hTensor

theorem hasMUBs_6_3 : HasMUBs 6 3 := ⟨tensorBasis6, tensorBasis6_isMUB⟩

end OQP13LowerBound6
