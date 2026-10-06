import Mathlib

/-!
This is a finite algebra counterexample to the generic inference used in the
transition from a sum of matched products to a product of sums:
`(∀ i, A i * B i = 0) → (∑ i, A i) * (∑ i, B i) = 0`.

For the two-element index set, take A=(1,0) and B=(0,1). Every matched
product vanishes, while the product of sums is 1 because of the cross term.
This refutes only that generic algebraic inference. It is not a counterexample
to a real Hadamard cube, an MUB triplet, or any additional structural
hypotheses that might make the inference valid in that setting.
-/

namespace OQP13AggregateProductGap

def A : Fin 2 → ℚ := fun i => if i.val = 0 then 1 else 0
def B : Fin 2 → ℚ := fun i => if i.val = 1 then 1 else 0

theorem matched_products_vanish : ∀ i : Fin 2, A i * B i = 0 := by
  intro i
  fin_cases i <;> norm_num [A, B]

theorem product_of_sums_is_one :
    (∑ i : Fin 2, A i) * (∑ i : Fin 2, B i) = 1 := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two]
  norm_num [A, B]

theorem generic_inference_is_false :
    ¬ ((∀ i : Fin 2, A i * B i = 0) →
      (∑ i : Fin 2, A i) * (∑ i : Fin 2, B i) = 0) := by
  intro h
  have hzero := h matched_products_vanish
  rw [product_of_sums_is_one] at hzero
  norm_num at hzero

#print axioms matched_products_vanish
#print axioms product_of_sums_is_one
#print axioms generic_inference_is_false

end OQP13AggregateProductGap
