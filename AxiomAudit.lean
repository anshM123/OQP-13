import Reduction
import OverlapConstraint
import HadamardBridge
import LowerBound
import LowerBound6
import SixRootPairing
import HadamardRootBridge
import Proposition46
import Corollary47Audit
import Corollary47FixedI
import Corollary47ArbitraryI
import AggregateProductGap

/-!
# OQP 13 axiom audit

Print the axioms used by the checked reduction, lower-bound construction, and
six-root pairing criterion so that unexpected assumptions are visible.
-/

#print axioms OQP13.four_iff_normalized
#print axioms OQP13.four_iff_transition_triple
#print axioms OQP13.max_three_iff_no_four
#print axioms OQP13OverlapConstraint.last_overlap_forced
#print axioms OQP13HadamardBridge.four_iff_six_hadamard_transitions
#print axioms OQP13.cubeRoot_pow_three
#print axioms OQP13LowerBound6.hasMUBs_6_3
#print axioms OQP13SixRoots.every_unit_root_has_distinct_opposite
#print axioms OQP13SixRoots.odd_power_sums_iff_negating_equiv
#print axioms OQP13SixRoots.negating_equiv_no_fixed_points
#print axioms OQP13SixRoots.unit_roots_first_third_sums_pair_without_fixed_points
#print axioms OQP13HadamardRootBridge.G_conditions_give_opposite_pairing
#print axioms OQP13Proposition46.proposition_4_6_pairing
#print axioms OQP13Corollary47Audit.printed_hypotheses_without_pairing
#print axioms OQP13Corollary47FixedI.fixed_even_odd_pairing
#print axioms OQP13Corollary47ArbitraryI.arbitrary_three_pairing
#print axioms OQP13AggregateProductGap.generic_inference_is_false
