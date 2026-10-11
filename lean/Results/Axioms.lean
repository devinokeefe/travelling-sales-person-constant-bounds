/-
The axioms behind every top-level theorem.  `lake build Results.Axioms` prints them.
-/
import TSPBound
import TSPShared
import Results

-- the implementation computes what the recipe defines
#print axioms Correct.table_eq
#print axioms Correct.cellSum_eq_S
#print axioms Correct.sumsRange_eq_S
#print axioms Correct.totalOfSums_cellSums
#print axioms Correct.total_eq
#print axioms Correct.totalPar_eq
#print axioms Correct.cellSumFlip_eq_S
#print axioms Correct.sumsStep_eq_S
#print axioms Correct.AofPar_eq_A
#print axioms Correct.AofPar_nil
#print axioms Correct.totalFrom_eq_total

-- facts about auxiliary definitions of `Spec` that its comments refer to
#print axioms Correct.cdiv_spec
#print axioms Correct.ceilSqrt_spec
#print axioms Correct.minOf_spec
#print axioms Correct.mem_tuples
#print axioms Correct.nodup_tuples
#print axioms Correct.mem_orders

-- the parameter sets
#print axioms Results.k5_allowed
#print axioms Results.k6_allowed
#print axioms Results.k7_allowed
#print axioms Results.k8_allowed
#print axioms Results.k9_allowed
#print axioms Results.k5_exact
#print axioms Results.k6_exact
#print axioms Results.k7_exact
#print axioms Results.k8_exact
#print axioms Results.k9_exact

-- the results
#print axioms Results.tiny_total
#print axioms Results.tiny_accepts
#print axioms Results.k4_total
#print axioms Results.k4_accepts
#print axioms Results.k5_total
#print axioms Results.k5_accepts
#print axioms Results.k6_total
#print axioms Results.k6_accepts
#print axioms Results.k7_total
#print axioms Results.k7_accepts
#print axioms Results.k8_total
#print axioms Results.k8_accepts
#print axioms Results.k5p_total

-- the routine of `TSPShared`
#print axioms Correct.tablePool_eq
#print axioms Correct.sharedSums_eq_S
#print axioms Correct.AofShared_eq_A
#print axioms Correct.A_of_list

-- the results by the routine of `TSPShared`
#print axioms Results.k5s_total
#print axioms Results.k5s_accepts
#print axioms Results.k6s_total
#print axioms Results.k6s_accepts
#print axioms Results.k7s_total
#print axioms Results.k7s_accepts
#print axioms Results.k8s_total
#print axioms Results.k8s_accepts
#print axioms Results.k9s_total
#print axioms Results.k9s_accepts
