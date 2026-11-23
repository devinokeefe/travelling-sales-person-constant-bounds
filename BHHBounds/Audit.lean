import BHHBounds.Bounds

/-!
# Axiom audit

Besides Lean's three standard axioms, the theorems depend only on the `native_decide` computations
listed here. The build fails if a list changes.
-/

/--
info: 'BHHBounds.expectedTourLength_lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 BHHBounds.Cert.allBoxes_disjoint_bool._native.native_decide.ax_1_1,
 BHHBounds.Cert.allBoxes_valid_bool._native.native_decide.ax_1_1,
 BHHBounds.Cert.base_cert_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.stepPot_valid_bool._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard00_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard01_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard02_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard03_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard04_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard05_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard06_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard07_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard08_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard09_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard10_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard11_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard12_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard13_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard14_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard15_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard16_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard17_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard18_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard19_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard20_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard21_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard22_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard23_verified._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms BHHBounds.expectedTourLength_lower_bound

/--
info: 'BHHBounds.expectedTourLength_upper_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 BHHBounds.Upper.checkFixedPoint4_dpPotential4._native.native_decide.ax_1_1,
 BHHBounds.Upper.costFlat1_checked._native.native_decide.ax_1_1,
 BHHBounds.Upper.costFlat2_checked._native.native_decide.ax_1_1,
 BHHBounds.Upper.costFlat3_checked._native.native_decide.ax_1_1,
 BHHBounds.Upper.costFlat4_checked._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms BHHBounds.expectedTourLength_upper_bound

/--
info: 'BHHBounds.bhh_bounds' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 BHHBounds.Cert.allBoxes_disjoint_bool._native.native_decide.ax_1_1,
 BHHBounds.Cert.allBoxes_valid_bool._native.native_decide.ax_1_1,
 BHHBounds.Cert.base_cert_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.stepPot_valid_bool._native.native_decide.ax_1_1,
 BHHBounds.Upper.checkFixedPoint4_dpPotential4._native.native_decide.ax_1_1,
 BHHBounds.Upper.costFlat1_checked._native.native_decide.ax_1_1,
 BHHBounds.Upper.costFlat2_checked._native.native_decide.ax_1_1,
 BHHBounds.Upper.costFlat3_checked._native.native_decide.ax_1_1,
 BHHBounds.Upper.costFlat4_checked._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard00_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard01_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard02_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard03_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard04_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard05_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard06_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard07_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard08_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard09_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard10_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard11_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard12_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard13_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard14_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard15_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard16_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard17_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard18_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard19_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard20_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard21_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard22_verified._native.native_decide.ax_1_1,
 BHHBounds.Cert.Shards.shard23_verified._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms BHHBounds.bhh_bounds
