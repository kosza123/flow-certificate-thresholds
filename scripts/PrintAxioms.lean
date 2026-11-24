import PlanarCore

/-! Prints the axioms used by the main declarations.  Expected output for each:
`[propext, Classical.choice, Quot.sound]` (or a subset of these). -/

#print axioms PlanarCore.theorem1_certified
#print axioms PlanarCore.triCert
#print axioms PlanarCore.triG_certified_threshold
#print axioms PlanarCore.RotCert.H2
#print axioms PlanarCore.RotCert.orth
#print axioms PlanarCore.RotCert.dual_mul_transpose
#print axioms PlanarCore.RotCert.dual_connected
#print axioms PlanarCore.MGraph.detL_pos
#print axioms PlanarCore.MGraph.current_eq_numer_div
#print axioms PlanarCore.MGraph.threshold_cramer
#print axioms PlanarCore.MGraph.theorem1_networks
#print axioms PlanarCore.projA
#print axioms PlanarCore.projB
#print axioms PlanarCore.MGraph.H1_of_connected
#print axioms PlanarCore.MGraph.current_abs_le_one
#print axioms PlanarCore.T3_fekete
