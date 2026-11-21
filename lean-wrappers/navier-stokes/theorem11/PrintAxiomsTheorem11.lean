/-
Axiom report for the space-side Theorem 1.1 wrapper and the helper modules that
compile on their own. The torus modules have their own report in
`PrintAxiomsTheorem11Torus.lean`, so a torus failure cannot hide these lines.
The global endpoints `Theorem11.theorem11Space` and `Theorem11.theorem11SpaceBlowup`
are printed last; the torus endpoint is an open target and is not declared.
-/
import Theorem11Solution
import Theorem11TorusMildExport
import Theorem11ContractFacts
import Theorem11GeometricRate
import Theorem11NormAssembly

#print axioms Theorem11Rate.norm_window
#print axioms Theorem11Rate.undo_quarter_scaling
#print axioms Theorem11Rate.power_error_small
#print axioms Theorem11Rate.late_rate
#print axioms Theorem11Rate.globalize_rate
#print axioms Theorem11GeometricRate.geometric_decay_exponent
#print axioms Theorem11GeometricRate.geometric_coefficient_eq
#print axioms Theorem11.finiteH1On_and_h1NormOn_eq_split
#print axioms Theorem11Core.norm_sq_eq_sum_partial
#print axioms Theorem11Core.gradient_reading
#print axioms Theorem11Core.mild_ne_zero_of_late_rate
#print axioms Theorem11Core.space_core
#print axioms Theorem11Core.local_velocity_unique
#print axioms Theorem11Core.partial_reading_of_smooth
#print axioms Theorem11Core.gradient_reading_of_smooth
#print axioms Theorem11Core.rescaled_gradient_reading
#print axioms Theorem11Core.local_physical_quantitative
#print axioms Theorem11.theorem11SpaceCore
#print axioms Theorem11.theorem11SpaceLocal
#print axioms Theorem11.theorem11SpaceSlabs
#print axioms Breakdown.Theorem11.Torus.torus_mild_blowup_of_profile
#print axioms Theorem11.comparisonField_one_zero
#print axioms Theorem11.rescaleAtOne_zero
#print axioms Theorem11.gradientNorm_eq_norm_of_sq_eq
#print axioms Theorem11Energy.energy_le_initial
#print axioms Theorem11Glue.pressure_agree
#print axioms Theorem11.glued_solution
#print axioms Theorem11Core.no_continuous_continuation
#print axioms Theorem11.theorem11SpaceBlowup
#print axioms Theorem11.theorem11Space
