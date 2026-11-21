import SpaceCore
import Breakdown.Uniqueness.LocalBlowup

/-!
# No smooth continuation through the blow-up time

If a field is continuous on [0,1] × R³ and agrees at every time of [0,1) with
the velocity reading of the constructed abstract trajectory, then the authors'
`false_of_orbit_rate` gives a contradiction: in self-similar variables the
trajectory converges to the nonzero profile, which a field continuous up to
time one cannot do.
-/

open MeasureTheory Set Real
open scoped ENNReal ContDiff Topology

noncomputable section

namespace Theorem11Core

open Breakdown Breakdown.Freq

theorem no_continuous_continuation (W : ℝ → Space → Space) (q : ℝ → Space → ℝ)
    (P : ℝ) (R : Space ≃ₗᵢ[ℝ] Space) (A : ℝ)
    (hP : 0 < P) (hprofile : IsSimilarityProfile W q A)
    (hperiodic : ∀ s y, W (s + P) y = R (W s (R.symm y)))
    (hnonzero : ∃ s y, W s y ≠ 0) {ε : ℝ} (z : SpaceWitness W ε)
    {v : ℝ → Space → Space}
    (hv : ContinuousOn (fun p : ℝ × Space => v p.1 p.2) (Icc 0 1 ×ˢ univ))
    (hagree : ∀ t ∈ Ico (0 : ℝ) 1,
      (velocity (z.state t) : Space → Space) =ᵐ[volume] v t) : False := by
  have horbit : realization.F.IsOrbit (realization.rot R)
      (fun s => realization.embed (W s)) P :=
    embeddedProfileOrbit_holds X realization W q P R A hP hprofile hperiodic hnonzero
  exact false_of_orbit_rate realization_fieldReading horbit z.exponent_pos z.convergence hv hagree

end Theorem11Core
