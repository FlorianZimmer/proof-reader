/-
Theorem 7.1: the same selected profile after smoothing.
Status: NOT COMPILED. Uses the added keep modules and Theorem71Transport; authors' files are unchanged.
-/
import Theorem71Keep
import Theorem71Statements
import Theorem71Transport

open MeasureTheory
open scoped ContDiff ENNReal

noncomputable section

namespace Breakdown.Theorem71

open Cert Freq

/-- The exact profile retains the selected period and agrees with the retained
    approximate-plus-correction field after normalizing similarity time. -/
theorem HeldWitness.smoothWithData {k : ℕ} {d : ExtendedCertificateData k}
    (a : HeldWitness d) :
    ∃ (W : VelField) (q : ℝ → Space → ℝ) (C : ℝ),
      FarField.IsSmoothOrbitField W q (d.period a.parameter)
        (LinearIsometryEquiv.refl ℝ Space) ∧
      FarField.DecayBounds W q C ∧
      ∀ᵐ θ, (fun y => W (d.period a.parameter * θ) y) =ᵐ[volume]
        (fun y => d.profile a.parameter θ y + a.correction θ y) := by
  obtain ⟨w, hw, hraw⟩ := a.orbit
  obtain ⟨W, q, C, hW, hvelocity, hdecay⟩ := Transport.regularizeKeeping hw
  have he : ∀ᵐ s, W s =ᵐ[volume] (fun y =>
      d.profile a.parameter ((d.period a.parameter)⁻¹ * s) y
        + a.correction ((d.period a.parameter)⁻¹ * s) y) := by
    filter_upwards [hraw] with s hs
    exact (hvelocity s).symm.trans hs
  refine ⟨W, q, C, hW, hdecay, ?_⟩
  have hP : d.period a.parameter ≠ 0 := a.sigma.period_pos.ne'
  have hscaled := (Breakdown.Internal.Rescale.quasiMeasurePreserving_mul (d.period a.parameter) hP).ae he
  filter_upwards [hscaled] with θ hθ
  filter_upwards [hθ] with y hy
  simpa only [inv_mul_cancel_left₀ hP] using hy

/-- Physical, identity-isometry profile with its original parameter and error field. -/
theorem HeldWitness.smooth {k : ℕ} {d : ExtendedCertificateData k}
    (a : HeldWitness d) :
    ∃ (W : VelField) (q : ℝ → Space → ℝ),
      IsIdentityProfile (d.period a.parameter) W q ∧
      ∀ᵐ θ, (fun y => W (d.period a.parameter * θ) y) =ᵐ[volume]
        (fun y => d.profile a.parameter θ y + a.correction θ y) := by
  obtain ⟨W, q, C, hs, hdecay, hraw⟩ := a.smoothWithData
  refine ⟨W, q, ?_, hraw⟩
  exact ⟨hs.period_pos, hs.smooth_field, hs.smooth_pressure, hs.residual, hs.divergence,
    fun s y => (hs.periodic s y).trans rfl, hs.nonzero, C, hdecay.1, hdecay.2⟩

end Breakdown.Theorem71
