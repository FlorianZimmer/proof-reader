import Breakdown.Cert.ExtendedSigmaProfileOfHeld

open scoped ContDiff ENNReal
open MeasureTheory Filter
noncomputable section
namespace Breakdown.Cert

/-- The keeping statement: the reading `v, G, H` of the held correction is returned
together with the profile built from it. -/
def ExtendedSigmaProfileOfHeldKeep : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k), IsExtendedCertificate d →
    ∀ q ∈ d.params, ∀ f κ, d.IsHeldSolution q f κ → d.multiplier q + κ = 0 →
      ∃ v G H, IsReadingOf (freeInv (d.period q) f) v G H ∧
        ∃ C, IsSigmaProfile (d.period q) (fun σ y => d.profile q σ y + v σ y)
          (fun σ y => fderiv ℝ (d.profile q σ) y + G σ y)
          (fun σ y => d.profileSecondDeriv q σ y + H σ y) C

set_option maxHeartbeats 1600000 in
open Internal.ExtendedSigmaProfileOfHeld in
/-- Retain the selected correction and its weak derivative arrays when constructing the periodic weak profile; the proof uses the authors' public slice and held-solution lemmas. -/
theorem extendedSigmaProfileOfHeld_keep (h1 : SliceReadingHolds)
    (h2 : ExtendedHeldWeakEquationHolds) (h3 : ExtendedHeldNonzeroHolds) :
    ExtendedSigmaProfileOfHeldKeep := by
  intro k d hd q hq f κ hf hκ
  obtain ⟨v, G, H, hr, hgrad, hdiv, ⟨B, hB⟩, hH⟩ := h1 (d.period q) (hd.period_pos q hq) f
  have key : ∃ (P : ℝ) (W : VelField) (G' : GradField) (H' : SecondField) (C : ℝ),
      P = d.period q ∧ W = (fun σ y => d.profile q σ y + v σ y) ∧
      G' = (fun σ y => fderiv ℝ (d.profile q σ) y + G σ y) ∧
      H' = (fun σ y => d.profileSecondDeriv q σ y + H σ y) ∧ IsSigmaProfile P W G' H' C := by
    refine ⟨d.period q, fun σ y => d.profile q σ y + v σ y,
      fun σ y => fderiv ℝ (d.profile q σ) y + G σ y,
      fun σ y => d.profileSecondDeriv q σ y + H σ y,
      max (2 ^ 6 * (∫ y : Space, d.decay ^ 6 * (1 + ‖y‖) ^ (-(6 : ℝ))) + 2 ^ 6 * max B 0)
        (2 ^ 2 * (∫ y : Space, d.decay ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ))) + 2 ^ 2 * max B 0),
      rfl, rfl, rfl, rfl, ?_⟩
    exact
      { period_pos := hd.period_pos q hq
        measurable_velocity :=
          (profile_joint hd q).continuous.aestronglyMeasurable.add hr.measurable_velocity
        measurable_gradient := (measurable_fderiv_with_param ℝ (f := d.profile q)
          (profile_joint hd q).continuous).aestronglyMeasurable.add hr.measurable_gradient
        measurable_secondDeriv :=
          (hd.profileSecondDeriv_measurable q hq).add hr.measurable_second
        periodic := fun σ y => by
          rw [hd.profile_periodic q σ y, hr.periodic_velocity σ y]
        weak_gradient := fun σ => isWeakGradient_add
          (isWeakGradient_of_contDiff (profile_slice hd q σ)) (hgrad σ)
        weak_secondDeriv := by
          filter_upwards [hr.weak_second] with σ hσ j
          exact weak_secondDeriv_sum hd hq σ hσ j
        divergence_free := fun σ => divergence_sum hd hq σ (hdiv σ)
        sixth_power := fun σ =>
          (sixth_bound hd hq (fun σ => (hB σ).1) σ).trans
            (ENNReal.ofReal_le_ofReal (le_max_left _ _))
        gradient_bound := fun σ =>
          (grad_bound hd hq (fun σ => (hB σ).2) σ).trans
            (ENNReal.ofReal_le_ofReal (le_max_right _ _))
        secondDeriv_finite := secondDeriv_finite_of_period hd hq hH
        weak_equation := fun φ hφ => h2 d hd q hq f κ hf hκ v G H hr φ hφ
        nonzero := h3 d hd q hq f κ hf v G H hr }
  obtain ⟨P, W, G', H', C, rfl, rfl, rfl, rfl, hσ⟩ := key
  exact ⟨v, G, H, hr, C, hσ⟩


end Breakdown.Cert
