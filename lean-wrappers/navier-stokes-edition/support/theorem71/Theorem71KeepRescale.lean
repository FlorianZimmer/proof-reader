import Theorem71KeepTypes
import Breakdown.Cert.Rescale

open scoped ContDiff ENNReal
open MeasureTheory
noncomputable section
namespace Breakdown

open Internal.Rescale in
/-- Rescale normalized time to similarity time while preserving this field, its exact positive period and the identity isometry. -/
theorem weakPeriodicSimilarityProfileOf_sigma_keep {P C : ℝ} {W : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (h : IsSigmaProfile P W G H C) :
    Theorem71.WeakProfileAt (fun s y => W (P⁻¹ * s) y)
      (fun s y => G (P⁻¹ * s) y) (fun s y => H (P⁻¹ * s) y)
      P (LinearIsometryEquiv.refl ℝ Space) C := by
  have hP := h.period_pos
  have hP0 : P ≠ 0 := hP.ne'
  have hPi : P⁻¹ ≠ 0 := inv_ne_zero hP0
  refine ⟨hP, ?_, ?_, ?_, ?_, fun s => h.weak_gradient _,
    ?_, fun s => h.divergence_free _, fun s => h.sixth_power _, fun s => h.gradient_bound _,
    ?_, ?_, ?_⟩
  · exact h.measurable_velocity.comp_quasiMeasurePreserving (quasiMeasurePreserving_timeScale _ hPi)
  · exact h.measurable_gradient.comp_quasiMeasurePreserving (quasiMeasurePreserving_timeScale _ hPi)
  · exact h.measurable_secondDeriv.comp_quasiMeasurePreserving (quasiMeasurePreserving_timeScale _ hPi)
  · intro s y
    have hs : P⁻¹ * (s + P) = P⁻¹ * s + 1 := by rw [mul_add, inv_mul_cancel₀ hP0]
    simp only [hs, h.periodic]
    rfl
  · exact (quasiMeasurePreserving_mul _ hPi).ae h.weak_secondDeriv
  · rw [setLIntegral_Icc_inv_mul hP (fun σ => ∫⁻ y, ENNReal.ofReal (‖H σ y‖ ^ 2))]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h.secondDeriv_finite
  · intro φ hφ
    have hψ := h.weak_equation _ (isSpaceTimeTestField_comp hP0 hφ)
    have hfun : weakSimilarityIntegrand (fun s y => W (P⁻¹ * s) y) (fun s y => G (P⁻¹ * s) y) φ
        = fun z => sigmaSimilarityIntegrand P W G (fun σ y => φ (P * σ) y) (P⁻¹ * z.1, z.2) :=
      funext (weakSimilarityIntegrand_eq hP0 W G φ)
    rw [hfun, integrable_timeScale_iff _ hPi, integral_timeScale _ hPi, hψ.2, mul_zero]
    exact ⟨hψ.1, rfl⟩
  · intro hW
    apply h.nonzero
    filter_upwards [(quasiMeasurePreserving_timeScale P hP0).ae hW] with z hz
    simpa [inv_mul_cancel_left₀ hP0] using hz


end Breakdown
