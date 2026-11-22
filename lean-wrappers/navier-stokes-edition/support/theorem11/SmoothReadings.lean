import SpaceCore
import Breakdown.Weak.VelocityWeakGradient

/-!
Status: IMPLEMENTED SOURCE, NOT YET COMPILED OR KERNEL CHECKED.

These proposed bridges derive classical gradient readings from a smooth
velocity representative. The implementation does not assume pointwise decay
or an H1-field premise. Its local physical estimates retain the same constants
for every compact time interval, subject to checking the source.
-/

open MeasureTheory Set Real Filter
open scoped ENNReal ContDiff Topology

noncomputable section

namespace Theorem11Core

open Breakdown Breakdown.Freq

theorem partial_reading_of_smooth (x : X) (f : Space → Space)
    (hf : ContDiff ℝ ∞ f)
    (hvel : (velocity x : Space → Space) =ᵐ[volume] f) (i : Fin 3) :
    (partialX i x : Space → Space) =ᵐ[volume]
      fun y => fderiv ℝ f y (unitVector i) := by
  have hdf : Continuous (fun y => fderiv ℝ f y (unitVector i)) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  refine ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (partialX i x)).locallyIntegrable (by first | exact one_le_two | norm_num))
    hdf.locallyIntegrable fun φ hφ hc => ?_
  calc
    (∫ y, φ y • (partialX i x : Space → Space) y)
        = -∫ y, fderiv ℝ φ y (unitVector i) • (velocity x : Space → Space) y :=
      Breakdown.WeakProfile.velocityWeakGradient_holds x φ ⟨hφ, hc⟩ i
    _ = -∫ y, fderiv ℝ φ y (unitVector i) • f y := by
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hvel] with y hy
      rw [hy]
    _ = ∫ y, φ y • fderiv ℝ f y (unitVector i) := by
      symm
      apply integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
      · exact (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).smul
          hf.continuous).integrable_of_hasCompactSupport
          ((hc.fderiv_apply (𝕜 := ℝ) (unitVector i)).smul_right)
      · exact (hφ.continuous.smul hdf).integrable_of_hasCompactSupport hc.smul_right
      · exact (hφ.continuous.smul hf.continuous).integrable_of_hasCompactSupport hc.smul_right
      · exact fun y _ => hφ.differentiable (by simp) y
      · exact fun y _ => hf.differentiable (by simp) y

theorem gradient_reading_of_smooth (x : X) (f : Space → Space)
    (hf : ContDiff ℝ ∞ f)
    (hvel : (velocity x : Space → Space) =ᵐ[volume] f) :
    Integrable (gradientSquare f) volume ∧ gradientNorm f = ‖x‖ :=
  gradient_reading x f (partial_reading_of_smooth x f hf hvel)

theorem smooth_dilateField (μ : ℝ) (f : Space → Space) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (dilateField μ f) := by
  have hs : ContDiff ℝ ∞ (fun y : Space => Real.sqrt μ • y) := contDiff_const_smul (Real.sqrt μ)
  have hc : ContDiff ℝ ∞ (fun y : Space => f (Real.sqrt μ • y)) := by
    first
    | exact hf.comp hs
    | fun_prop
  exact hc.const_smul (Real.sqrt μ)

theorem dilateField_ae {f g : Space → Space} (hfg : f =ᵐ[volume] g)
    {μ : ℝ} (hμ : 0 < μ) : dilateField μ f =ᵐ[volume] dilateField μ g := by
  have hmap : Measure.QuasiMeasurePreserving (fun y : Space => Real.sqrt μ • y)
      volume volume :=
    Measure.quasiMeasurePreserving_smul (μ := volume) (Real.sqrt_pos.2 hμ).ne'
  filter_upwards [hmap.ae_eq hfg] with y hy
  exact congrArg (fun v => Real.sqrt μ • v) hy

theorem rescaled_gradient_reading (x : X) (f g : Space → Space) (μ : ℝ)
    (hμ : 0 < μ) (hf : ContDiff ℝ ∞ f) (hg : IsDecayField g)
    (hvel : (velocity x : Space → Space) =ᵐ[volume] f) :
    Integrable (gradientSquare (dilateField μ f - g)) volume ∧
      gradientNorm (dilateField μ f - g) =
        ‖realization.F.D μ x - realization.embed g‖ := by
  have hdil : (velocity (realization.F.D μ x) : Space → Space) =ᵐ[volume]
      dilateField μ f :=
    (realization_fieldReading.dil μ hμ x).trans (dilateField_ae hvel hμ)
  have hgread : (velocity (realization.embed g) : Space → Space) =ᵐ[volume] g :=
    velocityDecay_holds g hg
  have hread : (velocity (realization.F.D μ x - realization.embed g) : Space → Space)
      =ᵐ[volume] dilateField μ f - g := by
    rw [map_sub]
    exact (Lp.coeFn_sub _ _).trans (hdil.sub hgread)
  exact gradient_reading_of_smooth _ _ ((smooth_dilateField μ f hf).sub hg.1) hread

/-- Physical estimates on every compact time slab, with the same datum,
profile, exponents, and constants for all slabs. The order of quantifiers
remains `forall T, exists U,p`; this theorem does not choose a global pressure. -/
theorem local_physical_quantitative (W : ℝ → Space → Space) (q : ℝ → Space → ℝ)
    (A ε : ℝ) (hprofile : IsSimilarityProfile W q A) (z : SpaceWitness W ε)
    (T : ℝ) (hT : 0 < T) (hT1 : T < 1) :
    ∃ (U : ℝ → Space → Space) (p : ℝ → Space → ℝ),
      IsSolutionOn T U p ∧ U 0 = z.datum ∧ EnergyBoundedOn T U ∧ GradientBoundedOn T U ∧
      (∀ t ∈ Icc (0 : ℝ) T, (velocity (z.state t) : Space → Space) =ᵐ[volume] U t) ∧
      ∀ t ∈ Icc (0 : ℝ) T,
        Integrable (gradientSquare (U t)) volume ∧
        gradientNorm (U t) = ‖z.state t‖ ∧
        z.lowerConstant * (1 - t) ^ (-(1 / 4 : ℝ)) ≤ gradientNorm (U t) ∧
        gradientNorm (U t) ≤ z.upperConstant * (1 - t) ^ (-(1 / 4 : ℝ)) ∧
        Integrable (gradientSquare (dilateField (1 - t) (U t) - W (-log (1 - t)))) volume ∧
        gradientNorm (dilateField (1 - t) (U t) - W (-log (1 - t))) ≤
          z.errorConstant * (1 - t) ^ z.exponent := by
  obtain ⟨U, p, hU, hinit, henergy, hgradient, hread⟩ := z.local_physical T hT hT1
  refine ⟨U, p, hU, hinit, henergy, hgradient, hread, ?_⟩
  intro t ht
  have ht1 : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1, ht.2.trans_lt hT1⟩
  have hsmooth := hU.contDiff_velocity ht
  obtain ⟨hfinite, hnorm⟩ := gradient_reading_of_smooth (z.state t) (U t) hsmooth (hread t ht)
  obtain ⟨herrfinite, herrnorm⟩ := rescaled_gradient_reading (z.state t) (U t)
    (W (-log (1 - t))) (1 - t) (by linarith [ht1.2]) hsmooth
    (sliceDecay_holds W q A hprofile _) (hread t ht)
  refine ⟨hfinite, hnorm, ?_, ?_, herrfinite, ?_⟩
  · rw [hnorm]
    exact (z.norm_rate t ht1).1
  · rw [hnorm]
    exact (z.norm_rate t ht1).2
  · rw [herrnorm]
    exact z.convergence t ht1

end Theorem11Core
