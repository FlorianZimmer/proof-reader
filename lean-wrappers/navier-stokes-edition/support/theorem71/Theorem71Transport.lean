/-
# Preserving a certificate correction under regularization

Status: NOT COMPILED. Target: Lean 4.33.1 / authors' ad53419.
This file contains new composition and representative-transport lemmas.
The approximate field is only C1, so the weak second derivative is retained.
No classical second differentiability of the approximate field is assumed.
-/
import Breakdown.Cert.ExtendedSigmaProfileOfHeld
import Breakdown.Cert.ExtendedAtProfile
import Breakdown.Cert.Rescale
import Breakdown.Cert.ProductBound
import Breakdown.Cert.ReadingEnergy
import Breakdown.Cert.CoercivePieceDensityPassageLimit
import Breakdown.CertTorus.Main

open MeasureTheory Filter
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Breakdown.Theorem71.Transport

open Cert Freq

/-- The regularization and decay theorems can be composed without discarding
the input orbit, its period or its isometry. -/
theorem regularizeKeeping {w : ℝ → X} {P : ℝ} {R : Space ≃ₗᵢ[ℝ] Space}
    (hw : realization.F.IsOrbit (realization.rot R) w P) :
    ∃ (W : VelField) (q : ℝ → Space → ℝ) (C : ℝ),
      FarField.IsSmoothOrbitField W q P R ∧
      FarField.IsVelocityOf w W ∧ FarField.DecayBounds W q C := by
  obtain ⟨W, q, hS, hV⟩ := FarField.smoothFieldOfOrbit_holds w P R hw
  have hI := FarField.integralEquationOfOrbit_holds w P R W q hw hS hV
  obtain ⟨C, hC⟩ := FarField.farFieldDecay_holds W q P R
    (FarField.isRegularOrbitField_of_smooth hS hI)
  exact ⟨W, q, C, hS, hV, hC⟩

/-- Normalizing time is nonsingular because the period is nonzero. -/
theorem normalized_error_ae {P : ℝ} (hP : P ≠ 0) {A V W : VelField}
    (he : ∀ᵐ s : ℝ, W s =ᵐ[volume]
      fun y => A (P⁻¹ * s) y + V (P⁻¹ * s) y) :
    ∀ᵐ θ : ℝ, (fun y => W (P * θ) y - A θ y) =ᵐ[volume] V θ := by
  filter_upwards [(Breakdown.Internal.Rescale.quasiMeasurePreserving_mul P hP).ae he]
    with θ hθ
  filter_upwards [hθ] with y hy
  simp only [inv_mul_cancel_left₀ hP] at hy
  show W (P * θ) y - A θ y = V θ y
  rw [hy]
  abel

/-- A change to a C1 representative changes neither weak derivatives nor the
abstract correction. The weak Hessian is kept verbatim. -/
theorem reading_of_C1_representative {u : XX} {v V : VelField}
    {G : GradField} {H : SecondField} (hr : IsReadingOf u v G H)
    (hV : ContDiff ℝ 1 (fun z : ℝ × Space => V z.1 z.2))
    (hper : IsTimePeriodic V)
    (he : ∀ᵐ σ : ℝ, V σ =ᵐ[volume] v σ) :
    IsReadingOf u V (fun σ y => fderiv ℝ (V σ) y) H := by
  have hs : ∀ σ, ContDiff ℝ 1 (V σ) := fun σ =>
    hV.comp (contDiff_const.prodMk contDiff_id)
  have hweak : ∀ σ, IsWeakGradient (V σ) (fderiv ℝ (V σ)) := fun σ =>
    Cert.Internal.ExtendedSigmaProfileOfHeld.isWeakGradient_of_contDiff (hs σ)
  have hgrad : ∀ᵐ σ : ℝ, fderiv ℝ (V σ) =ᵐ[volume] G σ := by
    filter_upwards [hr.weak_gradient, he] with σ hg hσ
    exact Cert.Internal.ProductBound.weakGradient_unique (hweak σ)
      (Cert.Internal.ReadingExists.isWeakGradient_congr hg hσ.symm EventuallyEq.rfl)
  refine
    { measurable_velocity := hV.continuous.aestronglyMeasurable
      measurable_gradient :=
        (Cert.Internal.AtProfile.continuous_fderiv_slice hV).aestronglyMeasurable
      measurable_second := hr.measurable_second
      periodic_velocity := hper
      periodic_gradient := ?_
      periodic_second := hr.periodic_second
      velocity_eq := ?_
      weak_gradient := ae_of_all _ hweak
      weak_second := ?_
      trace_eq := hr.trace_eq }
  · intro σ y
    have hfun : V (σ + 1) = V σ := funext (hper σ)
    show fderiv ℝ (V (σ + 1)) y = fderiv ℝ (V σ) y
    rw [hfun]
  · filter_upwards [he, hr.velocity_eq] with σ hσ hv
    exact hσ.trans hv
  · filter_upwards [hgrad, hr.weak_second] with σ hg hh
    intro j
    exact Cert.Internal.ReadingExists.isWeakGradient_congr (hh j)
      (hg.symm.mono fun y hy => congrArg (fun L : Space →L[ℝ] Space => L (unitVector j)) hy)
      EventuallyEq.rfl

/-- Smooth exact field minus a C1 approximate field is C1 in normalized time. -/
theorem normalized_error_C1 {P : ℝ} {A W : VelField}
    (hW : ContDiff ℝ ∞ (fun z : ℝ × Space => W z.1 z.2))
    (hA : ContDiff ℝ 1 (fun z : ℝ × Space => A z.1 z.2)) :
    ContDiff ℝ 1 (fun z : ℝ × Space => W (P * z.1) z.2 - A z.1 z.2) := by
  have hW1 : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2) :=
    hW.of_le (by exact_mod_cast le_top)
  exact (hW1.comp ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd)).sub hA

/-- Normalizing a profile of period P to time theta makes its difference from a period-one approximate profile periodic with period one. -/
theorem normalized_error_periodic {P : ℝ} {A W : VelField}
    (hW : ∀ s y, W (s + P) y = W s y) (hA : IsTimePeriodic A) :
    IsTimePeriodic (fun σ y => W (P * σ) y - A σ y) := by
  intro σ y
  show W (P * (σ + 1)) y - A (σ + 1) y = W (P * σ) y - A σ y
  rw [show P * (σ + 1) = P * σ + P by ring, hW, hA σ y]

/-- The two available derivative tails give a single integrable dominator for
the correction's squared gradient. -/
theorem normalized_error_gradient_decay {P C D : ℝ} {A W : VelField}
    (hW : ContDiff ℝ ∞ (fun z : ℝ × Space => W z.1 z.2))
    (hA : ContDiff ℝ 1 (fun z : ℝ × Space => A z.1 z.2))
    (hWd : ∀ s y, ‖fderiv ℝ (W s) y‖ ≤ C / (1 + ‖y‖) ^ 2)
    (hAd : ∀ σ y, ‖fderiv ℝ (A σ) y‖ ≤ D / (1 + ‖y‖) ^ 2) :
    ∀ σ y, ‖fderiv ℝ (fun x => W (P * σ) x - A σ x) y‖
      ≤ (C + D) / (1 + ‖y‖) ^ 2 := by
  intro σ y
  have hW1 : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2) :=
    hW.of_le (by exact_mod_cast le_top)
  have hWs : ContDiff ℝ 1 (W (P * σ)) :=
    hW1.comp (contDiff_const.prodMk contDiff_id)
  have hAs : ContDiff ℝ 1 (A σ) :=
    hA.comp (contDiff_const.prodMk contDiff_id)
  rw [fderiv_fun_sub (hWs.differentiable one_ne_zero y) (hAs.differentiable one_ne_zero y)]
  calc
    ‖fderiv ℝ (W (P * σ)) y - fderiv ℝ (A σ) y‖
      ≤ ‖fderiv ℝ (W (P * σ)) y‖ + ‖fderiv ℝ (A σ) y‖ := norm_sub_le _ _
    _ ≤ C / (1 + ‖y‖) ^ 2 + D / (1 + ‖y‖) ^ 2 := add_le_add (hWd _ _) (hAd _ _)
    _ = (C + D) / (1 + ‖y‖) ^ 2 := (add_div _ _ _).symm

/-- Each fixed symmetry is promoted separately. No intersection of exceptional
sets over an uncountable symmetry group is taken. -/
theorem invariant_everywhere {Γ : Set Symmetry} {V : VelField}
    (hV : Continuous (fun z : ℝ × Space => V z.1 z.2))
    (hinv : ∀ γ ∈ Γ, ∀ᵐ z : ℝ × Space,
      V (z.1 + γ.2) (γ.1 z.2) = γ.1 (V z.1 z.2)) :
    ∀ γ ∈ Γ, ∀ σ y, V (σ + γ.2) (γ.1 y) = γ.1 (V σ y) := by
  intro γ hγ σ y
  have hL : Continuous (fun z : ℝ × Space => V (z.1 + γ.2) (γ.1 z.2)) :=
    hV.comp ((continuous_fst.add continuous_const).prodMk (γ.1.continuous.comp continuous_snd))
  have hR : Continuous (fun z : ℝ × Space => γ.1 (V z.1 z.2)) := γ.1.continuous.comp hV
  exact congrFun ((hL.ae_eq_iff_eq volume hR).mp (hinv γ hγ)) (σ, y)

/-- Recombine the approximate field and correction, and undo normalized time. -/
theorem physical_symmetry {P : ℝ} (hP : P ≠ 0) {A W : VelField}
    {R : Space ≃ₗᵢ[ℝ] Space} {τ : ℝ}
    (hA : ∀ σ y, A (σ + τ) (R y) = R (A σ y))
    (hV : ∀ σ y,
      W (P * (σ + τ)) (R y) - A (σ + τ) (R y) =
        R (W (P * σ) y - A σ y)) :
    ∀ s y, W (s + τ * P) (R y) = R (W s y) := by
  intro s y
  have he := hV (P⁻¹ * s) y
  have ht : P * (P⁻¹ * s) = s := by rw [← mul_assoc, mul_inv_cancel₀ hP, one_mul]
  have ht' : P * (P⁻¹ * s + τ) = s + τ * P := by rw [mul_add, ht, mul_comm P τ]
  rw [ht', ht, hA, map_sub] at he
  have he' := congrArg (fun z : Space => z + R (A (P⁻¹ * s) y)) he
  simpa only [sub_add_cancel] using he'

/-- Finiteness is proved before reading an extended integral with toReal. -/
theorem weighted_integral_finite {Γ : Set Symmetry} {P : ℝ}
    {v : VelField} {G : GradField} {H : SecondField} {g : VelField}
    (hv : IsPerturbation Γ P v G H g) {w : Space → ℝ} {w₀ : ℝ}
    (hw : IsAdmissibleWeight w w₀) :
    periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y)) < ⊤ := by
  have hmT : AEMeasurable (fun z : ℝ × Space => ‖secondDerivTrace (H z.1 z.2)‖ ^ 2) volume :=
    ((Coercive.Internal.PassageLimit.continuous_secondDerivTrace.comp_aestronglyMeasurable
      hv.measurable_secondDeriv).norm.pow 2).aemeasurable
  have hmG : AEMeasurable (fun z : ℝ × Space => matSq (G z.1 z.2)) volume :=
    (Cert.Internal.ReadingEnergy.continuous_matSq.comp_aestronglyMeasurable
      hv.measurable_gradient).aemeasurable
  have hmw : AEMeasurable (fun z : ℝ × Space => w z.2) volume :=
    (hw.2.1.comp measurable_snd).aemeasurable
  have hnonneg : ∀ y, 0 ≤ w y := fun y => hw.1.le.trans (hw.2.2.1 y)
  obtain ⟨B, hB⟩ := hw.2.2.2
  rw [Coercive.Internal.PassageLimit.periodLIntegral_add
    (f := fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2) (g := fun σ y => w y * matSq (G σ y))
    hmT (hmw.mul hmG)
    (fun _ _ => sq_nonneg _) (fun σ y => mul_nonneg (hnonneg y)
      (Finset.sum_nonneg fun i _ => sq_nonneg _))]
  refine ENNReal.add_lt_top.2 ⟨hv.sumSecondPartials_finite, ?_⟩
  apply lt_of_le_of_lt (Coercive.Internal.PassageLimit.periodLIntegral_le_mul
    (f := fun σ y => w y * matSq (G σ y)) (g := fun σ y => matSq (G σ y))
    (C := max B 0) (le_max_right _ _) (fun σ y =>
      mul_le_mul_of_nonneg_right ((hB y).trans (le_max_left _ _))
        (Finset.sum_nonneg fun i _ => sq_nonneg _)))
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hv.gradient_finite

end Breakdown.Theorem71.Transport
