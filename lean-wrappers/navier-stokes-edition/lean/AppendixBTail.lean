import Breakdown.CertCell.CellLayerPartProofs
import Breakdown.CertCell.TailExteriorLinks

open scoped ENNReal
open MeasureTheory
open Breakdown Breakdown.PieceWeights Breakdown.CertCell Breakdown.CertCell.TailBand
open Breakdown.CertCell.TailBand.Internal.ExteriorLinks

noncomputable section
namespace NavierStokes

/-- If a density is bounded below by a finite Hardy-controlled quadratic form,
its negative part has finite integral and its positive integral dominates it.
This retains a finiteness conclusion used, but not exported, by the authors'
exterior estimate. All integrals in this statement are nonnegative extended integrals. -/
theorem exteriorNegativeFiniteAndLe {μ : Measure (ℝ × ℝ)} {S V D : ℝ × ℝ → ℝ}
    {α γ c : ℝ} (hα : 0 ≤ α) (hγ : 0 ≤ γ) (hαγ : α ≤ γ * c)
    (hS0 : ∀ᵐ p ∂μ, 0 ≤ S p) (hV0 : ∀ᵐ p ∂μ, 0 ≤ V p)
    (hD : ∀ᵐ p ∂μ, γ * S p - α * V p ≤ D p)
    (hVm : AEMeasurable (fun p => ENNReal.ofReal (V p)) μ)
    (hinv : ENNReal.ofReal c * ∫⁻ p, ENNReal.ofReal (V p) ∂μ ≤
      ∫⁻ p, ENNReal.ofReal (S p) ∂μ)
    (hfin : ∫⁻ p, ENNReal.ofReal (S p) ∂μ < ⊤) :
    (∫⁻ p, ENNReal.ofReal (-D p) ∂μ) < ⊤ ∧
      ∫⁻ p, ENNReal.ofReal (-D p) ∂μ ≤ ∫⁻ p, ENNReal.ofReal (D p) ∂μ := by
  have hαV : ENNReal.ofReal α * ∫⁻ p, ENNReal.ofReal (V p) ∂μ ≤
      ENNReal.ofReal γ * ∫⁻ p, ENNReal.ofReal (S p) ∂μ := by
    calc ENNReal.ofReal α * ∫⁻ p, ENNReal.ofReal (V p) ∂μ
        ≤ ENNReal.ofReal γ * ENNReal.ofReal c * ∫⁻ p, ENNReal.ofReal (V p) ∂μ := by
          rw [← ENNReal.ofReal_mul hγ]
          gcongr
      _ = ENNReal.ofReal γ * (ENNReal.ofReal c * ∫⁻ p, ENNReal.ofReal (V p) ∂μ) := by rw [mul_assoc]
      _ ≤ ENNReal.ofReal γ * ∫⁻ p, ENNReal.ofReal (S p) ∂μ := by gcongr
  have hneg : ∫⁻ p, ENNReal.ofReal (-D p) ∂μ ≤
      ENNReal.ofReal α * ∫⁻ p, ENNReal.ofReal (V p) ∂μ := by
    calc ∫⁻ p, ENNReal.ofReal (-D p) ∂μ ≤ ∫⁻ p, ENNReal.ofReal (α * V p) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hS0, hD] with p hs hd
          apply ENNReal.ofReal_le_ofReal
          have hsγ : 0 ≤ γ * S p := mul_nonneg hγ hs
          linarith
      _ = ENNReal.ofReal α * ∫⁻ p, ENNReal.ofReal (V p) ∂μ := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          exact lintegral_congr fun p => ENNReal.ofReal_mul hα
  exact ⟨lt_of_le_of_lt (hneg.trans hαV) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin),
    lintegral_neg_le hα hγ hαγ hS0 hV0 hD hVm hinv hfin⟩

/-- Lemma B.6, exterior estimate: under the explicit regional coefficient and
Hardy hypotheses, the negative part of each charged modal density has finite
integral and its integral is at most that of the positive part. The ray case
requires a measurable directional radius bounded above and bounded away from
zero. The square case requires zero azimuthal frequency and the reflection
identity. The proof retains the finiteness estimate from the authors' argument. -/
theorem lemma_B_6_exterior :
  ∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (w₀ epsSup epsGradSup ratio : ℝ),
    CoerciveWeak.IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio →
    ∀ (mm : ℕ) (E : ExteriorCondition C nE nM), ∀ mc : ModeCharges, IsExteriorCondition m P h w mc mm E →
    ∀ (Γ : Set Symmetry) v G H g, IsPerturbation Γ P v G H g → ∀ ι ∈ E.modes,
      (∀ R : ℝ, E.region = planeSquareExterior R → labelAzimuth mm ι = 0 → IsFlipEven mm ι v) →
      (∫⁻ p in E.region, ENNReal.ofReal (-(offModeDensity m P h w mc E.charges mm ι v G H p * p.1))) < ⊤ ∧
      ∫⁻ p in E.region, ENNReal.ofReal (-(offModeDensity m P h w mc E.charges mm ι v G H p * p.1))
        ≤ ∫⁻ p in E.region, ENNReal.ofReal (offModeDensity m P h w mc E.charges mm ι v G H p * p.1) := by
  let hA : AngularModeBounds := angularModeBounds
  let hQ : PointwiseQuadraticTest := pointwiseQuadraticTest
  let hU : UniformCoefficientBounds := uniformCoefficientBounds
  let hF : LabelGradFinite := labelGradFinite
  let hR : ModeRayInverseSquare := modeRayInverseSquare
  let hS : ModeSquareInverseSquare := modeSquareInverseSquare_of_smooth squareExteriorSmoothStatement
  intro C nE nM m P h w W HW w₀ epsSup epsGradSup ratio hm mm E mc hE Γ v G H g hv ι hι hflip
  have hP : 0 < P := hm.period_pos
  have hk : E.pieces.azimuthLow ≤ |(labelAzimuth mm ι : ℝ)| := hE.pieces_valid.azimuth_ge ι hι
  have hhalf : MeasurableSet halfPlane := measurableSet_Ioi.prod measurableSet_Ioi
  have hZ : E.region ⊆ halfPlane ∧ MeasurableSet E.region := by
    rcases hE.shape with ⟨R, R₀, R₁, hRd, hreg, -⟩ | ⟨R, -, hreg, -, -⟩
    · rw [hreg]
      exact ⟨fun p hp => hp.1, hhalf.inter (measurableSet_lt hRd.measurable continuous_planeRadius.measurable)⟩
    · rw [hreg]
      exact ⟨fun p hp => hp.1, hhalf.inter ((measurableSet_lt measurable_const measurable_fst).union
        (measurableSet_lt measurable_const measurable_snd))⟩
  have hinv : ENNReal.ofReal E.inverseSquareConst
      * ∫⁻ p in E.region, ENNReal.ofReal (cnormSq (labelVel mm ι v p) / planeRadius p ^ 2 * p.1)
      ≤ ∫⁻ p in E.region, ENNReal.ofReal (cnormSq (labelGrad mm ι G p) * p.1) := by
    rcases hE.shape with ⟨R, R₀, R₁, hRd, hreg, hcle⟩ | ⟨R, hR0, hreg, hcle, hz⟩
    · have key := hR R R₀ R₁ hRd Γ P v G H g hv hP mm ι
      rw [← hreg] at key
      refine le_trans ?_ key
      gcongr
      refine hcle.trans ?_
      unfold rayInverseSquareConst
      have : max (E.pieces.azimuthLow - 1) 0 ≤ max (|(labelAzimuth mm ι : ℝ)| - 1) 0 :=
        max_le_max (by linarith) le_rfl
      have h0 : 0 ≤ max (E.pieces.azimuthLow - 1) 0 := le_max_right _ _
      nlinarith
    · have hz' := hz ι hι
      have key := hS R hR0 Γ P v G H g hv hP mm ι hz' (hflip R hreg hz')
      rw [← hreg] at key
      refine le_trans ?_ key
      gcongr
  have hfin : ∫⁻ p in E.region, ENNReal.ofReal (cnormSq (labelGrad mm ι G p) * p.1) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono_set hZ.1) (hF Γ P v G H g hv hP mm ι)
  have hVm : AEMeasurable (fun p => ENNReal.ofReal (cnormSq (labelVel mm ι v p) / planeRadius p ^ 2 * p.1))
      (volume.restrict E.region) := by
    have h1 := ((aestronglyMeasurable_labelFields hv mm ι).1).mono_measure (Measure.restrict_mono hZ.1 le_rfl)
    have h2 := (continuous_cnormSq.comp_aestronglyMeasurable h1).aemeasurable
    exact ((h2.div (continuous_planeRadius.measurable.pow_const 2).aemeasurable).mul
      measurable_fst.aemeasurable).ennreal_ofReal
  obtain ⟨hα, hαγ, hγ⟩ := coeff_facts hE.inverseSquareConst_pos hE.velHigh_nonneg hE.crossHigh_nonneg hE.test
  have hs : 0 < Real.sqrt E.inverseSquareConst := Real.sqrt_pos.2 hE.inverseSquareConst_pos
  have hang := ae_restrict_of_ae_restrict_of_subset hZ.1 (hA Γ P v G H g hv hP mm ι)
  have hmem := ae_restrict_mem (μ := volume) hZ.2
  refine exteriorNegativeFiniteAndLe hα hγ hαγ ?_ ?_ ?_ hVm hinv hfin
  · filter_upwards [hmem] with p hp
    exact mul_nonneg (cnormSq_nonneg _) (Set.mem_prod.mp (hZ.1 hp)).1.le
  · filter_upwards [hmem] with p hp
    exact mul_nonneg (div_nonneg (cnormSq_nonneg _) (sq_nonneg _)) (Set.mem_prod.mp (hZ.1 hp)).1.le
  · filter_upwards [hmem, hang] with p hp hpa
    have hr : 0 < p.1 := (Set.mem_prod.mp (hZ.1 hp)).1
    have hρ : 0 < planeRadius p := Real.sqrt_pos.2 (by positivity)
    obtain ⟨hsc, hcov⟩ := hE.charges_cover
    obtain ⟨h1, h2, h3, h4, h5⟩ := hcov ι hι p hp
    have hD := hU m P h w W HW w₀ epsSup epsGradSup ratio hm E.pieces mm E.modes E.region hE.pieces_valid ι hι p hp
    have hdom := dominates_withStretch (s := E.charges.stretchConst) (cc := E.charges.curlCharge p)
      (gc := E.charges.gradCharge p) (vc := E.charges.velCharge p) hD hsc h1 h2 h3 h4 h5
    have hcg : 0 ≤ (modeCoef m P h w mm ι p).curlGrad := by
      have := hm.conv_le (labelHarmonic mm ι) (planePoint p)
      simp only [modeCoef, PointCoef.ofMode, ModeCoefficients.ofPieces]
      linarith
    have hq := quad_lower hQ hr hρ hk hdom hcg (hE.hess_nonneg p hp) (hE.grad_floor p hp)
      (hE.vel_ceiling p hp) (hE.cross_ceiling p hp) hpa
    have hx := cross_le (x1 := Real.sqrt (cnormSq (labelGrad mm ι G p)))
      (x0 := Real.sqrt (cnormSq (labelVel mm ι v p))) hE.crossHigh_nonneg hρ hs
    rw [Real.sq_sqrt (cnormSq_nonneg _), Real.sq_sqrt (cnormSq_nonneg _)] at hq hx
    have hden : offModeDensity m P h w mc E.charges mm ι v G H p
        = ((modeCoef m P h w mm ι p).withStretch E.charges.stretchConst (mc.curl ι p) (mc.product ι p)
          (mc.gradient ι p) (mc.length ι p) (E.charges.curlCharge p) (E.charges.gradCharge p)
          (E.charges.velCharge p)).quad (Real.sqrt (cnormSq (labelHess mm ι H p)))
          (Real.sqrt (cnormSq (curlGradOfSecondDeriv (labelHess mm ι H p))))
          (Real.sqrt (cnormSq (labelGrad mm ι G p))) (Real.sqrt (cnormSq (curlOfGrad (labelGrad mm ι G p))))
          (Real.sqrt (cnormSq (labelVel mm ι v p))) := rfl
    have hpt : (E.gradLow - E.crossHigh / (2 * Real.sqrt E.inverseSquareConst)) * cnormSq (labelGrad mm ι G p)
        - (E.velHigh + E.crossHigh * Real.sqrt E.inverseSquareConst / 2)
          * (cnormSq (labelVel mm ι v p) / planeRadius p ^ 2) ≤ offModeDensity m P h w mc E.charges mm ι v G H p := by
      have e : (E.gradLow - E.crossHigh / (2 * Real.sqrt E.inverseSquareConst)) * cnormSq (labelGrad mm ι G p)
          - (E.velHigh + E.crossHigh * Real.sqrt E.inverseSquareConst / 2)
            * (cnormSq (labelVel mm ι v p) / planeRadius p ^ 2)
          = (E.gradLow * cnormSq (labelGrad mm ι G p) - E.velHigh / planeRadius p ^ 2 * cnormSq (labelVel mm ι v p))
            - (E.crossHigh / (2 * Real.sqrt E.inverseSquareConst) * cnormSq (labelGrad mm ι G p)
              + E.crossHigh * Real.sqrt E.inverseSquareConst / 2
                * (cnormSq (labelVel mm ι v p) / planeRadius p ^ 2)) := by ring
      rw [e, hden]
      linarith
    have := mul_le_mul_of_nonneg_right hpt hr.le
    calc _ = ((E.gradLow - E.crossHigh / (2 * Real.sqrt E.inverseSquareConst)) * cnormSq (labelGrad mm ι G p)
        - (E.velHigh + E.crossHigh * Real.sqrt E.inverseSquareConst / 2)
          * (cnormSq (labelVel mm ι v p) / planeRadius p ^ 2)) * p.1 := by ring
      _ ≤ _ := this

/-- Lemma B.6: the angular Hardy estimate on a ray exterior, followed by
finiteness and nonnegativity of the charged modal density under the stated
exterior conditions. A signed integral is read as positive integral minus
negative integral; the latter is finite. The ray radius hypotheses and the
square-exterior reflection condition are explicit in the two components. -/
theorem lemma_B_6 :
  (∀ (R : ℝ × ℝ → ℝ) (R₀ R₁ : ℝ), IsDirectionRadius R R₀ R₁ →
    ∀ (Γ : Set Symmetry) (P : ℝ) v G H g, IsPerturbation Γ P v G H g → 0 < P → ∀ (mm : ℕ) (ι : ℤ × ℤ),
      ENNReal.ofReal (rayInverseSquareConst |(labelAzimuth mm ι : ℝ)|)
          * ∫⁻ p in planeRayRegion R, ENNReal.ofReal (cnormSq (labelVel mm ι v p) / planeRadius p ^ 2 * p.1)
        ≤ ∫⁻ p in planeRayRegion R, ENNReal.ofReal (cnormSq (labelGrad mm ι G p) * p.1)) ∧
  (∀ {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (w₀ epsSup epsGradSup ratio : ℝ),
    CoerciveWeak.IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio →
    ∀ (mm : ℕ) (E : ExteriorCondition C nE nM), ∀ mc : ModeCharges, IsExteriorCondition m P h w mc mm E →
    ∀ (Γ : Set Symmetry) v G H g, IsPerturbation Γ P v G H g → ∀ ι ∈ E.modes,
      (∀ R : ℝ, E.region = planeSquareExterior R → labelAzimuth mm ι = 0 → IsFlipEven mm ι v) →
      (∫⁻ p in E.region, ENNReal.ofReal (-(offModeDensity m P h w mc E.charges mm ι v G H p * p.1))) < ⊤ ∧
      ∫⁻ p in E.region, ENNReal.ofReal (-(offModeDensity m P h w mc E.charges mm ι v G H p * p.1))
        ≤ ∫⁻ p in E.region, ENNReal.ofReal (offModeDensity m P h w mc E.charges mm ι v G H p * p.1)) := by
  exact ⟨modeRayInverseSquare, lemma_B_6_exterior⟩

end NavierStokes
