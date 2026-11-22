/-
# From an essential bound to an every-time gradient estimate

Status: NOT COMPILED. Target: Lean 4.33.1 / authors' ad53419.
The correction is C1 and has a uniform spatial derivative tail. Thus the
squared Frobenius-gradient integral is continuous in time by dominated
convergence. Its essential upper bound extends to every time because
Lebesgue measure has full support.
-/
import Breakdown.Cert.ExtendedAtProfile
import Breakdown.Cert.ExtendedSigmaProfileOfHeld
import Breakdown.Cert.ProductBound
import Breakdown.Cert.ReadingEnergy
import Breakdown.Cert.HalfOrderGraphMem

open MeasureTheory Filter
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Breakdown.Theorem71.Transport

open Cert

/-- The sum of the squared matrix entries is nonnegative. -/
theorem matSq_nonneg' (A : Space →L[ℝ] Space) : 0 ≤ matSq A :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- For a linear map on three-dimensional Euclidean space, its squared Frobenius norm is at most three times its squared operator norm. -/
theorem matSq_le_three_opNorm_sq (A : Space →L[ℝ] Space) :
    matSq A ≤ 3 * ‖A‖ ^ 2 := by
  calc
    matSq A ≤ ∑ i : Fin 3, ‖A‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      simpa [unitVector] using A.le_opNorm (unitVector i)
    _ = 3 * ‖A‖ ^ 2 := by simp

/-- A uniform, integrable dominator for the physical gradient density. -/
theorem gradient_density_bound {V : ℝ → Space → Space} {C : ℝ}
    (hdec : ∀ σ y, ‖fderiv ℝ (V σ) y‖ ≤ C / (1 + ‖y‖) ^ 2)
    (σ : ℝ) (y : Space) :
    ‖matSq (fderiv ℝ (V σ) y)‖ ≤
      3 * C ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) := by
  rw [Real.norm_eq_abs, abs_of_nonneg (matSq_nonneg' _)]
  have hsq : ‖fderiv ℝ (V σ) y‖ ^ 2 ≤ C ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) :=
    Cert.Internal.ExtendedSigmaProfileOfHeld.pow_le_of_decay 2 2
      (norm_nonneg _) (norm_nonneg _) (by norm_num) (hdec σ y)
  calc
    matSq (fderiv ℝ (V σ) y) ≤ 3 * ‖fderiv ℝ (V σ) y‖ ^ 2 :=
      matSq_le_three_opNorm_sq _
    _ ≤ 3 * (C ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ))) :=
      mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = _ := by ring

/-- The fourth-power radial weight used to dominate the gradient density is integrable on three-dimensional space. -/
theorem gradient_dominator_integrable (C : ℝ) :
    Integrable (fun y : Space => 3 * C ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ))) := by
  have h : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(4 : ℝ))) :=
    integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; norm_num)
  exact h.const_mul (3 * C ^ 2)

/-- Joint C1 regularity and the r^-2 derivative tail make the actual squared
homogeneous H1 norm continuous; pointwise smoothness alone is not used as a
substitute for this integral argument. -/
theorem gradient_integral_continuous {V : ℝ → Space → Space} {C : ℝ}
    (hC1 : ContDiff ℝ 1 (fun z : ℝ × Space => V z.1 z.2))
    (hdec : ∀ σ y, ‖fderiv ℝ (V σ) y‖ ≤ C / (1 + ‖y‖) ^ 2) :
    Continuous (fun σ => ∫ y, matSq (fderiv ℝ (V σ) y)) := by
  have hG := Cert.Internal.AtProfile.continuous_fderiv_slice hC1
  have hF : Continuous (fun z : ℝ × Space => matSq (fderiv ℝ (V z.1) z.2)) :=
    Cert.Internal.ReadingEnergy.continuous_matSq.comp hG
  have hspace : ∀ σ : ℝ, Continuous (fun y : Space => matSq (fderiv ℝ (V σ) y)) := by
    intro σ
    have h1 : Continuous fun y : Space => ((σ, y) : ℝ × Space) := by fun_prop
    have h := hF.comp h1
    exact h
  have htime : ∀ y : Space, Continuous (fun σ : ℝ => matSq (fderiv ℝ (V σ) y)) := by
    intro y
    have h1 : Continuous fun σ : ℝ => ((σ, y) : ℝ × Space) := by fun_prop
    have h := hF.comp h1
    exact h
  exact continuous_of_dominated
    (fun σ => (hspace σ).aestronglyMeasurable)
    (fun σ => ae_of_all _ (gradient_density_bound hdec σ))
    (gradient_dominator_integrable C)
    (ae_of_all _ htime)

/-- A reading's essential gradient bound holds at every time for a C1
representative with the stated uniform derivative decay. -/
theorem gradient_bound_everywhere {u : XX} {V : VelField} {H : SecondField} {M C : ℝ}
    (hr : IsReadingOf u V (fun σ y => fderiv ℝ (V σ) y) H)
    (hC1 : ContDiff ℝ 1 (fun z : ℝ × Space => V z.1 z.2))
    (hdec : ∀ σ y, ‖fderiv ℝ (V σ) y‖ ≤ C / (1 + ‖y‖) ^ 2)
    (hM : 0 ≤ M) (hsup : supGrad u ≤ ENNReal.ofReal M) :
    ∀ σ, ∫ y, matSq (fderiv ℝ (V σ) y) ≤ M ^ 2 := by
  have hfin : supGrad u < ⊤ := lt_of_le_of_lt hsup ENNReal.ofReal_lt_top
  have hsupR : (supGrad u).toReal ≤ M := by
    simpa [ENNReal.toReal_ofReal hM] using
      ENNReal.toReal_mono (ENNReal.ofReal_ne_top : ENNReal.ofReal M ≠ ⊤) hsup
  have htime := (Cert.ae_coe_iff _).1
    (Cert.Internal.ProductBound.ae_norm_le_supGrad hfin)
  have hae : ∀ᵐ σ : ℝ, (∫ y, matSq (fderiv ℝ (V σ) y)) ≤ M ^ 2 := by
    filter_upwards [hr.velocity_eq, hr.weak_gradient, htime] with σ hv hg hb
    have he := Cert.Internal.ReadingEnergy.matSq_ae
      (fun q => Cert.halfSsp_of_xbar q)
      ((u : TimeCircle → XBar) (σ : TimeCircle)) hv hg
    rw [integral_congr_ae he, Cert.Internal.ReadingEnergy.integral_sum_partialX]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb.trans hsupR) 2
  have hcont := gradient_integral_continuous hC1 hdec
  have hmin : (fun σ : ℝ => min (∫ y, matSq (fderiv ℝ (V σ) y)) (M ^ 2)) =
      (fun σ : ℝ => ∫ y, matSq (fderiv ℝ (V σ) y)) := by
    apply ((hcont.min continuous_const).ae_eq_iff_eq volume hcont).mp
    filter_upwards [hae] with σ hσ
    exact min_eq_left hσ
  intro σ
  have h : min (∫ y, matSq (fderiv ℝ (V σ) y)) (M ^ 2) = ∫ y, matSq (fderiv ℝ (V σ) y) :=
    congrFun hmin σ
  rw [← h]
  exact min_le_right _ _

/-- ENNReal form used in the public statement: it also certifies finiteness. -/
theorem gradient_lintegral_bound_everywhere {u : XX} {V : VelField}
    {H : SecondField} {M C : ℝ}
    (hr : IsReadingOf u V (fun σ y => fderiv ℝ (V σ) y) H)
    (hC1 : ContDiff ℝ 1 (fun z : ℝ × Space => V z.1 z.2))
    (hdec : ∀ σ y, ‖fderiv ℝ (V σ) y‖ ≤ C / (1 + ‖y‖) ^ 2)
    (hM : 0 ≤ M) (hsup : supGrad u ≤ ENNReal.ofReal M) :
    ∀ σ, ∫⁻ y, ENNReal.ofReal (matSq (fderiv ℝ (V σ) y)) ≤ ENNReal.ofReal (M ^ 2) := by
  have hG := Cert.Internal.AtProfile.continuous_fderiv_slice hC1
  have hF : Continuous (fun z : ℝ × Space => matSq (fderiv ℝ (V z.1) z.2)) :=
    Cert.Internal.ReadingEnergy.continuous_matSq.comp hG
  intro σ
  have hspace : Continuous (fun y : Space => matSq (fderiv ℝ (V σ) y)) := by
    have h1 : Continuous fun y : Space => ((σ, y) : ℝ × Space) := by fun_prop
    have h := hF.comp h1
    exact h
  have hint : Integrable (fun y => matSq (fderiv ℝ (V σ) y)) :=
    (gradient_dominator_integrable C).mono' hspace.aestronglyMeasurable
      (ae_of_all _ (gradient_density_bound hdec σ))
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun y => matSq_nonneg' _)]
  exact ENNReal.ofReal_le_ofReal (gradient_bound_everywhere hr hC1 hdec hM hsup σ)

end Breakdown.Theorem71.Transport
