import PhysicalStatement
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The physical homogeneous H¹ norm under spatial scaling

The finiteness statement is carried alongside the norm identity. No decay
condition is imposed on the field. This is the change-of-variables step
needed to express a similarity-variable error in the original variables.
-/

open MeasureTheory

noncomputable section

namespace NavierStokes

/-- The three-dimensional velocity scaling x ↦ a f(ax), with a>0 in its
analytic uses. -/
def scaleVelocity (a : ℝ) (f : Theorem11.VectorField) : Theorem11.VectorField :=
  fun x => a • f (a • x)

/-- The Jacobian of x ↦ a f(ax) is a² times the Jacobian of f at ax. -/
theorem scaleVelocity_fderiv (a : ℝ) (f : Theorem11.VectorField) :
    fderiv ℝ (scaleVelocity a f) =
      fun x => (a * a) • fderiv ℝ f (a • x) := by
  have h : scaleVelocity a f = a • (fun x => f (a • x)) := rfl
  rw [h, fderiv_const_smul_field]
  funext x
  rw [Pi.smul_apply, fderiv_comp_smul, smul_smul]

/-- The squared Hilbert–Schmidt norm of the scaled Jacobian has factor a⁴. -/
theorem scaleVelocity_gradientSquare (a : ℝ) (f : Theorem11.VectorField)
    (x : Theorem11.Space) :
    Theorem11.gradientSquare (scaleVelocity a f) x =
      a ^ 4 * Theorem11.gradientSquare f (a • x) := by
  unfold Theorem11.gradientSquare
  rw [scaleVelocity_fderiv]
  simp only [smul_apply, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Scaling preserves finiteness of the physical homogeneous H¹ seminorm. -/
theorem finiteGradient_scaleVelocity (a : ℝ) (ha : 0 < a)
    (f : Theorem11.VectorField) (hf : Theorem11.FiniteGradient f) :
    Theorem11.FiniteGradient (scaleVelocity a f) := by
  have hi := (integrable_comp_smul_iff volume
    (Theorem11.gradientSquare f) ha.ne').2 hf
  change Integrable (fun x => Theorem11.gradientSquare (scaleVelocity a f) x) volume
  simp_rw [scaleVelocity_gradientSquare]
  exact hi.const_mul (a ^ 4)

/-- In dimension three, the integral of the squared gradient scales by a. -/
theorem gradientIntegral_scaleVelocity (a : ℝ) (ha : 0 < a)
    (f : Theorem11.VectorField) :
    (∫ x, Theorem11.gradientSquare (scaleVelocity a f) x) =
      a * ∫ x, Theorem11.gradientSquare f x := by
  simp_rw [scaleVelocity_gradientSquare]
  rw [integral_const_mul]
  have hi := Measure.integral_comp_smul_of_nonneg (volume : Measure Theorem11.Space)
    (Theorem11.gradientSquare f) a (hR := ha.le)
  rw [finrank_euclideanSpace_fin] at hi
  rw [hi, smul_eq_mul]
  field_simp [ha.ne']

/-- The homogeneous H¹ seminorm of x ↦ a f(ax) is √a times that of f. -/
theorem gradientNorm_scaleVelocity (a : ℝ) (ha : 0 < a)
    (f : Theorem11.VectorField) :
    Theorem11.gradientNorm (scaleVelocity a f) =
      Real.sqrt a * Theorem11.gradientNorm f := by
  unfold Theorem11.gradientNorm
  rw [gradientIntegral_scaleVelocity a ha, Real.sqrt_mul ha.le]

/-- Finiteness can also be recovered from the scaled field; the inverse
scaling uses the positive factor a⁻¹. -/
theorem finiteGradient_of_scaleVelocity (a : ℝ) (ha : 0 < a)
    (f : Theorem11.VectorField)
    (hf : Theorem11.FiniteGradient (scaleVelocity a f)) :
    Theorem11.FiniteGradient f := by
  have hi := finiteGradient_scaleVelocity a⁻¹ (inv_pos.2 ha) (scaleVelocity a f) hf
  have heq : scaleVelocity a⁻¹ (scaleVelocity a f) = f := by
    funext x
    simp only [scaleVelocity, smul_smul, mul_inv_cancel₀ ha.ne',
      inv_mul_cancel₀ ha.ne', one_smul]
  rwa [heq] at hi

/-- A quarter power is the square root of the spatial scaling factor. -/
theorem sqrt_sqrt_eq_quarter {μ : ℝ} (hμ : 0 < μ) :
    Real.sqrt (Real.sqrt μ) = μ ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hμ.le]
  norm_num

/-- Rescaling the physical error against (1.4) gives precisely the error
used in the supplied global whole-space theorem; its phase is preserved. -/
theorem scale_physical_error (u : Theorem11.Velocity)
    (W : Theorem11.Velocity) (t : ℝ) (ht : t < 1) :
    scaleVelocity (Real.sqrt (1 - t))
        (u t - Theorem11.comparisonField W 1 t) =
      Theorem11.rescaleAtOne u t - W (-Real.log (1 - t)) := by
  have hμ : 0 < 1 - t := sub_pos.2 ht
  have hc : Real.sqrt (1 - t) * (1 - t) ^ (-(1 / 2 : ℝ)) = 1 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hμ]
    norm_num
  have hc' : (1 - t) ^ (-(1 / 2 : ℝ)) * Real.sqrt (1 - t) = 1 := by
    rw [mul_comm, hc]
  have hlog : Real.log (1 / (1 - t)) = -Real.log (1 - t) := by
    rw [one_div, Real.log_inv]
  funext x
  simp only [scaleVelocity, Pi.sub_apply, Theorem11.comparisonField,
    Theorem11.rescaleAtOne, hlog, smul_sub, smul_smul,
    hc, hc', one_smul]

/-- The similarity error O((1-t)^κ) gives the physical gradient error
O((1-t)^(κ-1/4)); square-integrability is transported as well. No spatial
decay assumption on the constructed solution is used. -/
theorem physical_error_bound (u : Theorem11.Velocity)
    (W : Theorem11.Velocity) (t C κ : ℝ) (ht : t < 1)
    (hFinite : Theorem11.FiniteGradient
      (Theorem11.rescaleAtOne u t - W (-Real.log (1 - t))))
    (hError : Theorem11.gradientNorm
      (Theorem11.rescaleAtOne u t - W (-Real.log (1 - t))) ≤ C * (1 - t) ^ κ) :
    Theorem11.FiniteGradient (u t - Theorem11.comparisonField W 1 t) ∧
      Theorem11.gradientNorm (u t - Theorem11.comparisonField W 1 t) ≤
        C * (1 - t) ^ (κ - (1 / 4 : ℝ)) := by
  have hμ : 0 < 1 - t := sub_pos.2 ht
  have ha : 0 < Real.sqrt (1 - t) := Real.sqrt_pos.2 hμ
  have hScaled := scale_physical_error u W t ht
  have hFiniteScaled : Theorem11.FiniteGradient
      (scaleVelocity (Real.sqrt (1 - t))
        (u t - Theorem11.comparisonField W 1 t)) := by
    rw [hScaled]
    exact hFinite
  refine ⟨finiteGradient_of_scaleVelocity _ ha _ hFiniteScaled, ?_⟩
  have hNorm := gradientNorm_scaleVelocity (Real.sqrt (1 - t)) ha
    (u t - Theorem11.comparisonField W 1 t)
  rw [hScaled, sqrt_sqrt_eq_quarter hμ] at hNorm
  rw [hNorm] at hError
  have hp : 0 < (1 - t) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hμ _
  have hDiv : Theorem11.gradientNorm (u t - Theorem11.comparisonField W 1 t) ≤
      (C * (1 - t) ^ κ) / (1 - t) ^ (1 / 4 : ℝ) :=
    (le_div_iff₀ hp).2 (by simpa only [mul_comm] using hError)
  simpa only [Real.rpow_sub hμ, mul_div_assoc] using hDiv

/-- The supplied whole-space conclusion implies the printed physical error
formula (1.6), under the same formal profile assumptions. This changes only
the expression of the conclusion, not the hypotheses on the profile. -/
theorem paperSpaceConclusion_of_spaceConclusion (W : Theorem11.Velocity)
    (ε : ℝ) (h : Theorem11.SpaceConclusion W ε) :
    Theorem11.PaperSpaceConclusion W := by
  rcases h with ⟨u₀, u, p, c, C, κ, hs, hcpt, hd, _, _, hsol, henergy,
    hc, hcC, hκ, hκq, hrate, herror⟩
  refine ⟨u₀, u, p, c, C, κ, hs, hcpt, hd, hsol, henergy,
    hc, hcC, hκ, hκq, ?_⟩
  intro t ht
  obtain ⟨hfinite, hlo, hhi⟩ := hrate t ht
  obtain ⟨hefinite, hebound⟩ := herror t ht
  obtain ⟨hphysicalFinite, hphysicalBound⟩ :=
    physical_error_bound u W t C κ ht.2 hefinite hebound
  exact ⟨hfinite, hphysicalFinite, hlo, hhi, hphysicalBound⟩

/-- The physical error estimate holds for the very same global solution,
with the same constants, initial approximation, uniqueness and failure of
continuation as in the supplied whole-space proof. -/
theorem spacePhysicalBlowup_of_spaceBlowup (W : Theorem11.Velocity)
    (ε : ℝ) (h : Theorem11.SpaceBlowupConclusion W ε) :
    SpacePhysicalBlowupConclusion W ε := by
  rcases h with ⟨u₀, u, p, c, C, κ, hs, hcpt, hd, hf0, hclose, hsol,
    henergy, hc, hcC, hκ, hκq, hrate, herror, hunique, hno⟩
  refine ⟨u₀, u, p, c, C, κ, hs, hcpt, hd, hf0, hclose, hsol,
    henergy, hc, hcC, hκ, hκq, hrate, ?_, hunique, hno⟩
  intro t ht
  obtain ⟨hefinite, hebound⟩ := herror t ht
  exact physical_error_bound u W t C κ ht.2 hefinite hebound

end NavierStokes
