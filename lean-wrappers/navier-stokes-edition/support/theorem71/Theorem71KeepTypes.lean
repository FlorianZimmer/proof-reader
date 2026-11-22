/-
Theorem 7.1 witness-preserving interface.
Status: NOT COMPILED. Target: Lean 4.33.1, authors' ad53419.
This is the body of `WeakPeriodicSimilarityProfileExists` with its
existentially bound data made explicit. No existence is asserted here.
-/
import Breakdown.Defs

open MeasureTheory
open scoped ContDiff ENNReal

noncomputable section

namespace Breakdown.Theorem71

/-- The authors' weak-profile conditions for these particular witnesses. -/
def WeakProfileAt (W : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (P : ℝ) (R : Space ≃ₗᵢ[ℝ] Space) (C : ℝ) : Prop :=
  0 < P ∧
  AEStronglyMeasurable (fun z : ℝ × Space => W z.1 z.2) volume ∧
  AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume ∧
  AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume ∧
  (∀ s y, W (s + P) y = R (W s (R.symm y))) ∧
  (∀ s, IsWeakGradient (W s) (G s)) ∧
  (∀ᵐ s, ∀ j : Fin 3, IsWeakGradient (fun y => G s y (unitVector j))
    (fun y => (H s y).flip (unitVector j))) ∧
  (∀ s, ∀ᵐ y, ∑ i : Fin 3, (G s y (unitVector i)) i = 0) ∧
  (∀ s, ∫⁻ y, ENNReal.ofReal (‖W s y‖ ^ 6) ≤ ENNReal.ofReal C) ∧
  (∀ s, ∫⁻ y, ENNReal.ofReal (‖G s y‖ ^ 2) ≤ ENNReal.ofReal C) ∧
  (∫⁻ s in Set.Icc 0 P, ∫⁻ y, ENNReal.ofReal (‖H s y‖ ^ 2)) < ⊤ ∧
  (∀ φ, IsSpaceTimeTestField φ →
    Integrable (weakSimilarityIntegrand W G φ) ∧ ∫ z, weakSimilarityIntegrand W G φ z = 0) ∧
  ¬ (∀ᵐ z : ℝ × Space, W z.1 z.2 = 0)

/-- Forget the fixed weak field and period to obtain the authors' existential weak-profile premise. -/
theorem WeakProfileAt.forget {W : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {P C : ℝ} {R : Space ≃ₗᵢ[ℝ] Space} (h : WeakProfileAt W G H P R C) :
    WeakPeriodicSimilarityProfileExists :=
  ⟨W, G, H, P, R, C, h⟩

end Breakdown.Theorem71
