import Theorem11Challenge

/-! # The physical whole-space conclusion, with the same selected solution -/

open Set
open scoped ContDiff

noncomputable section

namespace NavierStokes

/-- The whole-space conclusion (1.6), with the selected profile W and the
same datum and solution retained throughout: compactly supported smooth
divergence-free datum within ε of W(0) in the homogeneous H¹ seminorm; one
smooth, uniformly finite-energy solution on [0,1); the two-sided gradient
rate; the physical error against (1.4); uniqueness among smooth solutions
with uniformly finite energy before time 1; and no such continuation through
time 1. Every real-valued gradient norm is accompanied by integrability. -/
def SpacePhysicalBlowupConclusion (W : Theorem11.Velocity) (ε : ℝ) : Prop :=
  ∃ (u₀ : Theorem11.VectorField) (u : Theorem11.Velocity)
      (p : Theorem11.Pressure) (c C κ : ℝ),
    ContDiff ℝ ∞ u₀ ∧ HasCompactSupport u₀ ∧
    (∀ x, Theorem11.divergenceAt u₀ x = 0) ∧
    Theorem11.FiniteGradient (u₀ - W 0) ∧
    Theorem11.gradientNorm (u₀ - W 0) < ε ∧
    Theorem11.IsSmoothSolutionBefore 1 1 u₀ u p ∧
    Theorem11.UniformFiniteEnergyBefore 1 u ∧
    0 < c ∧ c ≤ C ∧ 0 < κ ∧ κ < (1 / 4 : ℝ) ∧
    (∀ t ∈ Ico (0 : ℝ) 1,
      Theorem11.FiniteGradient (u t) ∧
      c * (1 - t) ^ (-(1 / 4 : ℝ)) ≤ Theorem11.gradientNorm (u t) ∧
      Theorem11.gradientNorm (u t) ≤ C * (1 - t) ^ (-(1 / 4 : ℝ))) ∧
    (∀ t ∈ Ico (0 : ℝ) 1,
      Theorem11.FiniteGradient (u t - Theorem11.comparisonField W 1 t) ∧
      Theorem11.gradientNorm (u t - Theorem11.comparisonField W 1 t) ≤
        C * (1 - t) ^ (κ - (1 / 4 : ℝ))) ∧
    (∀ T : ℝ, T ≤ 1 → ∀ (v : Theorem11.Velocity) (q : Theorem11.Pressure),
      Theorem11.IsSmoothSolutionBefore 1 T u₀ v q →
      Theorem11.UniformFiniteEnergyBefore T v →
      ∀ t ∈ Ico (0 : ℝ) T, v t = u t) ∧
    ¬ ∃ (v : Theorem11.Velocity) (q : Theorem11.Pressure),
      Theorem11.IsSmoothSolutionThrough 1 1 u₀ v q ∧
      Theorem11.UniformFiniteEnergyThrough 1 v

end NavierStokes
