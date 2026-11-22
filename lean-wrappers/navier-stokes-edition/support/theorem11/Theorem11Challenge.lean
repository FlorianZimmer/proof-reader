/-
# Physical statement contracts for Theorem 1.1

Status: COMPILED with Lean v4.33.1 at the packet Mathlib pin. No endpoint theorem is declared
in this file. The declarations below are mathematical propositions, not proofs
that the propositions hold. This is an independent Mathlib-only statement file.

The main requested contract, `Theorem11.Theorem11Space`, uses the explicit
profile assumptions of the authors' Challenge.lean and retains the selected
profile. `PaperTheorem11Space` and `PaperTheorem11Torus` record the printed
hypotheses and Eulerian error bounds. They are deliberately separate.
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open MeasureTheory Set
open scoped ContDiff ENNReal

noncomputable section

namespace Theorem11

abbrev Space := EuclideanSpace ℝ (Fin 3)
abbrev VectorField := Space → Space
abbrev Velocity := ℝ → VectorField
abbrev Pressure := ℝ → Space → ℝ

/-- The coordinate vectors of the fixed Euclidean frame. -/
def unitVector (i : Fin 3) : Space := EuclideanSpace.single i 1

def divergenceAt (v : VectorField) (x : Space) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ v x (unitVector i)) i

def laplacianAt (v : VectorField) (x : Space) : Space :=
  ∑ i : Fin 3, iteratedFDeriv ℝ 2 v x ![unitVector i, unitVector i]

def pressureGradientAt (p : Space → ℝ) (x : Space) : Space :=
  ∑ i : Fin 3, fderiv ℝ p x (unitVector i) • unitVector i

def advectionAt (v : VectorField) (x : Space) : Space :=
  fderiv ℝ v x (v x)

/-- Squared Hilbert--Schmidt norm of the Jacobian, not its operator norm. -/
def gradientSquare (v : VectorField) (x : Space) : ℝ :=
  ∑ i : Fin 3, ‖fderiv ℝ v x (unitVector i)‖ ^ 2

/-- Required wherever `gradientNorm` is used in a conclusion. -/
def FiniteGradient (v : VectorField) : Prop :=
  Integrable (gradientSquare v) volume

/-- The physical homogeneous H¹ seminorm; conclusions also require finiteness. -/
def gradientNorm (v : VectorField) : ℝ :=
  Real.sqrt (∫ x, gradientSquare v x)

/-- Squared H¹ density, including the velocity itself. -/
def h1Square (v : VectorField) (x : Space) : ℝ :=
  ‖v x‖ ^ 2 + gradientSquare v x

/-- Explicit guard against a totalized Bochner integral at every H¹ norm use. -/
def FiniteH1On (v : VectorField) (Ω : Set Space) : Prop :=
  Integrable (h1Square v) (volume.restrict Ω)

def h1NormOn (v : VectorField) (Ω : Set Space) : ℝ :=
  Real.sqrt (∫ x in Ω, h1Square v x)

/-- The unit periodic cell, with boundary choices immaterial to its integrals. -/
def unitCell : Set Space := {x | ∀ i : Fin 3, 0 ≤ x i ∧ x i ≤ 1}

def PeriodicField (v : VectorField) : Prop :=
  ∀ i x, v (x + unitVector i) = v x

def PeriodicScalar (p : Space → ℝ) : Prop :=
  ∀ i x, p (x + unitVector i) = p x

/-- Smoothness up to t=0, with the PDE stated at interior positive times.
This follows the convention of the authors' `IsSmoothSolution`. The time
variable is not constrained outside the interval on which the solution is used.
-/
structure IsSmoothSolutionBefore (ν T : ℝ) (u₀ : VectorField)
    (u : Velocity) (p : Pressure) : Prop where
  smooth_velocity : ContDiffOn ℝ ∞ (fun z : ℝ × Space => u z.1 z.2)
    (Ico 0 T ×ˢ (univ : Set Space))
  smooth_pressure : ContDiffOn ℝ ∞ (fun z : ℝ × Space => p z.1 z.2)
    (Ico 0 T ×ˢ (univ : Set Space))
  initial : ∀ x, u 0 x = u₀ x
  momentum : ∀ t ∈ Ioo 0 T, ∀ x,
    deriv (fun τ => u τ x) t + advectionAt (u t) x =
      ν • laplacianAt (u t) x - pressureGradientAt (p t) x
  incompressible : ∀ t ∈ Ico 0 T, ∀ x, divergenceAt (u t) x = 0

/-- Uniform finite energy, including t=0 and arbitrarily near blow-up. -/
def UniformFiniteEnergyBefore (T : ℝ) (u : Velocity) : Prop :=
  ∃ E : ℝ, 0 ≤ E ∧ ∀ t ∈ Ico 0 T,
    ∫⁻ x, ENNReal.ofReal (‖u t x‖ ^ 2) ≤ ENNReal.ofReal E

def similarityResidual (W : Velocity) (q : Pressure) (s : ℝ) (y : Space) : Space :=
  deriv (fun σ => W σ y) s + (1 / 2 : ℝ) • W s y +
    (1 / 2 : ℝ) • fderiv ℝ (W s) y y - laplacianAt (W s) y +
    advectionAt (W s) y + pressureGradientAt (q s) y

/-- The explicit witness-level version of the premise in Challenge.lean.
The second derivative bound and pressure-gradient decay are stronger written
assumptions than the first displayed hypothesis of printed Theorem 1.1.
-/
def IsLibraryProfile (W : Velocity) (q : Pressure) (P : ℝ)
    (R : Space ≃ₗᵢ[ℝ] Space) (A : ℝ) : Prop :=
  0 < P ∧
  ContDiff ℝ ∞ (fun z : ℝ × Space => W z.1 z.2) ∧
  ContDiff ℝ ∞ (fun z : ℝ × Space => q z.1 z.2) ∧
  (∀ s y, similarityResidual W q s y = 0) ∧
  (∀ s y, divergenceAt (W s) y = 0) ∧
  (∀ s y, W (s + P) y = R (W s (R.symm y))) ∧
  (∃ s y, W s y ≠ 0) ∧
  (∀ s y, ∀ j ≤ 2,
    ‖iteratedFDeriv ℝ j (W s) y‖ ≤ A / (1 + ‖y‖) ^ (j + 1)) ∧
  (∀ s y, ‖fderiv ℝ (q s) y‖ ≤ A / (1 + ‖y‖) ^ 3)

/-- The printed (1.2)--(1.3) hypothesis, before importing Remark 1.2 or
pressure-decay regularization. Here the first derivative bound uses the same
finite-dimensional derivative norm as the Lean profile predicate. -/
def IsPaperProfile (W : Velocity) (q : Pressure) (P : ℝ)
    (R : Space ≃ₗᵢ[ℝ] Space) (A : ℝ) : Prop :=
  0 < P ∧
  ContDiff ℝ ∞ (fun z : ℝ × Space => W z.1 z.2) ∧
  ContDiff ℝ ∞ (fun z : ℝ × Space => q z.1 z.2) ∧
  (∀ s y, similarityResidual W q s y = 0) ∧
  (∀ s y, divergenceAt (W s) y = 0) ∧
  (∀ s y, W (s + P) y = R (W s (R.symm y))) ∧
  (∃ s y, W s y ≠ 0) ∧
  (∀ s y, ‖W s y‖ ≤ A / (1 + ‖y‖)) ∧
  (∀ s y, ‖fderiv ℝ (W s) y‖ ≤ A / (1 + ‖y‖) ^ 2)

/-- Formula (1.4), with its T-dependent phase preserved. -/
def comparisonField (W : Velocity) (T t : ℝ) : VectorField :=
  fun x => (T - t) ^ (-(1 / 2 : ℝ)) •
    W (Real.log (T / (T - t))) ((T - t) ^ (-(1 / 2 : ℝ)) • x)

/-- Physical solution expressed in similarity variables for blow-up at time 1. -/
def rescaleAtOne (u : Velocity) (t : ℝ) : VectorField :=
  fun y => Real.sqrt (1 - t) • u t (Real.sqrt (1 - t) • y)

/-- The explicit physical conclusion requested for a fixed selected profile.
All constants may depend on W, q, P, R, A and ε, but not on t.
-/
def SpaceConclusion (W : Velocity) (ε : ℝ) : Prop :=
  ∃ (u₀ : VectorField) (u : Velocity) (p : Pressure) (c C κ : ℝ),
    ContDiff ℝ ∞ u₀ ∧ HasCompactSupport u₀ ∧
    (∀ x, divergenceAt u₀ x = 0) ∧
    FiniteGradient (u₀ - W 0) ∧ gradientNorm (u₀ - W 0) < ε ∧
    IsSmoothSolutionBefore 1 1 u₀ u p ∧ UniformFiniteEnergyBefore 1 u ∧
    0 < c ∧ c ≤ C ∧ 0 < κ ∧ κ < (1 / 4 : ℝ) ∧
    (∀ t ∈ Ico (0 : ℝ) 1,
      FiniteGradient (u t) ∧
      c * (1 - t) ^ (-(1 / 4 : ℝ)) ≤ gradientNorm (u t) ∧
      gradientNorm (u t) ≤ C * (1 - t) ^ (-(1 / 4 : ℝ))) ∧
    (∀ t ∈ Ico (0 : ℝ) 1,
      FiniteGradient (rescaleAtOne u t - W (-Real.log (1 - t))) ∧
      gradientNorm (rescaleAtOne u t - W (-Real.log (1 - t))) ≤
        C * (1 - t) ^ κ)

/-- Requested endpoint: retains every explicit profile, and every ε>0. -/
def Theorem11Space : Prop :=
  ∀ (W : Velocity) (q : Pressure) (P : ℝ)
    (R : Space ≃ₗᵢ[ℝ] Space) (A : ℝ),
    IsLibraryProfile W q P R A → ∀ ε : ℝ, 0 < ε → SpaceConclusion W ε

/-- Printed (1.6), with no arbitrary-ε strengthening and Eulerian error norm. -/
def PaperSpaceConclusion (W : Velocity) : Prop :=
  ∃ (u₀ : VectorField) (u : Velocity) (p : Pressure) (c C κ : ℝ),
    ContDiff ℝ ∞ u₀ ∧ HasCompactSupport u₀ ∧
    (∀ x, divergenceAt u₀ x = 0) ∧
    IsSmoothSolutionBefore 1 1 u₀ u p ∧ UniformFiniteEnergyBefore 1 u ∧
    0 < c ∧ c ≤ C ∧ 0 < κ ∧ κ < (1 / 4 : ℝ) ∧
    ∀ t ∈ Ico (0 : ℝ) 1,
      FiniteGradient (u t) ∧
      FiniteGradient (u t - comparisonField W 1 t) ∧
      c * (1 - t) ^ (-(1 / 4 : ℝ)) ≤ gradientNorm (u t) ∧
      gradientNorm (u t) ≤ C * (1 - t) ^ (-(1 / 4 : ℝ)) ∧
      gradientNorm (u t - comparisonField W 1 t) ≤
        C * (1 - t) ^ (κ - (1 / 4 : ℝ))

def PaperTheorem11Space : Prop :=
  ∀ (W : Velocity) (q : Pressure) (P : ℝ)
    (R : Space ≃ₗᵢ[ℝ] Space) (A : ℝ),
    IsPaperProfile W q P R A → PaperSpaceConclusion W

/-- Printed (1.7). The error is small on B_(1/16); it is not zero there.
Both pressure and velocity are periodic, as in the paper's solution class.
-/
def TorusConclusion (W : Velocity) : Prop :=
  ∃ (T : ℝ) (u₀ : VectorField) (u : Velocity) (p : Pressure) (c C κ : ℝ),
    0 < T ∧ T ≤ 1 ∧
    ContDiff ℝ ∞ u₀ ∧ PeriodicField u₀ ∧
    (∀ x, divergenceAt u₀ x = 0) ∧
    IsSmoothSolutionBefore 1 T u₀ u p ∧
    (∀ t ∈ Ico (0 : ℝ) T, PeriodicField (u t) ∧ PeriodicScalar (p t)) ∧
    0 < c ∧ c ≤ C ∧ 0 < κ ∧ κ < (1 / 4 : ℝ) ∧
    ∀ t ∈ Ico (0 : ℝ) T,
      FiniteH1On (u t) unitCell ∧
      FiniteH1On (u t - comparisonField W T t) (Metric.ball 0 (1 / 16 : ℝ)) ∧
      c * (T - t) ^ (-(1 / 4 : ℝ)) ≤ h1NormOn (u t) unitCell ∧
      h1NormOn (u t) unitCell ≤ C * (T - t) ^ (-(1 / 4 : ℝ)) ∧
      h1NormOn (u t - comparisonField W T t) (Metric.ball 0 (1 / 16 : ℝ)) ≤
        C * (T - t) ^ (κ - (1 / 4 : ℝ))

def Theorem11Torus : Prop :=
  ∀ (W : Velocity) (q : Pressure) (P : ℝ)
    (R : Space ≃ₗᵢ[ℝ] Space) (A : ℝ),
    IsLibraryProfile W q P R A → TorusConclusion W

def PaperTheorem11Torus : Prop :=
  ∀ (W : Velocity) (q : Pressure) (P : ℝ)
    (R : Space ≃ₗᵢ[ℝ] Space) (A : ℝ),
    IsPaperProfile W q P R A → TorusConclusion W

/-- A weaker physical endpoint already supported by local regularization.
One compact datum works for every compact time interval before one. The
velocity, pressure and energy bound may depend on the interval endpoint T.
No single globally smooth pressure, uniform energy bound as T approaches one,
physical rate, or physical rescaled convergence is asserted by this contract.
-/
def SpaceLocalConclusion (W : Velocity) (ε : ℝ) : Prop :=
  ∃ φ : VectorField,
    ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
    (∀ x, divergenceAt φ x = 0) ∧
    FiniteGradient (φ - W 0) ∧ gradientNorm (φ - W 0) < ε ∧
    ∀ T : ℝ, 0 < T → T < 1 →
      ∃ (U : Velocity) (p : Pressure),
        IsSmoothSolutionBefore 1 T φ U p ∧ UniformFiniteEnergyBefore T U

/-- Witness-preserving, arbitrary-tolerance version of the weaker physical
endpoint. As elsewhere, this is a proposition definition, not its proof. -/
def Theorem11SpaceLocal : Prop :=
  ∀ (W : Velocity) (q : Pressure) (P : ℝ)
    (R : Space ≃ₗᵢ[ℝ] Space) (A : ℝ),
    IsLibraryProfile W q P R A → ∀ ε : ℝ, 0 < ε → SpaceLocalConclusion W ε

/-- Quantitative physical solutions on every compact time slab before one.
The datum and all rate/convergence constants are chosen before T. Only the
smooth solution, its pressure, and the finite-energy bound may depend on T.
This preserves the physical quantitative content without asserting a global
pressure choice or a common energy bound on the full half-open interval.
-/
def SpaceSlabsConclusion (W : Velocity) (ε : ℝ) : Prop :=
  ∃ (φ : VectorField) (c C κ : ℝ),
    ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
    (∀ x, divergenceAt φ x = 0) ∧
    FiniteGradient (φ - W 0) ∧ gradientNorm (φ - W 0) < ε ∧
    0 < c ∧ c ≤ C ∧ 0 < κ ∧ κ < (1 / 4 : ℝ) ∧
    ∀ T : ℝ, 0 < T → T < 1 →
      ∃ (U : Velocity) (p : Pressure),
        IsSmoothSolutionBefore 1 T φ U p ∧ UniformFiniteEnergyBefore T U ∧
        ∀ t ∈ Ico (0 : ℝ) T,
          FiniteGradient (U t) ∧
          c * (1 - t) ^ (-(1 / 4 : ℝ)) ≤ gradientNorm (U t) ∧
          gradientNorm (U t) ≤ C * (1 - t) ^ (-(1 / 4 : ℝ)) ∧
          FiniteGradient (rescaleAtOne U t - W (-Real.log (1 - t))) ∧
          gradientNorm (rescaleAtOne U t - W (-Real.log (1 - t))) ≤
            C * (1 - t) ^ κ

/-- The strongest physical fallback contract in this packet: quantitative
solutions on all compact slabs, for the same selected profile and datum. -/
def Theorem11SpaceSlabs : Prop :=
  ∀ (W : Velocity) (q : Pressure) (P : ℝ)
    (R : Space ≃ₗᵢ[ℝ] Space) (A : ℝ),
    IsLibraryProfile W q P R A → ∀ ε : ℝ, 0 < ε → SpaceSlabsConclusion W ε

/-- Smoothness up to and including time T, with the PDE at interior times.
This is the class of a smooth continuation through the blow-up time. -/
structure IsSmoothSolutionThrough (ν T : ℝ) (u₀ : VectorField)
    (u : Velocity) (p : Pressure) : Prop where
  smooth_velocity : ContDiffOn ℝ ∞ (fun z : ℝ × Space => u z.1 z.2)
    (Icc 0 T ×ˢ (univ : Set Space))
  smooth_pressure : ContDiffOn ℝ ∞ (fun z : ℝ × Space => p z.1 z.2)
    (Icc 0 T ×ˢ (univ : Set Space))
  initial : ∀ x, u 0 x = u₀ x
  momentum : ∀ t ∈ Ioo 0 T, ∀ x,
    deriv (fun τ => u τ x) t + advectionAt (u t) x =
      ν • laplacianAt (u t) x - pressureGradientAt (p t) x
  incompressible : ∀ t ∈ Icc 0 T, ∀ x, divergenceAt (u t) x = 0

/-- Uniform finite energy on the closed interval [0,T]. -/
def UniformFiniteEnergyThrough (T : ℝ) (u : Velocity) : Prop :=
  ∃ E : ℝ, 0 ≤ E ∧ ∀ t ∈ Icc 0 T,
    ∫⁻ x, ENNReal.ofReal (‖u t x‖ ^ 2) ≤ ENNReal.ofReal E

/-- The conclusion of `SpaceConclusion`, together with the two facts that make
the solution the one that blows up: every smooth finite-energy solution with
the same datum on an interval [0,T), T ≤ 1, is this solution there; and no
smooth finite-energy solution with this datum exists on the closed interval
[0,1]. -/
def SpaceBlowupConclusion (W : Velocity) (ε : ℝ) : Prop :=
  ∃ (u₀ : VectorField) (u : Velocity) (p : Pressure) (c C κ : ℝ),
    ContDiff ℝ ∞ u₀ ∧ HasCompactSupport u₀ ∧
    (∀ x, divergenceAt u₀ x = 0) ∧
    FiniteGradient (u₀ - W 0) ∧ gradientNorm (u₀ - W 0) < ε ∧
    IsSmoothSolutionBefore 1 1 u₀ u p ∧ UniformFiniteEnergyBefore 1 u ∧
    0 < c ∧ c ≤ C ∧ 0 < κ ∧ κ < (1 / 4 : ℝ) ∧
    (∀ t ∈ Ico (0 : ℝ) 1,
      FiniteGradient (u t) ∧
      c * (1 - t) ^ (-(1 / 4 : ℝ)) ≤ gradientNorm (u t) ∧
      gradientNorm (u t) ≤ C * (1 - t) ^ (-(1 / 4 : ℝ))) ∧
    (∀ t ∈ Ico (0 : ℝ) 1,
      FiniteGradient (rescaleAtOne u t - W (-Real.log (1 - t))) ∧
      gradientNorm (rescaleAtOne u t - W (-Real.log (1 - t))) ≤
        C * (1 - t) ^ κ) ∧
    (∀ T : ℝ, T ≤ 1 → ∀ (v : Velocity) (q : Pressure),
      IsSmoothSolutionBefore 1 T u₀ v q → UniformFiniteEnergyBefore T v →
      ∀ t ∈ Ico (0 : ℝ) T, v t = u t) ∧
    ¬ ∃ (v : Velocity) (q : Pressure),
      IsSmoothSolutionThrough 1 1 u₀ v q ∧ UniformFiniteEnergyThrough 1 v

/-- Theorem 1.1 on R³ for a profile of the library's class, with uniqueness and
the impossibility of a smooth finite-energy continuation to time one. -/
def Theorem11SpaceBlowup : Prop :=
  ∀ (W : Velocity) (q : Pressure) (P : ℝ)
    (R : Space ≃ₗᵢ[ℝ] Space) (A : ℝ),
    IsLibraryProfile W q P R A → ∀ ε : ℝ, 0 < ε → SpaceBlowupConclusion W ε

end Theorem11
