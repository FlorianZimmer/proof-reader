import SectionsTwoSix
import Theorem11Challenge

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace NavierStokes.Analysis

/-- L^(3/2) is a normed space since its exponent is at least one. -/
instance factOneLeThreeHalves : Fact ((1 : ℝ≥0∞) ≤ 3 / 2) := ⟨by
  rw [ENNReal.le_div_iff_mul_le (by simp) (by simp)]; norm_num⟩

/-- B(u,v)(t) is the quadratic Duhamel integral with initial time zero. -/
def duhamel {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (H : Breakdown.HeatBilinear X) (u v : ℝ → X) (t : ℝ) : X :=
  ∫ s in (0 : ℝ)..t, H.K (t - s) (u s) (v s)

/-- Membership in Cκ([0,1);X), with boundedness stated before using a real supremum. -/
def WeightedCurve {X : Type} [NormedAddCommGroup X] (κ : ℝ) (v : ℝ → X) : Prop :=
  ContinuousOn v (Ico 0 1) ∧
    ∃ M : ℝ, ∀ t ∈ Ico (0 : ℝ) 1, (1 - t) ^ ((1 / 4 : ℝ) - κ) * ‖v t‖ ≤ M

/-- The norm (4.5). It is used only with a separate `WeightedCurve` hypothesis. -/
def weightedNorm {X : Type} [NormedAddCommGroup X] (κ : ℝ) (v : ℝ → X) : ℝ :=
  sSup ((fun t => (1 - t) ^ ((1 / 4 : ℝ) - κ) * ‖v t‖) '' Ico (0 : ℝ) 1)

/-- Linearity on the weighted space, without imposing arbitrary conditions on
extensions of functions outside [0,1). -/
def WeightedLinear {X E Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [AddCommGroup E] [Module ℝ E] [AddCommGroup Y] [Module ℝ Y]
    (κ : ℝ) (R : (ℝ → X) → E × (ℝ → Y)) : Prop :=
  (∀ g h, WeightedCurve κ g → WeightedCurve κ h →
    (R (g + h)).1 = (R g).1 + (R h).1 ∧
    ∀ t ∈ Ico (0 : ℝ) 1, (R (g + h)).2 t = (R g).2 t + (R h).2 t) ∧
  (∀ c : ℝ, ∀ g, WeightedCurve κ g →
    (R (c • g)).1 = c • (R g).1 ∧
    ∀ t ∈ Ico (0 : ℝ) 1, (R (c • g)).2 t = c • (R g).2 t)

/-- Continuous extension by the nearest endpoint. -/
def intervalExtension {X : Type} [TopologicalSpace X] [Zero X] {a b : ℝ} (f : C(Icc a b, X))
    (t : ℝ) : X := if h : a ≤ b then Set.IccExtend h f t else 0

/-- The physical profile in the authors' homogeneous H¹ realization. The
paper-profile hypothesis is retained in targets that use this expression. -/
def profileCurve (W : Theorem11.Velocity) (t : ℝ) : Breakdown.Freq.X :=
  Breakdown.Freq.embedX (Theorem11.comparisonField W 1 t)

/-- The centred physical cube of side L. -/
def cube (L : ℝ) : Set Breakdown.Space :=
  {x | ∀ i : Fin 3, -(L / 2) ≤ x i ∧ x i ≤ L / 2}

/-- Period L in every coordinate. -/
def PeriodicAt (L : ℝ) (f : Breakdown.Space → Breakdown.Space) : Prop :=
  ∀ i x, f (x + L • Breakdown.unitVector i) = f x

/-- Fourier coefficients on a torus of side L, normalized by its volume. -/
def torusCoefficient (L : ℝ) (f : Breakdown.Space → Breakdown.Space)
    (k : Breakdown.Periodic.Lattice) : Breakdown.Periodic.Coef :=
  (L ^ 3)⁻¹ • ∫ x in cube L,
    Complex.exp (-(2 * Real.pi * Complex.I *
      (((inner ℝ (Breakdown.Periodic.freq k) x) / L : ℝ) : ℂ))) •
      Breakdown.Periodic.complexify (f x)

/-- Homogeneous H¹ norm of the L-periodic field represented by unit-frequency
coefficients v. The power L^(1/2) is the change of spatial variables. -/
def torusGradientNorm (L : ℝ) (v : Breakdown.Periodic.V) : ℝ :=
  L ^ (1 / 2 : ℝ) * Real.sqrt
    (∑' k : Breakdown.Periodic.Lattice,
      (4 * Real.pi ^ 2 * ‖Breakdown.Periodic.freq k‖ ^ 2) *
        ‖Breakdown.Periodic.coeff v k‖ ^ 2)

/-- The bilinear kernel on the L-periodic torus, transported from the unit torus. -/
def torusKernel (L τ : ℝ) (u v : Breakdown.Periodic.V) : Breakdown.Periodic.V :=
  L⁻¹ • Breakdown.Periodic.kernel (τ / L ^ 2) u v

/-- The Duhamel equation in rescaled unit Fourier coordinates for period L. -/
def TorusMild (L : ℝ) (u : ℝ → Breakdown.Periodic.V) (a b : ℝ) : Prop :=
  ContinuousOn u (Ico a b) ∧
    ∀ t ∈ Ico a b,
      IntervalIntegrable (fun s => torusKernel L (t - s) (u s) (u s)) volume a t ∧
      u t = Breakdown.Periodic.heat ((t - a) / L ^ 2) (u a) +
        ∫ s in a..t, torusKernel L (t - s) (u s) (u s)

/-- Field of period L represented in the unit Fourier coordinates. -/
def toTorus (L : ℝ) (f : Breakdown.Space → Breakdown.Space) : Breakdown.Periodic.V :=
  Breakdown.Periodic.toV (fun x => f (L • x))

/-- The real part of a complex three-vector. -/
def realVector (z : Breakdown.Periodic.Coef) : Breakdown.Space :=
  WithLp.toLp 2 (fun i => (z i).re)

/-- Periodic extension of the L⁶ representative on the authors' unit cell. -/
def torusValue (v : Breakdown.Periodic.V) (x : Breakdown.Space) : Breakdown.Space :=
  realVector ((Breakdown.Periodic.torusSeries 6 (Breakdown.Periodic.coeff v) :
    Breakdown.Space → Breakdown.Periodic.Coef) (Breakdown.Periodic.wrap x))

/-- Periodic extension of the L² weak-derivative representative on the unit cell. -/
def torusDerivative (v : Breakdown.Periodic.V) (i : Fin 3)
    (x : Breakdown.Space) : Breakdown.Space :=
  realVector ((Breakdown.Periodic.torusSeries 2 (Breakdown.Periodic.gradCoef i v) :
    Breakdown.Space → Breakdown.Periodic.Coef) (Breakdown.Periodic.wrap x))

/-- Local H¹ error density, using weak Fourier derivatives for v. -/
def torusErrorSquare (v : Breakdown.Periodic.V) (f : Breakdown.Space → Breakdown.Space)
    (x : Breakdown.Space) : ℝ :=
  ‖torusValue v x - f x‖ ^ 2 + ∑ i : Fin 3,
    ‖torusDerivative v i x - fderiv ℝ f x (Breakdown.unitVector i)‖ ^ 2

/-- Explicit finiteness accompanies every use of this local error norm. -/
def torusErrorNorm (v : Breakdown.Periodic.V) (f : Breakdown.Space → Breakdown.Space)
    (Ω : Set Breakdown.Space) : ℝ :=
  Real.sqrt (∫ x in Ω, torusErrorSquare v f x)

/-- The radius-r solenoidal cutoff used in §5, with the same inner/outer ratio. -/
def cutoffProfile (W : Theorem11.Velocity) (r t : ℝ) : Breakdown.Space → Breakdown.Space :=
  Breakdown.Periodic.cutoffField
    (fun x => Real.smoothTransition (2 - 2 * ‖x‖ / r)) 0
    (Theorem11.comparisonField W 1 t)

/-- Periodization. The uses below are for compactly supported fields whose
translates have disjoint interiors. -/
def periodize (L : ℝ) (f : Breakdown.Space → Breakdown.Space)
    (x : Breakdown.Space) : Breakdown.Space :=
  ∑' k : Breakdown.Periodic.Lattice, f (x - L • Breakdown.Periodic.freq k)

/-- The periodic approximate curve of §6, with the field cut off at L/8. -/
def approximateTorus (W : Theorem11.Velocity) (L t : ℝ) : Breakdown.Periodic.V :=
  toTorus L (periodize L (cutoffProfile W (L / 8) t))

/-- The physical periodic residual, written in unit Fourier coordinates. -/
def approximateTorusResidual (W : Theorem11.Velocity) (L t : ℝ) : Breakdown.Periodic.V :=
  approximateTorus W L t - Breakdown.Periodic.heat (t / L ^ 2) (approximateTorus W L 0) -
    ∫ s in (0 : ℝ)..t, torusKernel L (t - s)
      (approximateTorus W L s) (approximateTorus W L s)

/-- Weighted homogeneous torus space; boundedness is explicit. -/
def TorusWeighted (κ L : ℝ) (u : ℝ → Breakdown.Periodic.V) : Prop :=
  ContinuousOn u (Ico 0 1) ∧
    (∀ t ∈ Ico (0 : ℝ) 1, Breakdown.Periodic.coeff (u t) 0 = 0) ∧
    ∃ M : ℝ, ∀ t ∈ Ico (0 : ℝ) 1,
      (1 - t) ^ ((1 / 4 : ℝ) - κ) * torusGradientNorm L (u t) ≤ M

/-- Linearity restricted to mean-zero weighted periodic curves. -/
def TorusWeightedLinear {E : Type} [AddCommGroup E] [Module ℝ E]
    (κ L : ℝ) (R : (ℝ → Breakdown.Periodic.V) → E × (ℝ → Breakdown.Periodic.V)) : Prop :=
  (∀ g h, TorusWeighted κ L g → TorusWeighted κ L h →
    (R (g + h)).1 = (R g).1 + (R h).1 ∧
    ∀ t ∈ Ico (0 : ℝ) 1, (R (g + h)).2 t = (R g).2 t + (R h).2 t) ∧
  (∀ c : ℝ, ∀ g, TorusWeighted κ L g →
    (R (c • g)).1 = c • (R g).1 ∧
    ∀ t ∈ Ico (0 : ℝ) 1, (R (c • g)).2 t = c • (R g).2 t)

/-- Norm in the weighted homogeneous torus space. -/
def torusWeightedNorm (κ L : ℝ) (u : ℝ → Breakdown.Periodic.V) : ℝ :=
  sSup ((fun t => (1 - t) ^ ((1 / 4 : ℝ) - κ) * torusGradientNorm L (u t)) ''
    Ico (0 : ℝ) 1)

/-- One-period Volterra inverse, with its existence asserted separately in the
target. `Ring.inverse` is not evidence of invertibility. -/
def periodResolvent {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (H : Breakdown.HeatBilinear X) (u : ℝ → X) (T : ℝ) :
    Breakdown.Piece X T →L[ℝ] Breakdown.Piece X T :=
  Ring.inverse (1 - (2 : ℝ) • H.pieceBil T (Breakdown.toPiece T u))

/-- The paper's monodromy, before replacing it by a product of short steps. -/
def monodromy {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (F : Breakdown.MildFramework X) (ρ : X ≃ₗᵢ[ℝ] X)
    (u : ℝ → X) (lam : ℝ) : X →L[ℝ] X :=
  (ρ.symm.toContinuousLinearEquiv : X →L[ℝ] X).comp
    ((F.D lam).comp ((Breakdown.pieceEnd (1 - lam)).comp
      ((periodResolvent F.toHeatBilinear u (1 - lam)).comp
        (F.toHeatBilinear.pieceFree (1 - lam)))))

/-- Restrict a physical curve to its nth similarity interval and normalize it. -/
def normalizedPiece {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (F : Breakdown.MildFramework X) (ρ : X ≃ₗᵢ[ℝ] X)
    (lam : ℝ) (v : ℝ → X) (n : ℕ) (s : ℝ) : X :=
  ((ρ.symm : X → X)^[n]) (F.D (lam ^ n) (v (1 - lam ^ n + lam ^ n * s)))

/-- Forcing sequence (4.13), defined from g alone. -/
def recurrenceForcing {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (F : Breakdown.MildFramework X) (ρ : X ≃ₗᵢ[ℝ] X)
    (u : ℝ → X) (lam : ℝ) (g : ℝ → X) (n : ℕ) : X :=
  ρ.symm (F.D lam (Breakdown.pieceEnd (1 - lam)
    ((periodResolvent F.toHeatBilinear u (1 - lam))
      (Breakdown.toPiece (1 - lam) (normalizedPiece F ρ lam g n)) -
        Breakdown.toPiece (1 - lam) (normalizedPiece F ρ lam g n))))

/-- Physical symmetrized convection of two L-periodic Fourier fields. -/
def torusConvection (L : ℝ) (u v : Breakdown.Periodic.V)
    (x : Breakdown.Space) : Breakdown.Space :=
  L⁻¹ • ∑ i : Fin 3,
    (((torusValue u (L⁻¹ • x)) i) • torusDerivative v i (L⁻¹ • x) +
      ((torusValue v (L⁻¹ • x)) i) • torusDerivative u i (L⁻¹ • x))

/-- A tensor is indexed by output component first and divergence direction second. -/
abbrev Tensor := Fin 3 → Fin 3 → ℝ

/-- W^(1,1) specified by integrable entries and integrable weak derivatives. -/
def TensorW11 (F : Breakdown.Space → Tensor)
    (DF : Fin 3 → Breakdown.Space → Tensor) : Prop :=
  (∀ i j, Integrable (fun x => F x i j)) ∧
  (∀ l i j, Integrable (fun x => DF l x i j)) ∧
  ∀ φ : Breakdown.Space → ℝ, Breakdown.IsTestFunction φ → ∀ l i j,
    (∫ x, F x i j * fderiv ℝ φ x (Breakdown.unitVector l)) =
      -(∫ x, DF l x i j * φ x)

/-- Divergence from the specified weak derivative tensor. -/
def tensorDivergence (DF : Fin 3 → Breakdown.Space → Tensor)
    (x : Breakdown.Space) : Breakdown.Space :=
  WithLp.toLp 2 (fun j => ∑ i : Fin 3, DF i x j i)

/-- Frobenius norm, used for the W^(1,1) forcing estimate. -/
def tensorNorm (F : Tensor) : ℝ := Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, F i j ^ 2)

/-- Fourier transform with the convention exp(-2πi ξ·x). -/
def fieldFourier (f : Breakdown.Space → Breakdown.Space)
    (ξ : Breakdown.Space) : Breakdown.Periodic.Coef :=
  ∫ x, Complex.exp (-(2 * Real.pi * Complex.I * ((inner ℝ ξ x : ℝ) : ℂ))) •
    Breakdown.Periodic.complexify (f x)

/-- Orthogonal projection onto the plane perpendicular to the real frequency. -/
def frequencyProjection (ξ : Breakdown.Space) (z : Breakdown.Periodic.Coef) :
    Breakdown.Periodic.Coef :=
  z - ((∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * z i) / ((‖ξ‖ ^ 2 : ℝ) : ℂ)) •
    Breakdown.Periodic.complexify ξ

/-- Projected heat evolution of an integrable force, by Fourier inversion. -/
def projectedHeatField (τ : ℝ) (f : Breakdown.Space → Breakdown.Space)
    (x : Breakdown.Space) : Breakdown.Space :=
  realVector (∫ ξ : Breakdown.Space,
    Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ ξ x : ℝ) : ℂ)) •
      (Real.exp (-(4 * Real.pi ^ 2 * τ * ‖ξ‖ ^ 2)) •
        frequencyProjection ξ (fieldFourier f ξ)))

/-- Periodic projected heat evolution, with Fourier frequencies k/L. -/
def periodicHeatField (L τ : ℝ) (f : Breakdown.Space → Breakdown.Space)
    (x : Breakdown.Space) : Breakdown.Space :=
  realVector (∑' k : Breakdown.Periodic.Lattice,
    Complex.exp (2 * Real.pi * Complex.I *
      (((inner ℝ (Breakdown.Periodic.freq k) x) / L : ℝ) : ℂ)) •
      (Real.exp (-(4 * Real.pi ^ 2 * τ * ‖Breakdown.Periodic.freq k‖ ^ 2 / L ^ 2)) •
        Breakdown.Periodic.divFree k (torusCoefficient L f k)))

/-- Defining duality identity for projected heat evolution in homogeneous H¹. -/
def ProjectedHeatSpec (τ : ℝ) (f : Breakdown.Space → Breakdown.Space)
    (v : Breakdown.Freq.X) : Prop :=
  ∀ ψ : Breakdown.Freq.X,
    Integrable (fun x => inner ℝ (f x) (Breakdown.Freq.phiX τ ψ x)) ∧
    inner ℝ v ψ = ∫ x, inner ℝ (f x) (Breakdown.Freq.phiX τ ψ x)

open Classical in
/-- The projected-heat element when its duality representative exists. Targets
using this definition also require `ProjectedHeatSpec`; the fallback gives no
existence or estimate. -/
def projectedHeat (τ : ℝ) (f : Breakdown.Space → Breakdown.Space) : Breakdown.Freq.X :=
  if h : ∃ v, ProjectedHeatSpec τ f v then h.choose else 0

/-- Defining Fourier coefficients for the periodic projected heat field. -/
def ProjectedTorusSpec (L τ : ℝ) (f : Breakdown.Space → Breakdown.Space)
    (v : Breakdown.Periodic.V) : Prop :=
  ∀ k : Breakdown.Periodic.Lattice,
    Breakdown.Periodic.coeff v k =
      Real.exp (-(4 * Real.pi ^ 2 * τ * ‖Breakdown.Periodic.freq k‖ ^ 2 / L ^ 2)) •
        Breakdown.Periodic.divFree k (torusCoefficient L f k)

open Classical in
/-- Periodic projected heat element; its specification is required separately. -/
def projectedTorus (L τ : ℝ) (f : Breakdown.Space → Breakdown.Space) : Breakdown.Periodic.V :=
  if h : ∃ v, ProjectedTorusSpec L τ f v then h.choose else 0

/-- fζ from §6.3, for ζ equal to a periodic field plus a whole-space field.
The cutoff and its derivative supply the compact support. -/
def interactionForce (W : Theorem11.Velocity) (L t : ℝ)
    (g : Breakdown.Periodic.V) (v : Breakdown.Freq.X)
    (x : Breakdown.Space) : Breakdown.Space :=
  ∑ i : Fin 3,
    ((cutoffProfile W (L / 8) t x) i •
      (L⁻¹ • torusDerivative g i (L⁻¹ • x) + Breakdown.Freq.partialX i v x) +
    (torusValue g (L⁻¹ • x) + Breakdown.Freq.velocity v x) i •
      fderiv ℝ (cutoffProfile W (L / 8) t) x (Breakdown.unitVector i))

/-- Aζ of §6.3. -/
def wholeInteraction (W : Theorem11.Velocity) (L : ℝ)
    (g : ℝ → Breakdown.Periodic.V) (v : ℝ → Breakdown.Freq.X) (t : ℝ) : Breakdown.Freq.X :=
  -∫ s in (0 : ℝ)..t, projectedHeat (t - s) (interactionForce W L s (g s) (v s))

/-- A_T ζ of §6.3, in rescaled unit Fourier coordinates. -/
def periodicInteraction (W : Theorem11.Velocity) (L : ℝ)
    (g : ℝ → Breakdown.Periodic.V) (v : ℝ → Breakdown.Freq.X)
    (t : ℝ) : Breakdown.Periodic.V :=
  -∫ s in (0 : ℝ)..t,
    projectedTorus L (t - s) (periodize L (interactionForce W L s (g s) (v s)))

/-- Finiteness and representation conditions for the two interaction integrals. -/
def InteractionsDefined (W : Theorem11.Velocity) (L : ℝ)
    (g : ℝ → Breakdown.Periodic.V) (v : ℝ → Breakdown.Freq.X) : Prop :=
  ∀ t ∈ Ico (0 : ℝ) 1,
    IntervalIntegrable (fun s => projectedHeat (t - s) (interactionForce W L s (g s) (v s)))
      volume 0 t ∧
    IntervalIntegrable (fun s => projectedTorus L (t - s)
      (periodize L (interactionForce W L s (g s) (v s)))) volume 0 t ∧
    ∀ s ∈ Ico (0 : ℝ) t,
      MemLp (interactionForce W L s (g s) (v s)) (3 / 2) volume ∧
      ProjectedHeatSpec (t - s) (interactionForce W L s (g s) (v s))
        (projectedHeat (t - s) (interactionForce W L s (g s) (v s))) ∧
      ProjectedTorusSpec L (t - s) (periodize L (interactionForce W L s (g s) (v s)))
        (projectedTorus L (t - s) (periodize L (interactionForce W L s (g s) (v s))))

end NavierStokes.Analysis
