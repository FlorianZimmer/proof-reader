import PhysicalStatement
import Breakdown.Cert.ExtendedStatement

/-!
# The assumptions at the entrance to the adapted edition

This module defines propositions only. The velocity assumptions and the
pressure-gradient estimate are separate, so neither is silently supplied by
the phrase "a profile". The certificate alternative is the authors' complete
formal certificate, not a hash or an assertion that a computation succeeded.
-/

open scoped ContDiff

noncomputable section

namespace NavierStokes

/-- A nonzero smooth recurrent solution of the self-similar equations, with
velocity decay through two spatial derivatives. Here S is positive, R is an
orthogonal linear map, and every identity and estimate holds for all real
self-similar times s and all y in R³. This condition does not include the
pressure-gradient estimate, which is stated separately below. -/
def ProfileWithVelocityDecay (W : Theorem11.Velocity) (q : Theorem11.Pressure)
    (S : ℝ) (R : Theorem11.Space ≃ₗᵢ[ℝ] Theorem11.Space) (A : ℝ) : Prop :=
  0 < S ∧
  ContDiff ℝ ∞ (fun z : ℝ × Theorem11.Space => W z.1 z.2) ∧
  ContDiff ℝ ∞ (fun z : ℝ × Theorem11.Space => q z.1 z.2) ∧
  (∀ s y, Theorem11.similarityResidual W q s y = 0) ∧
  (∀ s y, Theorem11.divergenceAt (W s) y = 0) ∧
  (∀ s y, W (s + S) y = R (W s (R.symm y))) ∧
  (∃ s y, W s y ≠ 0) ∧
  (∀ s y, ∀ j ≤ 2,
    ‖iteratedFDeriv ℝ j (W s) y‖ ≤ A / (1 + ‖y‖) ^ (j + 1))

/-- The additional uniform pressure-gradient bound used by the formal
profile route: |∇q(s,y)| ≤ A(1+|y|)^(-3), for every s and y. The norm of the
derivative of the real-valued pressure is its Euclidean gradient norm. -/
def PressureGradientDecay (q : Theorem11.Pressure) (A : ℝ) : Prop :=
  ∀ s y, ‖fderiv ℝ (q s) y‖ ≤ A / (1 + ‖y‖) ^ 3

/-- Either a smooth recurrent profile with velocity and pressure-gradient
decay is supplied, or data satisfying every clause of the authors' formal
extended certificate are supplied. The second alternative is an assumption
that such data exist; it is not a verification of a numerical certificate. -/
def ProfileOrCertificate : Prop :=
  (∃ (W : Theorem11.Velocity) (q : Theorem11.Pressure) (S : ℝ)
      (R : Theorem11.Space ≃ₗᵢ[ℝ] Theorem11.Space) (A : ℝ),
    ProfileWithVelocityDecay W q S R A ∧ PressureGradientDecay q A) ∨
  (∃ (k : ℕ) (d : Breakdown.ExtendedCertificateData k),
    Breakdown.IsExtendedCertificate d)

end NavierStokes
