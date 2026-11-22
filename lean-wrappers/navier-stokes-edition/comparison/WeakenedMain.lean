import EditionContracts
import Theorem11Solution
import Breakdown.Uniqueness.Space
import Breakdown.Cert.ExtendedMain
import Breakdown.CertTorus.Main

/-!
# Deliberately weaker solution for the negative comparison

This module is not imported by any delivered mathematical result. Its two
public declaration names match the challenge, but their types omit required
conclusions. A comparison must reject their statements; a compilation failure
or a missing executable is not a successful control.
-/

open scoped ContDiff
noncomputable section
namespace NavierStokes

/-- Negative control: only a family of local smooth solutions, omitting the
single global-before-blow-up trajectory, rates and continuation conclusion. -/
theorem theorem_1_1_space
    (W : Theorem11.Velocity) (q : Theorem11.Pressure) (S : ℝ)
    (R : Theorem11.Space ≃ₗᵢ[ℝ] Theorem11.Space) (A : ℝ)
    (hS : 0 < S)
    (hW : ContDiff ℝ ∞ (fun z : ℝ × Theorem11.Space => W z.1 z.2))
    (hq : ContDiff ℝ ∞ (fun z : ℝ × Theorem11.Space => q z.1 z.2))
    (hEquation : ∀ s y, Theorem11.similarityResidual W q s y = 0)
    (hDivergence : ∀ s y, Theorem11.divergenceAt (W s) y = 0)
    (hRecurrence : ∀ s y, W (s + S) y = R (W s (R.symm y)))
    (hNonzero : ∃ s y, W s y ≠ 0)
    (hVelocityDecay : ∀ s y, ∀ j ≤ 2,
      ‖iteratedFDeriv ℝ j (W s) y‖ ≤ A / (1 + ‖y‖) ^ (j + 1))
    (hPressureGradientDecay : ∀ s y,
      ‖fderiv ℝ (q s) y‖ ≤ A / (1 + ‖y‖) ^ 3)
    (ε : ℝ) (hε : 0 < ε) : Theorem11.SpaceLocalConclusion W ε := by
  exact Theorem11.theorem11SpaceLocal W q S R A
    ⟨hS, hW, hq, hEquation, hDivergence, hRecurrence, hNonzero,
      hVelocityDecay, hPressureGradientDecay⟩ ε hε

/-- Negative control: the torus conclusion is deliberately omitted. -/
theorem conditional_main
    (hProfileWithPressureDecay_or_certificate :
      (∃ (W : Theorem11.Velocity) (q : Theorem11.Pressure) (S : ℝ)
          (R : Theorem11.Space ≃ₗᵢ[ℝ] Theorem11.Space) (A : ℝ),
        ProfileWithVelocityDecay W q S R A ∧ PressureGradientDecay q A) ∨
      (∃ (k : ℕ) (d : Breakdown.ExtendedCertificateData k),
        Breakdown.IsExtendedCertificate d)) :
    Breakdown.BreakdownOnSpace := by
  rcases hProfileWithPressureDecay_or_certificate with hProfile | hCertificate
  · rcases hProfile with ⟨W, q, S, R, A, hVelocity, hPressure⟩
    rcases hVelocity with ⟨hS, hW, hq, hEq, hDiv, hRec, hNonzero, hDecay⟩
    have hp : Theorem11.IsLibraryProfile W q S R A :=
      ⟨hS, hW, hq, hEq, hDiv, hRec, hNonzero, hDecay, hPressure⟩
    exact Breakdown.breakdownOnSpace_of_profile (Theorem11.libraryProfile_to_exists hp)
  · rcases hCertificate with ⟨k, d, hd⟩
    exact Breakdown.breakdownOnSpace_of_profile
      (Breakdown.FarField.periodicLerayProfileExists_of_weak
        (Breakdown.extended_certificate_orbit_proved ⟨k, d, hd⟩))

end NavierStokes
