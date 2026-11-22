import EditionContracts
import SpatialScaling
import Theorem11Solution
import Breakdown.Uniqueness.Space
import Breakdown.Torus.Main
import Breakdown.Cert.ExtendedMain
import Breakdown.CertTorus.Main
import Breakdown.CertTorus.CertificateCorollary

/-!
# Theorem 1.1 on R³ and the conditional main implication

The first result retains a specified profile and constructs one solution on
the entire half-open interval [0,1). The second result uses the authors'
nonexistence conclusions on R³ and the torus. These are different conclusions;
the quantitative torus construction remains a separate open target.
-/

open scoped ContDiff

noncomputable section

namespace NavierStokes

/-- The velocity assumptions and the pressure-gradient bound together give
exactly the profile premise required by the supplied Theorem 1.1 proof. -/
theorem library_profile_of_explicit_assumptions
    {W : Theorem11.Velocity} {q : Theorem11.Pressure} {S A : ℝ}
    {R : Theorem11.Space ≃ₗᵢ[ℝ] Theorem11.Space}
    (hProfile : ProfileWithVelocityDecay W q S R A)
    (hPressureGradientDecay : PressureGradientDecay q A) :
    Theorem11.IsLibraryProfile W q S R A := by
  rcases hProfile with ⟨hS, hW, hq, hEq, hDiv, hRec, hNonzero, hDecay⟩
  exact ⟨hS, hW, hq, hEq, hDiv, hRec, hNonzero, hDecay, hPressureGradientDecay⟩

/-- Theorem 1.1 on R³ in the formal profile class: from the stated smooth
recurrent profile, including decay of the second spatial derivatives and of
the pressure gradient, every ε>0 gives a compactly supported smooth datum
within ε of W(0) in the homogeneous H¹ seminorm and one smooth solution of
unit-viscosity Navier–Stokes on [0,1), with uniformly finite energy, two-sided
gradient rate (1-t)^(-1/4), and physical gradient error O((1-t)^(κ-1/4)) for
some 0<κ<1/4. The solution is unique in the stated finite-energy smooth class
and has no finite-energy smooth continuation through time 1.

The quantitative torus conclusion is a separate open target. The second-derivative and pressure bounds
are hypotheses here, rather than an unproved appeal to Remark 1.2. -/
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
    (ε : ℝ) (hε : 0 < ε) : SpacePhysicalBlowupConclusion W ε := by
  apply spacePhysicalBlowup_of_spaceBlowup W ε
  exact Theorem11.theorem11SpaceBlowup W q S R A
    ⟨hS, hW, hq, hEquation, hDivergence, hRecurrence, hNonzero,
      hVelocityDecay, hPressureGradientDecay⟩ ε hε

/-- A smooth recurrent profile with the explicit velocity and pressure
decay bounds rules out global smooth bounded-energy solutions for suitable
compactly supported data on R³, and global smooth periodic-velocity
solutions for suitable periodic data, at every positive viscosity. -/
theorem main_of_profile
    (W : Theorem11.Velocity) (q : Theorem11.Pressure) (S : ℝ)
    (R : Theorem11.Space ≃ₗᵢ[ℝ] Theorem11.Space) (A : ℝ)
    (hProfile : ProfileWithVelocityDecay W q S R A)
    (hPressureGradientDecay : PressureGradientDecay q A) :
    Breakdown.BreakdownOnSpace ∧ Breakdown.BreakdownOnTorus := by
  have hp := Theorem11.libraryProfile_to_exists
    (library_profile_of_explicit_assumptions hProfile hPressureGradientDecay)
  exact ⟨Breakdown.breakdownOnSpace_of_profile hp,
    Breakdown.Periodic.breakdownOnTorus_of_profile hp⟩

/-- A certificate satisfying every formal extended-certificate condition
implies the authors' nonexistence conclusions on R³ and on the torus. -/
theorem main_of_certificate {k : ℕ} (d : Breakdown.ExtendedCertificateData k)
    (hCertificate : Breakdown.IsExtendedCertificate d) :
    Breakdown.BreakdownOnSpace ∧ Breakdown.BreakdownOnTorus := by
  have hw := Breakdown.extended_certificate_orbit_proved ⟨k, d, hCertificate⟩
  have hp := Breakdown.FarField.periodicLerayProfileExists_of_weak hw
  exact ⟨Breakdown.breakdownOnSpace_of_profile hp,
    Breakdown.FarField.breakdownOnTorus_of_weak hw⟩

/-- A nonzero smooth recurrent profile with the explicit pressure-gradient
decay bound, or a valid formal extended certificate, implies nonexistence of
global smooth solutions in the authors' classes on both R³ and the torus.

For R³ the excluded solutions have uniformly bounded energy; on the torus
their velocities are periodic, while the pressure is unrestricted. The data
may depend on the positive viscosity. This statement supplies neither a
numerical certificate nor the quantitative torus trajectory of (1.7). -/
theorem conditional_main
    (hProfileWithPressureDecay_or_certificate :
      (∃ (W : Theorem11.Velocity) (q : Theorem11.Pressure) (S : ℝ)
          (R : Theorem11.Space ≃ₗᵢ[ℝ] Theorem11.Space) (A : ℝ),
        ProfileWithVelocityDecay W q S R A ∧ PressureGradientDecay q A) ∨
      (∃ (k : ℕ) (d : Breakdown.ExtendedCertificateData k),
        Breakdown.IsExtendedCertificate d)) :
    Breakdown.BreakdownOnSpace ∧ Breakdown.BreakdownOnTorus := by
  rcases hProfileWithPressureDecay_or_certificate with hProfile | hCertificate
  · rcases hProfile with ⟨W, q, S, R, A, hVelocity, hPressure⟩
    exact main_of_profile W q S R A hVelocity hPressure
  · rcases hCertificate with ⟨k, d, hd⟩
    exact main_of_certificate d hd

/-- The fifteen groups of cell conditions give the same two nonexistence
conclusions. All cell data and all their mathematical conditions are inputs;
this implication does not assert that particular numerical data pass them. -/
theorem main_of_cell_conditions
    {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : Breakdown.CertCell.CellLayerData k C nE nM)
    (X : Breakdown.CertCell.Instance.InstanceData k C nE nM)
    (R : Breakdown.CertCell.CellCalculus.CellCalculusEntry D)
    (T : Breakdown.CertCell.TreeEntry D R)
    (Y : Breakdown.CertCell.CellLayerEntries D R T)
    (N : Breakdown.CellLayerSystem.CoerciveNumbers)
    (B : Breakdown.CellLayerSystem.ReductionEntries k)
    (hCells : Breakdown.CellLayerSystem.CellSystemCondition D X R T Y N B) :
    Breakdown.BreakdownOnSpace ∧ Breakdown.BreakdownOnTorus := by
  exact Breakdown.CellLayerSystem.spaceAndTorusBreakdown_of_cell_system_condition
    D X R T Y N B hCells

end NavierStokes
