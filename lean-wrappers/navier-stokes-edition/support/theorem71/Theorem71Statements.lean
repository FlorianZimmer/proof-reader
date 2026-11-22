import Breakdown.Cert.ExtendedStatement

/-!
# The physical conclusion of Theorem 7.1

Status: NOT COMPILED. Definitions and elementary interface lemmas only.
Target: the authors' source at ad53419de079eb8f95f60313473374624a348546.

The selected parameter occurs in the period, the approximate field, the
multiplier penalty and the pin target. The correction is an actual difference
of fields. Its Hessian is a weak Hessian: an extended approximate profile is
only required to be C1, even though the resulting exact profile is smooth.
-/

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown.Theorem71

/-- A smooth, nonzero profile at the specified period and the identity isometry.
The derivative and pressure bounds are those of the public profile definition.
No minimal-period or pressure-gauge assertion is included. -/
def IsIdentityProfile (P : ℝ) (W : ℝ → Space → Space)
    (q : ℝ → Space → ℝ) : Prop :=
  0 < P ∧
    ContDiff ℝ ∞ (fun z : ℝ × Space => W z.1 z.2) ∧
    ContDiff ℝ ∞ (fun z : ℝ × Space => q z.1 z.2) ∧
    (∀ s y, SimilarityResidual W q s y = 0) ∧
    (∀ s y, divergenceAt (W s) y = 0) ∧
    (∀ s y, W (s + P) y = W s y) ∧
    (∃ s y, W s y ≠ 0) ∧
    ∃ C : ℝ,
      (∀ s y, ∀ j ≤ 2,
        ‖iteratedFDeriv ℝ j (W s) y‖ ≤ C / (1 + ‖y‖) ^ (j + 1)) ∧
      (∀ s y, ‖fderiv ℝ (q s) y‖ ≤ C / (1 + ‖y‖) ^ 3)

/-- The error is measured in normalized time, theta = s / P. -/
def correction (P : ℝ) (Wa W : ℝ → Space → Space) : ℝ → Space → Space :=
  fun θ y => W (P * θ) y - Wa θ y

def gradient (v : ℝ → Space → Space) :
    ℝ → Space → (Space →L[ℝ] Space) :=
  fun θ y => fderiv ℝ (v θ) y

/-- The membership and three estimates in (7.38), for the actual error field.
The explicit finiteness clause prevents a divergent extended integral from
being hidden by `ENNReal.toReal`. Matrix norms use `matSq`, not operator norm. -/
def CorrectionBounds {k : ℕ} (Γ : Set Symmetry) (P : ℝ)
    (Wa : ℝ → Space → Space) (mw : ℝ) (β : Fin k → ℝ)
    (pin : Fin k → ℝ → Space → (Space →L[ℝ] Space)) (barℓ : Fin k → ℝ)
    (w : Space → ℝ) (ε M : ℝ) (W : ℝ → Space → Space) : Prop :=
  let v := correction P Wa W
  let G := gradient v
  ∃ (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (g : ℝ → Space → Space),
    IsPerturbation Γ P v G H g ∧
    periodLIntegral (fun θ y =>
      ‖secondDerivTrace (H θ y)‖ ^ 2 + w y * matSq (G θ y)) < ⊤ ∧
    weightedEnergy w G H + mw ^ 2 * (∑ i, β i ^ 2) ≤ 4 * ε ^ 2 ∧
    (∀ θ : ℝ, ∫⁻ y, ENNReal.ofReal (matSq (G θ y)) ≤ ENNReal.ofReal (M ^ 2)) ∧
    (∀ i, pinValue (pin i) G = barℓ i)

/-- The prescribed velocity symmetries, with physical similarity-time shifts. -/
def PrescribedSymmetries (Γ : Set Symmetry) (P : ℝ)
    (W : ℝ → Space → Space) : Prop :=
  ∀ γ ∈ Γ, ∀ s y, W (s + γ.2 * P) (γ.1 y) = γ.1 (W s y)

/-- All output clauses concern one parameter and one exact field. -/
def ExtendedConclusion {k : ℕ} (d : ExtendedCertificateData k) : Prop :=
  ∃ α ∈ d.params, ∃ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ),
    IsIdentityProfile (d.period α) W q ∧
    CorrectionBounds d.symmetries (d.period α) (d.profile α)
      d.multiplierWeight (d.multiplier α) d.pin (d.targetGap α)
      d.weightFn d.sizeBound d.supBound W ∧
    PrescribedSymmetries d.symmetries (d.period α) W

/-- The earlier certificate has a box parameter set and implicit multiplier
weight one. Its pin data also prescribe total, rather than perturbation, pins. -/
def OrdinaryConclusion {k : ℕ} (d : CertificateData k) : Prop :=
  ∃ α ∈ d.box, ∃ (W : ℝ → Space → Space) (q : ℝ → Space → ℝ),
    IsIdentityProfile (d.period α) W q ∧
    CorrectionBounds d.symmetries (d.period α) (d.profile α)
      1 (d.multiplier α) d.pin
      (fun i => d.target α i -
        pinValue (d.pin i) (fun θ y => fderiv ℝ (d.profile α θ) y))
      d.weightFn d.sizeBound d.supBound W ∧
    PrescribedSymmetries d.symmetries (d.period α) W

/-- Forget the specified identity-periodic profile only after packaging all formal profile bounds, including the pressure-gradient bound. -/
theorem IsIdentityProfile.profileExists {P : ℝ}
    {W : ℝ → Space → Space} {q : ℝ → Space → ℝ}
    (h : IsIdentityProfile P W q) : PeriodicSimilarityProfileExists := by
  rcases h with ⟨hP, hW, hq, heq, hdiv, hper, hne, C, hdec, hpress⟩
  refine ⟨W, q, P, LinearIsometryEquiv.refl ℝ Space, C,
    hP, hW, hq, heq, hdiv, ?_, hne, hdec, hpress⟩
  exact fun s y => (hper s y).trans rfl

/-- The retained output of Theorem 7.1 supplies the authors' smooth recurrent-profile premise. -/
theorem ExtendedConclusion.profileExists {k : ℕ} {d : ExtendedCertificateData k}
    (h : ExtendedConclusion d) : PeriodicSimilarityProfileExists := by
  rcases h with ⟨α, hα, W, q, hW, hbounds, hsym⟩
  exact hW.profileExists

/-- Changing a stored bound for the approximate field changes none of the
claimed output. The cell-layer construction is allowed to enlarge this bound. -/
theorem extendedConclusion_decay_update {k : ℕ} (d : ExtendedCertificateData k)
    (b : ℝ) : ExtendedConclusion ({d with decay := b}) ↔ ExtendedConclusion d := by
  rfl

end Breakdown.Theorem71

namespace Breakdown

/-- Full physical statement requested for the extended certificate.
This declaration is a proposition, not a proof of that proposition. -/
def Theorem71Extended : Prop :=
  ∀ {k : ℕ} (d : ExtendedCertificateData k),
    IsExtendedCertificate d → Theorem71.ExtendedConclusion d

/-- Corresponding statement for the earlier certificate format. -/
def Theorem71Ordinary : Prop :=
  ∀ {k : ℕ} (d : CertificateData k),
    IsCertificate d → Theorem71.OrdinaryConclusion d

end Breakdown
