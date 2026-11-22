import SectionSevenNodes
import Theorem71Solution
import Theorem11Solution
import SpatialScaling
import Breakdown.Uniqueness.Space

/-!
# Section 7: certificate construction and the analytic estimates

These statements describe the exact propositions reduced to the authors' library.
The accompanying table distinguishes their corrected formal forms from the printed
statements. In particular, a formal certificate is an assumption, not supplied data;
operators on the derivative graph are not silently identified with operators on
all physical perturbations. Theorem 7.1 keeps the chosen parameter and field.
-/

open MeasureTheory Filter
open scoped ContDiff ENNReal Topology
noncomputable section
namespace NavierStokes
open Breakdown Breakdown.Cert Breakdown.Freq Breakdown.Theorem71

/-- Theorem 7.1, under the formal extended-certificate hypotheses: one parameter
alpha gives a smooth nonzero profile of period S(alpha), with identity isometry,
the actual correction satisfying all three bounds (7.38), and the symmetries
(7.39). The profile includes decay through two spatial derivatives and the bound
on its pressure gradient. The approximate-profile and certificate assumptions are
those of IsExtendedCertificate, which are stronger than the printed definition. -/
theorem theorem_7_1 {k : ℕ} (d : ExtendedCertificateData k)
    (certificate : IsExtendedCertificate d) :
    ∃ α ∈ d.params, ∃ (W : VelField) (q : ℝ → Space → ℝ),
      IsIdentityProfile (d.period α) W q ∧
      CorrectionBounds d.symmetries (d.period α) (d.profile α)
        d.multiplierWeight (d.multiplier α) d.pin (d.targetGap α)
        d.weightFn d.sizeBound d.supBound W ∧
      PrescribedSymmetries d.symmetries (d.period α) W := by
  exact Breakdown.theorem71_extended d certificate

/-- Corollary 7.2 under the formal certificate hypotheses: the selected profile of
Theorem 7.1 gives, for every epsilon>0, one smooth finite-energy space solution on
[0,1) with the two-sided blow-up rate, the physical-variable error estimate (1.6)
relative to this same profile, uniqueness and no finite-energy smooth continuation. The
authors' nonexistence conclusions also hold on space and on the torus at every
positive viscosity. The quantitative torus trajectory remains a separate target. -/
theorem corollary_7_2 {k : ℕ} (d : ExtendedCertificateData k)
    (certificate : IsExtendedCertificate d) :
    ∃ α ∈ d.params, ∃ (W : VelField) (q : ℝ → Space → ℝ),
      IsIdentityProfile (d.period α) W q ∧
      CorrectionBounds d.symmetries (d.period α) (d.profile α)
        d.multiplierWeight (d.multiplier α) d.pin (d.targetGap α)
        d.weightFn d.sizeBound d.supBound W ∧
      PrescribedSymmetries d.symmetries (d.period α) W ∧
      (∀ ε : ℝ, 0 < ε → SpacePhysicalBlowupConclusion W ε) ∧
      BreakdownOnSpace ∧ BreakdownOnTorus := by
  obtain ⟨α, hα, W, q, hprofile, hbounds, hsym⟩ := theorem_7_1 d certificate
  have library : ∃ A : ℝ, Theorem11.IsLibraryProfile W q (d.period α)
      (LinearIsometryEquiv.refl ℝ Space) A := by
    rcases hprofile with ⟨hP, hW, hq, hEq, hDiv, hRec, hNonzero, A, hDecay, hPressure⟩
    exact ⟨A, hP, hW, hq, hEq, hDiv,
      fun s y => (hRec s y).trans rfl, hNonzero, hDecay, hPressure⟩
  obtain ⟨A, hA⟩ := library
  exact ⟨α, hα, W, q, hprofile, hbounds, hsym,
    fun ε hε => spacePhysicalBlowup_of_spaceBlowup W ε
      (Theorem11.theorem11SpaceBlowup W q (d.period α)
        (LinearIsometryEquiv.refl ℝ Space) A hA ε hε),
    Breakdown.breakdownOnSpace_of_profile hprofile.profileExists,
    Breakdown.Periodic.breakdownOnTorus_of_profile hprofile.profileExists⟩

/-- Lemma 7.4 for the constructed free inverse: it has a continuous period-one
representative in the homogeneous Sobolev space, satisfies the integrated energy
identity, and obeys the period energy inequality. The stored second component is
minus the Laplacian. Extending this statement to every physical perturbation and
spelling out local absolute continuity and the differentiated identity are
separate obligations; they are not hypotheses of this theorem. -/
theorem lemma_7_4 (P : ℝ) (period_positive : 0 < P) (f : HH) :
    (∃ c : ℝ → X, Continuous c ∧ (∀ θ, c (θ + 1) = c θ) ∧
      (∀ᵐ θ : ℝ, c θ = gradPart (sliceOf (freeInv P f) (θ : TimeCircle))) ∧
      ∀ a b, a ≤ b → (1 / (2 * P)) * (‖c b‖ ^ 2 - ‖c a‖ ^ 2) =
        ∫ θ in a..b, (inner ℝ ((f : TimeCircle → HBar) (θ : TimeCircle))
            (secondPart (sliceOf (freeInv P f) (θ : TimeCircle)))
          - ‖secondPart (sliceOf (freeInv P f) (θ : TimeCircle))‖ ^ 2
          - (1 / 4 : ℝ) * ‖c θ‖ ^ 2)) ∧
    ‖secondCLM (freeInv P f)‖ ^ 2 + (1 / 4 : ℝ) * ‖gradCLM (freeInv P f)‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  let n := Internal.sectionSevenNodes
  exact ⟨Breakdown.Cert.Internal.FreeEnergyLocal.exists_energyCurve
    n.propagator n.gradientInverse n.graph n.freeInverse period_positive f,
    (n.freeInverse P period_positive).2 f⟩

/-- Proposition 7.5 in the derivative-graph representation: a bounded linear free
inverse exists, preserves every specified symmetry class, and depends weakly
continuously on a positive period and bounded weakly convergent forcing.
This is not a bijection statement on every physical field in the printed domain;
local strong convergence of the entire sequence is not concluded here. -/
theorem proposition_7_5 (P : ℝ) (period_positive : 0 < P) :
    (∃ T : HH →L[ℝ] XX, ∀ f, gradCLM (T f) = gradInv P f) ∧
    (∀ (Γ : Set Symmetry) (f : HH), f ∈ invariantHH Γ →
      IsInvariantXX Γ (freeInv P f)) ∧
    (∀ (periods : ℕ → ℝ) (forces : ℕ → HH) (force : HH),
      (∀ n, 0 < periods n) → Tendsto periods atTop (𝓝 P) →
      (∃ C, ∀ n, ‖forces n‖ ≤ C) →
      (∀ y : HH, Tendsto (fun n => inner ℝ (forces n) y) atTop (𝓝 (inner ℝ force y))) →
      ∀ y : XX, Tendsto (fun n => inner ℝ (freeInv (periods n) (forces n)) y) atTop
        (𝓝 (inner ℝ (freeInv P force) y))) := by
  let n := Internal.sectionSevenNodes
  exact ⟨(n.freeInverse P period_positive).1,
    fun Γ f hf => n.equivariance Γ P period_positive f hf,
    fun periods forces force hpositive hperiods hbounded hweak =>
      n.periodContinuity periods P forces force period_positive hpositive hperiods hbounded hweak⟩

/-- Lemma 7.6: the weighted spatial estimate (7.48), followed by the weighted
quadratic estimate for two graph fields. The second field must have
finite essential supremum of its gradient norm. The conclusion bounds both the
physical product and its solenoidal projection; taking equal fields gives the
nonlinear estimate used in the certificate argument. -/
theorem lemma_7_6 :
    (∀ w₀ : ℝ, 0 < w₀ → ∀ u : XBar, ∀ᵐ y,
      ‖(velocity (gradPart u) : Space → Space) y‖ ^ 2 ≤
        supBoundFactor w₀ ^ 2 * (‖secondPart u‖ ^ 2 + w₀ * ‖gradPart u‖ ^ 2)) ∧
    (∀ (w : Space → ℝ) (w₀ : ℝ), IsAdmissibleWeight w w₀ →
      ∀ u v : XX, supGrad v < ⊤ →
        IsPeriodicField (productField u v) ∧
        periodNorm (productField u v) ≤
          supBoundFactor w₀ * Real.sqrt (energyW w u) * (supGrad v).toReal ∧
        ‖productH u v‖ ≤ supBoundFactor w₀ * Real.sqrt (energyW w u) * (supGrad v).toReal) := by
  refine ⟨?_, Internal.sectionSevenNodes.product⟩
  intro w₀ hw u
  have weighted : (1 / (2 * Real.pi)) * ‖gradPart u‖ * ‖secondPart u‖ ≤
      supBoundFactor w₀ ^ 2 * (‖secondPart u‖ ^ 2 + w₀ * ‖gradPart u‖ ^ 2) := by
    simpa only [one_pow, mul_one] using
      (Breakdown.Cert.Internal.ProductBound.slice_real_le
        (a := ‖gradPart u‖) (b := ‖secondPart u‖) (c := 1) (K := 1)
        hw (norm_nonneg _) (norm_nonneg _) (by norm_num) le_rfl)
  filter_upwards [Internal.sectionSevenNodes.spatialBound u] with y hy
  exact hy.trans weighted

/-- Lemma 7.7 for projected convection: at each admissible parameter its norm is
bounded by a constant times the gradient norm, it preserves the specified
symmetry class, and its composition with the free inverse is compact. The target
is the solenoidal Hilbert space. Compactness of the unprojected physical operator
and a constant depending only on the displayed decay bound are not asserted. -/
theorem lemma_7_7 {k : ℕ} (d : ExtendedCertificateData k)
    (certificate : IsExtendedCertificate d) (α : Fin k → ℝ) (parameter_mem : α ∈ d.params) :
    (∃ C, ∀ u : XX, ‖convection d.toCertificateData α u‖ ≤ C * ‖gradCLM u‖) ∧
    (∀ u : XX, IsInvariantXX d.symmetries u →
      convection d.toCertificateData α u ∈ invariantHH d.symmetries) ∧
    IsCompactOperator ((convection d.toCertificateData α).comp (freeInv (d.period α))) := by
  let n := Internal.sectionSevenNodes
  exact ⟨(n.convection d certificate α parameter_mem).2.1,
    fun u hu => ((n.invariance d certificate α parameter_mem).1 u hu).1,
    n.convectionCompact d certificate α parameter_mem⟩

set_option maxHeartbeats 1000000 in
/-- Proposition 7.8 in forcing coordinates: for a normalized formal certificate,
every invariant forcing and every pin target has exactly one invariant bordered
solution (f,beta). The physical correction is freeInv(S(alpha),f). Normalized
means multiplier weight one, coincident model and approximate profile, zero gap
and zero form shift; the theorem does not silently assume those equalities. -/
theorem proposition_7_8 {k : ℕ} (d : ExtendedCertificateData k)
    (certificate : IsExtendedCertificate d)
    (unit_multiplier_weight : d.multiplierWeight = 1)
    (model_is_profile : d.model = d.profile)
    (zero_gap : d.gapSize = 0) (zero_form_shift : d.formShift = 0)
    (α : Fin k → ℝ) (parameter_mem : α ∈ d.params)
    (F : HH) (forcing_invariant : F ∈ invariantHH d.symmetries) (pin_target : Fin k → ℝ) :
    ∃! x : HH × (Fin k → ℝ),
      x.1 ∈ invariantHH d.symmetries ∧ bordered d.toCertificateData α x = (F, pin_target) := by
  have normal : IsNormalExtendedCertificate d :=
    ⟨certificate, unit_multiplier_weight, model_is_profile, zero_gap, zero_form_shift⟩
  have bordered_holds := Internal.sectionSevenNodes.borderedInverse d normal α parameter_mem
  obtain ⟨⟨T, inverse⟩, injective⟩ := bordered_holds
  have ht := inverse (F, pin_target) forcing_invariant
  refine ⟨T (F, pin_target), ht, ?_⟩
  intro y hy
  exact injective y (T (F, pin_target)) hy.1 ht.1 (hy.2.trans ht.2.symm)

/-- Proposition 7.9 for the constructed inverse: the essential supremum of the
gradient is finite and satisfies the displayed estimate with the certificate's
weight, period, twist and form bound. The forcing norm is that of the projected
bordered residual. Replacing it by an arbitrary physical residual and the
essential supremum by the all-time supremum needs the representative bridge. -/
theorem proposition_7_9 {k : ℕ} (d : ExtendedCertificateData k)
    (certificate : IsExtendedCertificate d) (α : Fin k → ℝ) (parameter_mem : α ∈ d.params)
    (f : HH) (forcing_invariant : f ∈ invariantHH d.symmetries) (β : Fin k → ℝ) :
    supGrad (freeInv (d.period α) f) < ⊤ ∧
    (supGrad (freeInv (d.period α) f)).toReal ^ 2 ≤
      (1 / d.weight + 2 * (d.period α / d.twist) * d.formBound)
          * energyW d.weightFn (freeInv (d.period α) f)
        + 2 * (d.period α / d.twist)
          * (‖(bordered d.toCertificateData α (f, β)).1‖ + d.actuatorBound * vecNorm β)
          * Real.sqrt (energyW d.weightFn (freeInv (d.period α) f)) := by
  exact Internal.sectionSevenNodes.supremumBound d certificate α parameter_mem f forcing_invariant β

/-- Proposition 7.10 after the authors' two certificate reductions: some parameter
has a held nonlinear solution with the equation, pin values, size bound and finite
essential gradient bound, and its total multiplier vanishes. The returned
multiplier correction is exactly minus omega times the original multiplier.
Theorem 7.1 separately transports the bounds to the actual smooth correction. -/
theorem proposition_7_10 {k : ℕ} (d : ExtendedCertificateData k)
    (certificate : IsExtendedCertificate d) :
    ∃ α ∈ d.params, ∃ (f : HH) (β : Fin k → ℝ),
      (normalData d).IsHeldSolution α f β ∧
      (normalData d).multiplier α + β = 0 ∧
      ∀ i, β i = -(d.multiplierWeight * d.multiplier α i) := by
  obtain ⟨a⟩ := heldWitness_exists d certificate
  exact ⟨a.parameter, a.parameter_mem, a.forcing, a.multiplierCorrection,
    a.held, a.multiplier_cancel, a.multiplierCorrection_eq⟩

/-- Proposition 7.11 with the formal weak-profile assumptions made explicit by
IsSigmaProfile: a nonzero period-one weak field with uniformly bounded L6 and
homogeneous H1 norms, a square-integrable weak Hessian over a period, and the
weak similarity equation has a smooth profile representative at this same period.
If x is its continuous homogeneous-H1 representative, equality with the input
field holds at every similarity time, almost everywhere in space. The weak
Hessian assumption is stronger than the printed proposition. -/
theorem proposition_7_11 (P C : ℝ) (V : VelField) (G : GradField) (H : SecondField)
    (weak_profile : IsSigmaProfile P V G H C) (x : ℝ → X)
    (continuous_representative : Continuous x)
    (represents_field : ∀ θ : ℝ, (velocity (x θ) : Space → Space) =ᵐ[volume] V θ) :
    ∃ (W : VelField) (q : ℝ → Space → ℝ),
      IsIdentityProfile P W q ∧
      ∀ s : ℝ, W s =ᵐ[volume] V (P⁻¹ * s) := by
  have weak_at := Breakdown.weakPeriodicSimilarityProfileOf_sigma_keep weak_profile
  obtain ⟨w, orbit, reads⟩ := weakOrbitKeeping weak_at
  have xcont : Continuous (fun s : ℝ => x (P⁻¹ * s)) :=
    continuous_representative.comp (continuous_const.mul continuous_id)
  have ae_equal : w =ᵐ[volume] (fun s : ℝ => x (P⁻¹ * s)) := by
    filter_upwards [reads] with s hs
    have hs' : (velocity (w s) : Space → Space) =ᵐ[volume] V (P⁻¹ * s) := hs
    exact Breakdown.WeakProfile.EditionOrbitAux.eq_of_velocity_ae
      (hs'.trans (represents_field (P⁻¹ * s)).symm)
  have equal : w = (fun s : ℝ => x (P⁻¹ * s)) :=
    (orbit.1.ae_eq_iff_eq volume xcont).mp ae_equal
  obtain ⟨W, q, D, smooth, velocity_eq, decay⟩ := Transport.regularizeKeeping orbit
  refine ⟨W, q, ?_, ?_⟩
  · exact ⟨smooth.period_pos, smooth.smooth_field, smooth.smooth_pressure,
      smooth.residual, smooth.divergence, fun s y => (smooth.periodic s y).trans rfl,
      smooth.nonzero, D, decay.1, decay.2⟩
  · intro s
    have reading : (velocity (w s) : Space → Space) =ᵐ[volume] V (P⁻¹ * s) := by
      rw [equal]
      exact represents_field (P⁻¹ * s)
    exact (velocity_eq s).symm.trans reading

end NavierStokes
