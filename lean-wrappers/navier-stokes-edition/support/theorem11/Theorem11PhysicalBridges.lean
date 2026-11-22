import Theorem11Challenge
import Breakdown.FreqTr.EmbedMem
import Breakdown.FreqTr.EmbedNegSsp
import Breakdown.Profile.Dilate
import Breakdown.Profile.DilateDecay
import Breakdown.Profile.Slice
import Breakdown.Uniqueness.Basic

/-!
Physical norm bridges for the Theorem 1.1 wrapper.
Authoring status: NOT COMPILED. These lemmas apply to explicitly decaying
fields. They do not assert decay of every transferred physical solution.
-/

open MeasureTheory Set Real
open scoped ContDiff

noncomputable section

namespace Theorem11

/-- Decay supplies integrability, independently of the totalized real integral. -/
theorem finiteGradient_of_decay {f : VectorField}
    (hf : Breakdown.IsDecayField f) : FiniteGradient f := by
  change Integrable (fun x : Breakdown.Space =>
    ∑ i : Fin 3, ‖Breakdown.Freq.partialField f i x‖ ^ 2) volume
  apply integrable_finsetSum
  intro i _
  have hp := Breakdown.Freq.Internal.EmbedMem.memLp_partialField hf i
  exact (memLp_two_iff_integrable_sq_norm hp.aestronglyMeasurable).1 hp

/-- Read the realization's squared-norm identity as the physical Hdot1 norm. -/
theorem gradientNorm_eq_embed {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X]
    (Rlz : Breakdown.Realization X) {f : VectorField}
    (hf : Breakdown.IsDecayField f) : gradientNorm f = ‖Rlz.embed f‖ := by
  change Real.sqrt (∫ x, ∑ i : Fin 3,
    ‖fderiv ℝ f x (Breakdown.unitVector i)‖ ^ 2) = ‖Rlz.embed f‖
  rw [← Rlz.embed_norm f hf, Real.sqrt_sq (norm_nonneg _)]

/-- The norm identity and its finiteness guard travel together. -/
theorem finiteGradient_and_norm_eq_embed {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X]
    (Rlz : Breakdown.Realization X) {f : VectorField}
    (hf : Breakdown.IsDecayField f) :
    FiniteGradient f ∧ gradientNorm f = ‖Rlz.embed f‖ :=
  ⟨finiteGradient_of_decay hf, gradientNorm_eq_embed Rlz hf⟩

/-- This is the precise bridge for the requested initial-data tolerance. -/
theorem initial_approximation_is_physical {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X]
    (Rlz : Breakdown.Realization X) {φ f : VectorField} {ε : ℝ}
    (hφ : Breakdown.IsTestField φ) (hf : Breakdown.IsDecayField f)
    (hε : ‖Rlz.embed φ - Rlz.embed f‖ < ε) :
    FiniteGradient (φ - f) ∧ gradientNorm (φ - f) < ε := by
  have hφd := Breakdown.Freq.Internal.EmbedNegSsp.isDecayField_of_isTestField hφ
  have hd := Breakdown.decayFieldSub_holds φ f hφd hf
  refine ⟨finiteGradient_of_decay hd, ?_⟩
  rw [gradientNorm_eq_embed Rlz hd, Rlz.embed_sub φ f hφd hf]
  exact hε

/-- Dilation transports the physical norm with exactly the quarter-power. -/
theorem gradientNorm_dilate {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X]
    (Rlz : Breakdown.Realization X) {f : VectorField} {μ : ℝ}
    (hμ : 0 < μ) (hf : Breakdown.IsDecayField f) :
    FiniteGradient (Breakdown.dilateField μ f) ∧
      gradientNorm (Breakdown.dilateField μ f) = μ ^ (1 / 4 : ℝ) * gradientNorm f := by
  have hd := Breakdown.decayFieldDilate_holds Breakdown.dilateCalculus_holds μ f hμ hf
  refine ⟨finiteGradient_of_decay hd, ?_⟩
  rw [gradientNorm_eq_embed Rlz hd, ← Rlz.embed_dilate μ f hμ hf,
    Rlz.F.D_norm μ hμ, gradientNorm_eq_embed Rlz hf]

/-- Translate the independent contract's profile predicate to the library's
witness-level profile record. No profile is reselected. -/
theorem libraryProfile_to_similarity {W : Velocity} {q : Pressure} {P A : ℝ}
    {R : Space ≃ₗᵢ[ℝ] Space} (h : IsLibraryProfile W q P R A) :
    Breakdown.IsSimilarityProfile W q A := by
  rcases h with ⟨_, hs, hq, hr, hd, _, _, hb, hp⟩
  exact ⟨hs, hq, hr, hd, hb, hp⟩

/-- Existence is only used here for compatibility with the old endpoint;
the new quantitative construction should use the witness-level lemma above. -/
theorem libraryProfile_to_exists {W : Velocity} {q : Pressure} {P A : ℝ}
    {R : Space ≃ₗᵢ[ℝ] Space} (h : IsLibraryProfile W q P R A) :
    Breakdown.PeriodicSimilarityProfileExists := by
  exact ⟨W, q, P, R, A, h⟩


/-- Restrict the authors' closed-interval physical reading to the independent
half-open statement vocabulary. -/
theorem smooth_before_of_library {T : ℝ} {φ : VectorField} {U : Velocity} {p : Pressure}
    (hs : Breakdown.IsSolutionOn T U p) (hi : U 0 = φ) :
    IsSmoothSolutionBefore 1 T φ U p := by
  refine { smooth_velocity := hs.smooth_velocity.mono ?_
           smooth_pressure := hs.smooth_pressure.mono ?_
           initial := fun x => congrFun hi x
           momentum := ?_
           incompressible := ?_ }
  · intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.le⟩, hz.2⟩
  · intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.le⟩, hz.2⟩
  · intro t ht x
    -- `simpa` compares at reducible transparency, which does not unfold the
    -- two vocabularies; they agree by unfolding, so `exact` closes the goal.
    rw [one_smul]
    exact hs.momentum t ht x
  · intro t ht x
    exact hs.incompressible t ⟨ht.1, ht.2.le⟩ x

/-- The energy bound here is for this particular T. No uniformity in T is
introduced by translating the proposition. -/
theorem energy_before_of_library {T : ℝ} {U : Velocity}
    (hE : Breakdown.EnergyBoundedOn T U) : UniformFiniteEnergyBefore T U := by
  obtain ⟨E, hE⟩ := hE
  refine ⟨max E 0, le_max_right _ _, fun t ht => ?_⟩
  exact (hE t ⟨ht.1, ht.2.le⟩).trans
    (ENNReal.ofReal_le_ofReal (le_max_left E 0))

end Theorem11
