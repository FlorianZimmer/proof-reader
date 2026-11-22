import Breakdown.Uniqueness.RegGlue
import Breakdown.Uniqueness.Restrict
import Breakdown.FreqTr.Realization
import Breakdown.Transfer.Exports
import Breakdown.Spectral.RealDichotomy
import Breakdown.Profile.Orbit
import Theorem11Rate

/-!
New wrapper source for the pinned authors' library, commit ad53419.
Status: IMPLEMENTED SOURCE, NOT YET COMPILED OR KERNEL CHECKED.

The proposed theorem preserves a specified profile and arbitrary epsilon.
The implementation combines the full-time abstract quarter-power rate with
the local smooth physical representatives supplied by the library. It does
not claim that the locally chosen representatives form one globally chosen
smooth pressure. Completion remains subject to checking this source.
-/

open MeasureTheory Set Real
open scoped ENNReal ContDiff Topology

noncomputable section

namespace Theorem11Core

open Breakdown Breakdown.Freq

/-- Reconstruct the public reading instance without importing the unrelated
global-solution nonexistence and physical uniqueness chain. -/
theorem realization_fieldReading : FieldReading realization velocity where
  injective := velocityInjective_holds
  rot := velocityCov_holds.1
  dil := velocityCov_holds.2

/-- The same public regularity input used by `mildRegular_realization`, with
a narrower import closure. No additional analytic hypothesis is introduced. -/
theorem realization_mildRegular : MildRegular realization velocity :=
  Breakdown.SmoothFlow.mildRegular_of_freq realization
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    heat_holds fieldOpRealized_holds h1Consistency_holds bilinH1Formula_holds
    bilin_holds.1 bilin_holds.2

def gradientSquare (f : Space → Space) (x : Space) : ℝ :=
  ∑ i : Fin 3, ‖fderiv ℝ f x (unitVector i)‖ ^ 2

def gradientNorm (f : Space → Space) : ℝ :=
  Real.sqrt (∫ x, gradientSquare f x)

/-- This bridge only applies to decay fields; its hypothesis must not be
silently omitted when applying it to a generated physical solution. -/
theorem gradientNorm_eq_embed_norm {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (Rlz : Realization E)
    (f : Space → Space) (hf : IsDecayField f) :
    gradientNorm f = ‖Rlz.embed f‖ := by
  unfold gradientNorm gradientSquare
  rw [← Rlz.embed_norm f hf, Real.sqrt_sq (norm_nonneg _)]

/-- Finiteness is returned separately, so a totalized Bochner integral cannot
masquerade as a finite homogeneous Sobolev norm. -/
theorem gradientSquare_integrable (f : Space → Space) (hf : IsDecayField f) :
    Integrable (gradientSquare f) volume := by
  unfold gradientSquare
  refine integrable_finsetSum _ fun i _ => ?_
  have hi := (Lp.memLp (partialX i (embedX f))).integrable_norm_pow two_ne_zero
  apply hi.congr
  filter_upwards [partial_holds.1 f hf i] with x hx
  rw [hx]
  rfl

/-- The norm identity holds on every abstract state, by density of test
fields. This deliberately exposes a bridge kept private in the source. -/
theorem norm_sq_eq_sum_partial (x : X) :
    ‖x‖ ^ 2 = ∑ i : Fin 3, ‖partialX i x‖ ^ 2 := by
  have hL : Continuous (fun z : X => ‖z‖ ^ 2) := continuous_norm.pow 2
  have hR : Continuous (fun z : X => ∑ i : Fin 3, ‖partialX i z‖ ^ 2) :=
    continuous_finsetSum _ fun i _ => ((partialX i).continuous.norm).pow 2
  have htest : (testSpan : Set X) ⊆
      {z : X | ‖z‖ ^ 2 = ∑ i : Fin 3, ‖partialX i z‖ ^ 2} := by
    intro z hz
    obtain ⟨φ, hφ, rfl⟩ := testSpan_holds z hz
    have hd := Breakdown.Freq.Internal.EmbedNegSsp.isDecayField_of_isTestField hφ
    have he : ∀ i : Fin 3,
        (fun y => ‖(partialX i (embedX φ) : Space → Space) y‖ ^ 2) =ᵐ[volume]
        (fun y => ‖fderiv ℝ φ y (unitVector i)‖ ^ 2) := by
      intro i
      filter_upwards [partial_holds.1 φ hd i] with y hy
      rw [hy]
      rfl
    have hi : ∀ i : Fin 3, Integrable
        (fun y => ‖fderiv ℝ φ y (unitVector i)‖ ^ 2) volume := fun i =>
      ((Lp.memLp (partialX i (embedX φ))).integrable_norm_pow two_ne_zero).congr (he i)
    show ‖embedX φ‖ ^ 2 = ∑ i : Fin 3, ‖partialX i (embedX φ)‖ ^ 2
    rw [embedNormLinear_holds.1 φ hd, integral_finsetSum _ (fun i _ => hi i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← integral_congr_ae (he i),
      ← real_inner_self_eq_norm_sq (partialX i (embedX φ)), L2.inner_def]
    congr 1
    funext y
    exact (real_inner_self_eq_norm_sq _).symm
  have hclosed := closure_minimal htest (isClosed_eq hL hR)
  rw [testDense_holds.2.closure_eq] at hclosed
  exact hclosed (mem_univ x)

/-- A physical derivative reading is sufficient for both finiteness and the
exact norm identity. No decay assumption on the physical representative is
needed in this version. -/
theorem gradient_reading (x : X) (f : Space → Space)
    (hread : ∀ i : Fin 3, (partialX i x : Space → Space) =ᵐ[volume]
      fun y => fderiv ℝ f y (unitVector i)) :
    Integrable (gradientSquare f) volume ∧ gradientNorm f = ‖x‖ := by
  have he : ∀ i : Fin 3,
      (fun y => ‖(partialX i x : Space → Space) y‖ ^ 2) =ᵐ[volume]
      (fun y => ‖fderiv ℝ f y (unitVector i)‖ ^ 2) := by
    intro i
    filter_upwards [hread i] with y hy
    rw [hy]
  have hi : ∀ i : Fin 3, Integrable
      (fun y => ‖fderiv ℝ f y (unitVector i)‖ ^ 2) volume := fun i =>
    ((Lp.memLp (partialX i x)).integrable_norm_pow two_ne_zero).congr (he i)
  refine ⟨integrable_finsetSum _ (fun i _ => hi i), ?_⟩
  have hn : ∫ y, gradientSquare f y = ‖x‖ ^ 2 := by
    unfold gradientSquare
    rw [integral_finsetSum _ (fun i _ => hi i), norm_sq_eq_sum_partial]
    apply Finset.sum_congr rfl
    intro i _
    rw [← integral_congr_ae (he i), ← real_inner_self_eq_norm_sq (partialX i x), L2.inner_def]
    congr 1
    funext y
    exact (real_inner_self_eq_norm_sq _).symm
  unfold gradientNorm
  rw [hn, Real.sqrt_sq (norm_nonneg _)]

theorem gradient_reading_of_h1 (f : Space → Space) (hf : IsH1Field f) :
    Integrable (gradientSquare f) volume ∧ gradientNorm f = ‖embedX f‖ :=
  gradient_reading (embedX f) f (h1Consistency_holds f hf).2.2

/-- Smooth velocity representatives of the same abstract trajectory agree
pointwise on overlaps. The pressure is deliberately absent from the conclusion. -/
theorem local_velocity_unique (u : ℝ → X) {T S : ℝ}
    {U V : ℝ → Space → Space} {p q : ℝ → Space → ℝ}
    (hU : IsSolutionOn T U p) (hV : IsSolutionOn S V q)
    (hUr : ∀ t ∈ Icc (0 : ℝ) T, (velocity (u t) : Space → Space) =ᵐ[volume] U t)
    (hVr : ∀ t ∈ Icc (0 : ℝ) S, (velocity (u t) : Space → Space) =ᵐ[volume] V t) :
    ∀ t ∈ Icc (0 : ℝ) (min T S), U t = V t := by
  intro t ht
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.trans (min_le_left _ _)⟩
  have htS : t ∈ Icc (0 : ℝ) S := ⟨ht.1, ht.2.trans (min_le_right _ _)⟩
  exact (Continuous.ae_eq_iff_eq volume
    (hU.contDiff_velocity htT).continuous (hV.contDiff_velocity htS).continuous).1
    ((hUr t htT).symm.trans (hVr t htS))

/-- Uniqueness rules out a zero at an earlier time: a zero mild state remains
zero, contradicting the strictly positive endpoint lower estimate. -/
theorem mild_ne_zero_of_late_rate {E : Type} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (F : MildFramework E)
    (u : ℝ → E) (hu : F.IsMildOn u 0 1) (c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (hlate : ∀ t ∈ Ico (0 : ℝ) 1, 1 - δ < t →
      c * (1 - t) ^ (-(1 / 4 : ℝ)) ≤ ‖u t‖) :
    ∀ t ∈ Ico (0 : ℝ) 1, u t ≠ 0 := by
  intro t ht hzero
  have hrest : F.toHeatBilinear.IsMildOn u t 1 := by
    refine ⟨hu.1.mono (Ico_subset_Ico_left ht.1), ?_⟩
    intro s hs
    have hs0 : s ∈ Ico (0 : ℝ) 1 := ⟨ht.1.trans hs.1, hs.2⟩
    exact Breakdown.restrict E F.toHeatBilinear u 0 t s ht.1 hs.1
      (hu.1.mono (Icc_subset_Ico_right hs.2)) (hu.2 t ht) (hu.2 s hs0)
  have hz : F.toHeatBilinear.IsMildOn (fun _ : ℝ => (0 : E)) t 1 := by
    refine ⟨continuousOn_const, fun s _ => ?_⟩
    simp
  have heq := (Breakdown.mildUnique E F.toHeatBilinear u (fun _ : ℝ => (0 : E)) t 1).1
    hrest hz hzero
  let a : ℝ := max t (1 - δ)
  let s : ℝ := (a + 1) / 2
  have ha1 : a < 1 := max_lt ht.2 (by linarith)
  have hta : t ≤ a := le_max_left _ _
  have hna : 1 - δ ≤ a := le_max_right _ _
  have hs0 : 0 ≤ s := by dsimp [s]; linarith [ht.1]
  have hs1 : s < 1 := by dsimp [s]; linarith
  have hts : t ≤ s := by dsimp [s]; linarith
  have hsnear : 1 - δ < s := by dsimp [s]; linarith
  have hl := hlate s ⟨hs0, hs1⟩ hsnear
  rw [heq s ⟨hts, hs1⟩, norm_zero] at hl
  exact (not_le_of_gt (mul_pos hc (Real.rpow_pos_of_pos (by linarith : 0 < 1 - s) _))) hl

structure SpaceWitness (W : ℝ → Space → Space) (ε : ℝ) where
  datum : Space → Space
  state : ℝ → X
  errorConstant : ℝ
  exponent : ℝ
  lowerConstant : ℝ
  upperConstant : ℝ
  datum_test : IsTestField datum
  initial : state 0 = realization.embed datum
  initial_gradient_finite : Integrable (gradientSquare (datum - W 0)) volume
  initial_gradient_close : gradientNorm (datum - W 0) < ε
  initial_abstract_close : ‖state 0 - realization.embed (W 0)‖ < ε
  mild : realization.F.IsMildOn state 0 1
  errorConstant_nonneg : 0 ≤ errorConstant
  exponent_pos : 0 < exponent
  exponent_lt_quarter : exponent < (1 / 4 : ℝ)
  lowerConstant_pos : 0 < lowerConstant
  upperConstant_pos : 0 < upperConstant
  convergence : ∀ t ∈ Ico (0 : ℝ) 1,
    ‖realization.F.D (1 - t) (state t) - realization.embed (W (-log (1 - t)))‖ ≤
      errorConstant * (1 - t) ^ exponent
  norm_rate : ∀ t ∈ Ico (0 : ℝ) 1,
    lowerConstant * (1 - t) ^ (-(1 / 4 : ℝ)) ≤ ‖state t‖ ∧
      ‖state t‖ ≤ upperConstant * (1 - t) ^ (-(1 / 4 : ℝ))
  local_physical : ∀ T : ℝ, 0 < T → T < 1 →
    ∃ (U : ℝ → Space → Space) (p : ℝ → Space → ℝ),
      IsSolutionOn T U p ∧ U 0 = datum ∧ EnergyBoundedOn T U ∧ GradientBoundedOn T U ∧
      ∀ t ∈ Icc (0 : ℝ) T, (velocity (state t) : Space → Space) =ᵐ[volume] U t

/-- The supplied profile is retained literally; epsilon is never specialized
to one. Rates here are in the concrete frequency-space norm. -/
theorem space_core (W : ℝ → Space → Space) (q : ℝ → Space → ℝ)
    (P : ℝ) (R : Space ≃ₗᵢ[ℝ] Space) (A : ℝ)
    (hP : 0 < P) (hprofile : IsSimilarityProfile W q A)
    (hperiodic : ∀ s y, W (s + P) y = R (W s (R.symm y)))
    (hnonzero : ∃ s y, W s y ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    Nonempty (SpaceWitness W ε) := by
  let w : ℝ → X := fun s => realization.embed (W s)
  have horbit : realization.F.IsOrbit (realization.rot R) w P :=
    embeddedProfileOrbit_holds X realization W q P R A hP hprofile hperiodic hnonzero
  obtain ⟨u, hu0, hclose, hu, C, κ, hκ, herror⟩ :=
    transferHolds_of_dichotomy dichotomyHolds X realization.F (realization.rot R)
      (realization.rot_commutes R) w P horbit realization.test realization.test_dense ε hε
  obtain ⟨φ, hφ, hφu⟩ := realization.test_spec (u 0) hu0
  have hdec : IsDecayField (W 0) := sliceDecay_holds W q A hprofile 0
  have hφdec : IsDecayField φ :=
    Breakdown.Freq.Internal.EmbedNegSsp.isDecayField_of_isTestField hφ
  have hdiff : IsDecayField (φ - W 0) := decayFieldSub_holds φ (W 0) hφdec hdec
  have hphysicalClose : gradientNorm (φ - W 0) < ε := by
    rw [gradientNorm_eq_embed_norm realization _ hdiff,
      realization.embed_sub φ (W 0) hφdec hdec, hφu]
    exact hclose
  have hC : 0 ≤ C := by
    have hh := herror 0 (show (0 : ℝ) ∈ Ico 0 1 by constructor <;> norm_num)
    have hh' : ‖realization.F.D (1 - 0) (u 0) - w (-log (1 - 0))‖ ≤ C := by
      simpa using hh
    exact (norm_nonneg _).trans hh'
  let κ' : ℝ := min κ (1 / 8)
  have hκ' : 0 < κ' := lt_min hκ (by norm_num)
  have hκ'quarter : κ' < (1 / 4 : ℝ) :=
    lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have herror' : ∀ t ∈ Ico (0 : ℝ) 1,
      ‖realization.F.D (1 - t) (u t) - w (-log (1 - t))‖ ≤ C * (1 - t) ^ κ' := by
    intro t ht
    exact (herror t ht).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge (by linarith [ht.2] : 0 < 1 - t)
        (by linarith [ht.1] : 1 - t ≤ 1) (min_le_left _ _)) hC)
  obtain ⟨M, hM⟩ := orbitBound X realization.F (realization.rot R) w P horbit
  obtain ⟨c, hc, hlow⟩ := orbitNorm X realization.F (realization.rot R)
    (realization.rot_commutes R) w P horbit
  obtain ⟨δ, hδ, hlate⟩ := Theorem11Rate.late_rate u
    (fun t => realization.F.D (1 - t) (u t)) (fun t => w (-log (1 - t))) c M C κ hc hκ
    (fun t _ => hlow _) (fun t _ => hM _)
    (fun t ht => realization.F.D_norm _ (by linarith [ht.2]) _) herror
  have hne : ∀ t ∈ Ico (0 : ℝ) 1, u t ≠ 0 :=
    mild_ne_zero_of_late_rate realization.F u hu (c / 2) δ (half_pos hc) hδ
      (fun t ht hn => (hlate t ht hn).1)
  obtain ⟨a, b, ha, hb, hrates⟩ := Theorem11Rate.globalize_rate u hu.1 hne
    (c / 2) (M + c / 2) δ (half_pos hc) hδ hlate
  refine ⟨{
    datum := φ
    state := u
    errorConstant := C
    exponent := κ'
    lowerConstant := a
    upperConstant := b
    datum_test := hφ
    initial := hφu.symm
    initial_gradient_finite := gradientSquare_integrable _ hdiff
    initial_gradient_close := hphysicalClose
    initial_abstract_close := hclose
    mild := hu
    errorConstant_nonneg := hC
    exponent_pos := hκ'
    exponent_lt_quarter := hκ'quarter
    lowerConstant_pos := ha
    upperConstant_pos := hb
    convergence := herror'
    norm_rate := hrates
    local_physical := ?_ }⟩
  intro T hT hT1
  exact realization_mildRegular φ hφ u T hT
    (realization.F.isMildOnIcc_of_isMildOn hu hT.le hT1) hφu.symm

end Theorem11Core
