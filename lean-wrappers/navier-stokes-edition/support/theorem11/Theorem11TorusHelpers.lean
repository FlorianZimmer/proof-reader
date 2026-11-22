/-
Copyright status: new wrapper code; the authors' proof library is imported.
Validation: NOT COMPILED in the return-producing environment.

These are local/quantitative bridge lemmas, not a proof of Theorem11Torus.
In particular, equality on B_(1/16) concerns the approximate field. The final
solution is a perturbation and is not asserted to equal the profile there.
-/
import Breakdown.Torus.ApproxLinks
import Breakdown.Torus.SelfSimilar
import Breakdown.Torus.Cutoff
import Breakdown.Torus.Glue
import Breakdown.Torus.GlueUnbounded
import Breakdown.Transfer.Main

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.Theorem11.Torus

open Breakdown.Periodic

/-- Assemble just the approximation facts needed by these wrappers. -/
theorem approximation_properties : ApproxFieldProperties :=
  approxFieldProperties selfSimilarSolves homotopyCurl (cutoffDivergenceFree homotopyCurl)

/-- The normalized approximate pieces agree with the periodic physical field. -/
theorem approximation_links : ApproxLinks :=
  approxLinks approximation_properties transplantSmooth (freqTrSeriesSpec coefDeriv)

/-- The paper's torus phase is log(T / (T-t)), not -log(T-t). -/
theorem similarityTime_eq_log_ratio {T t : ℝ} (hT : 0 < T) (ht : t < T) :
    similarityTime T t = Real.log (T / (T - t)) := by
  have hgap : 0 < T - t := sub_pos.2 ht
  rw [similarityTime, Real.log_div hgap.ne' hT.ne', Real.log_div hT.ne' hgap.ne']
  ring

/-- Translating the library's cell center to the origin removes the spatial
center from the self-similar formula. This is only a formula identity. -/
theorem selfSimilar_translate_center (W : ℝ → Space → Space) (T t : ℝ) (x : Space) :
    selfSimilar W T t (Periodic.center + x) =
      (T - t) ^ (-(1 / 2 : ℝ)) •
        W (similarityTime T t) ((T - t) ^ (-(1 / 2 : ℝ)) • x) := by
  simp only [selfSimilar, add_sub_cancel_left]

/-- The Fourier-space norm is the physical full H¹ norm on the unit cell.
The spatial gradient is measured by the sum of squared basis derivatives,
not by the operator norm of a Fréchet derivative. -/
theorem norm_toV_eq_physicalH1 {f : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hp : IsPeriodic f)
    (hd : ∀ x, divergenceAt f x = 0) :
    ‖toV f‖ = Real.sqrt ((∫ x in cell, ‖f x‖ ^ 2) +
      ∑ i : Fin 3, ∫ x in cell, ‖fderiv ℝ f x (unitVector i)‖ ^ 2) := by
  rw [← Transplant.Internal.norm_toV_sq hf hp hd,
    Real.sqrt_sq (norm_nonneg (toV f))]

/-- The fixed radius is exactly 1/16; the library's center is the center of
its chosen fundamental cube. -/
theorem approxField_eq_selfSimilar_on_innerBall
    {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C T t : ℝ}
    (hW : IsSimilarityProfile W q C) (hT : 0 < T) (ht : t < T)
    {x : Space} (hx : dist x Periodic.center ≤ (1 / 16 : ℝ)) :
    approxField W T t x = selfSimilar W T t x := by
  apply ((approximation_properties W q C T hW hT).2.2 t ht x).2.2
  have hr : centralRadius / 4 = (1 / 16 : ℝ) := by norm_num [centralRadius]
  simpa only [hr] using hx

/-- Periodization leaves the same inner ball unchanged. -/
theorem approxPeriodic_eq_selfSimilar_on_innerBall
    {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C T t : ℝ}
    (hW : IsSimilarityProfile W q C) (hT : 0 < T) (ht : t < T)
    {x : Space} (hx : dist x Periodic.center ≤ (1 / 16 : ℝ)) :
    approxPeriodic W T t x = selfSimilar W T t x := by
  have he : approxField W T t (wrap x) = approxField W T t (x - freq (0 : Lattice)) := by
    apply ApproxLinks.Internal.wrap_eq_shift
      (ApproxLinks.Internal.approxField_far approximation_properties hW hT ht)
    intro j
    have hc := Transplant.Internal.abs_apply_le (x - Periodic.center) j
    rw [PiLp.sub_apply, Transplant.Internal.center_apply] at hc
    have hx' : ‖x - Periodic.center‖ ≤ (1 / 16 : ℝ) := by
      simpa only [dist_eq_norm] using hx
    simp only [Pi.zero_apply, Int.cast_zero, sub_zero]
    linarith
  calc
    approxPeriodic W T t x = approxField W T t x := by
      simpa only [approxPeriodic, Transplant.Internal.freq_zero, sub_zero] using he
    _ = selfSimilar W T t x :=
      approxField_eq_selfSimilar_on_innerBall hW hT ht hx

/-- Local equality supplies the ordinary Mathlib spatial derivative identity.
The open ball is enough for the local H¹ estimate. -/
theorem fderiv_approxPeriodic_eq_on_innerBall
    {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C T t : ℝ}
    (hW : IsSimilarityProfile W q C) (hT : 0 < T) (ht : t < T)
    {x : Space} (hx : dist x Periodic.center < (1 / 16 : ℝ)) :
    fderiv ℝ (approxPeriodic W T t) x = fderiv ℝ (selfSimilar W T t) x := by
  have he : approxPeriodic W T t =ᶠ[𝓝 x] selfSimilar W T t :=
    Filter.eventually_of_mem
      (Metric.isOpen_ball.mem_nhds (show x ∈ Metric.ball Periodic.center (1 / 16 : ℝ) from hx))
      (fun y hy => approxPeriodic_eq_selfSimilar_on_innerBall hW hT ht
        (show dist y Periodic.center ≤ (1 / 16 : ℝ) from le_of_lt hy))
  exact he.fderiv_eq

/-- The local error against the true profile has exactly the same derivative
as the error against the periodic approximant. This is an identity, without
an estimate or an additional tail term. -/
theorem fderiv_error_eq_on_innerBall
    {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C T t : ℝ}
    (hW : IsSimilarityProfile W q C) (hT : 0 < T) (ht : t < T)
    (v : Space → Space) {x : Space} (hx : dist x Periodic.center < (1 / 16 : ℝ)) :
    fderiv ℝ (fun y => v y - approxPeriodic W T t y) x =
      fderiv ℝ (fun y => v y - selfSimilar W T t y) x := by
  have he : (fun y => v y - approxPeriodic W T t y) =ᶠ[𝓝 x]
      (fun y => v y - selfSimilar W T t y) :=
    Filter.eventually_of_mem
      (Metric.isOpen_ball.mem_nhds (show x ∈ Metric.ball Periodic.center (1 / 16 : ℝ) from hx))
      (fun y hy => by
        try dsimp only
        rw [approxPeriodic_eq_selfSimilar_on_innerBall hW hT ht
          (show dist y Periodic.center ≤ (1 / 16 : ℝ) from le_of_lt hy)])
  exact he.fderiv_eq

def localGradientNorm (f : Space → Space) : ℝ :=
  Real.sqrt (∫ x in Metric.ball Periodic.center (1 / 16 : ℝ),
    ∑ i : Fin 3, ‖fderiv ℝ f x (unitVector i)‖ ^ 2)

theorem innerBall_subset_cell : Metric.ball Periodic.center (1 / 16 : ℝ) ⊆ cell := by
  intro x hx i
  have hb := Transplant.Internal.abs_apply_le (x - Periodic.center) i
  rw [PiLp.sub_apply, Transplant.Internal.center_apply, abs_le] at hb
  have hx' : ‖x - Periodic.center‖ < (1 / 16 : ℝ) := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hx
  constructor <;> linarith [hb.1, hb.2]

/-- The physical gradient seminorm on B_(1/16) is bounded by the full periodic
H¹ norm. Smoothness supplies the integrability required for set integrals. -/
theorem localGradientNorm_le_toV {f : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hp : IsPeriodic f)
    (hd : ∀ x, divergenceAt f x = 0) :
    localGradientNorm f ≤ ‖toV f‖ := by
  have hi : ∀ i : Fin 3, IntegrableOn
      (fun x => ‖fderiv ℝ f x (unitVector i)‖ ^ 2) cell := fun i =>
    ((FreqTrSeries.Internal.contDiff_partialD i hf).continuous.norm.pow 2).continuousOn.integrableOn_compact
      FreqTrSeries.Internal.isCompact_cell
  have hlocal : (∫ x in Metric.ball Periodic.center (1 / 16 : ℝ),
      ∑ i : Fin 3, ‖fderiv ℝ f x (unitVector i)‖ ^ 2) ≤
      ∑ i : Fin 3, ∫ x in cell, ‖fderiv ℝ f x (unitVector i)‖ ^ 2 := by
    rw [integral_finsetSum _ (fun i _ => (hi i).mono_set innerBall_subset_cell)]
    exact Finset.sum_le_sum fun i _ => setIntegral_mono_set (hi i)
      (Filter.Eventually.of_forall fun x => sq_nonneg _) innerBall_subset_cell.eventuallyLE
  have hnorm := Transplant.Internal.norm_toV_sq hf hp hd
  have hmass : 0 ≤ ∫ x in cell, ‖f x‖ ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hbound : (∫ x in Metric.ball Periodic.center (1 / 16 : ℝ),
      ∑ i : Fin 3, ‖fderiv ℝ f x (unitVector i)‖ ^ 2) ≤ ‖toV f‖ ^ 2 := by
    linarith
  unfold localGradientNorm
  calc
    Real.sqrt _ ≤ Real.sqrt (‖toV f‖ ^ 2) := Real.sqrt_le_sqrt hbound
    _ = ‖toV f‖ := Real.sqrt_sq (norm_nonneg _)

/-- This is the concrete B_(1/16) error bridge once a smooth physical
representative of the constructed trajectory is available. Its hypotheses
are explicit; no regularity of the V-valued trajectory is assumed silently. -/
theorem local_profile_error_le_periodic_error
    {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C T t : ℝ}
    (hW : IsSimilarityProfile W q C) (hT : 0 < T) (ht : t < T)
    (v : Space → Space)
    (hf : ContDiff ℝ ∞ (fun y => v y - approxPeriodic W T t y))
    (hp : IsPeriodic (fun y => v y - approxPeriodic W T t y))
    (hd : ∀ x, divergenceAt (fun y => v y - approxPeriodic W T t y) x = 0) :
    localGradientNorm (fun y => v y - selfSimilar W T t y) ≤
      ‖toV (fun y => v y - approxPeriodic W T t y)‖ := by
  have he : localGradientNorm (fun y => v y - selfSimilar W T t y) =
      localGradientNorm (fun y => v y - approxPeriodic W T t y) := by
    unfold localGradientNorm
    congr 1
    refine setIntegral_congr_fun measurableSet_ball ?_
    intro x hx
    try dsimp only
    rw [fderiv_error_eq_on_innerBall hW hT ht v hx]
  rw [he]
  exact localGradientNorm_le_toV hf hp hd

/-- The full local H¹ norm, including the velocity L² term. The gradient
term is the sum of squared basis derivatives (the Frobenius norm).
Use the explicit integrability conclusions/arguments of the lemmas below
when interpreting these real-valued integrals. -/
def localH1Norm (f : Space → Space) : ℝ :=
  Real.sqrt ((∫ x in Metric.ball Periodic.center (1 / 16 : ℝ), ‖f x‖ ^ 2) +
    ∑ i : Fin 3, ∫ x in Metric.ball Periodic.center (1 / 16 : ℝ),
      ‖fderiv ℝ f x (unitVector i)‖ ^ 2)

/-- Explicit cell integrability guards for the physical full H¹ norm. -/
theorem physicalH1_integrableOn_cell {f : Space → Space}
    (hf : ContDiff ℝ ∞ f) :
    IntegrableOn (fun x => ‖f x‖ ^ 2) cell ∧
      ∀ i : Fin 3, IntegrableOn (fun x => ‖fderiv ℝ f x (unitVector i)‖ ^ 2) cell := by
  refine ⟨(hf.continuous.norm.pow 2).continuousOn.integrableOn_compact
    FreqTrSeries.Internal.isCompact_cell, ?_⟩
  intro i
  exact ((FreqTrSeries.Internal.contDiff_partialD i hf).continuous.norm.pow 2).continuousOn.integrableOn_compact
    FreqTrSeries.Internal.isCompact_cell

/-- Full local H¹ control with explicit cell integrability assumptions.
No divergent real-valued integral can be hidden behind this estimate. -/
theorem localH1Norm_le_toV {f : Space → Space}
    (hf : ContDiff ℝ ∞ f) (hp : IsPeriodic f)
    (hd : ∀ x, divergenceAt f x = 0)
    (hL2 : IntegrableOn (fun x => ‖f x‖ ^ 2) cell)
    (hD2 : ∀ i : Fin 3, IntegrableOn (fun x => ‖fderiv ℝ f x (unitVector i)‖ ^ 2) cell) :
    localH1Norm f ≤ ‖toV f‖ := by
  have hvalue : (∫ x in Metric.ball Periodic.center (1 / 16 : ℝ), ‖f x‖ ^ 2) ≤
      ∫ x in cell, ‖f x‖ ^ 2 :=
    setIntegral_mono_set hL2 (Filter.Eventually.of_forall fun x => sq_nonneg _)
      innerBall_subset_cell.eventuallyLE
  have hgradient : (∑ i : Fin 3, ∫ x in Metric.ball Periodic.center (1 / 16 : ℝ),
      ‖fderiv ℝ f x (unitVector i)‖ ^ 2) ≤
      ∑ i : Fin 3, ∫ x in cell, ‖fderiv ℝ f x (unitVector i)‖ ^ 2 :=
    Finset.sum_le_sum fun i _ => setIntegral_mono_set (hD2 i)
      (Filter.Eventually.of_forall fun x => sq_nonneg _) innerBall_subset_cell.eventuallyLE
  have htotal := add_le_add hvalue hgradient
  rw [← Transplant.Internal.norm_toV_sq hf hp hd] at htotal
  unfold localH1Norm
  calc
    Real.sqrt _ ≤ Real.sqrt (‖toV f‖ ^ 2) := Real.sqrt_le_sqrt htotal
    _ = ‖toV f‖ := Real.sqrt_sq (norm_nonneg _)

/-- Equality of the full local H¹ expressions: both velocity and spatial
basis derivatives agree on the ball. Integrability is supplied explicitly
by the guarded bound below, not asserted by this identity alone. -/
theorem localH1_profile_error_eq_periodic_error
    {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C T t : ℝ}
    (hW : IsSimilarityProfile W q C) (hT : 0 < T) (ht : t < T)
    (v : Space → Space) :
    localH1Norm (fun y => v y - selfSimilar W T t y) =
      localH1Norm (fun y => v y - approxPeriodic W T t y) := by
  unfold localH1Norm
  apply congrArg Real.sqrt
  apply congrArg₂ (fun a b : ℝ => a + b)
  · refine setIntegral_congr_fun measurableSet_ball ?_
    intro x hx
    try dsimp only
    rw [approxPeriodic_eq_selfSimilar_on_innerBall hW hT ht
      (show dist x Periodic.center ≤ (1 / 16 : ℝ) from le_of_lt hx)]
  · apply Finset.sum_congr rfl
    intro i hi
    refine setIntegral_congr_fun measurableSet_ball ?_
    intro x hx
    try dsimp only
    rw [fderiv_error_eq_on_innerBall hW hT ht v hx]

/-- The guarded FULL H¹ local error bridge. Smoothness of the periodic error
supplies cell integrability; local equality transfers it to the profile
error. The conclusion returns both explicit local integrability guards and
the full H¹ norm bound. It does not construct a smooth physical trajectory. -/
theorem local_fullH1_profile_error_le_periodic_error
    {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C T t : ℝ}
    (hW : IsSimilarityProfile W q C) (hT : 0 < T) (ht : t < T)
    (v : Space → Space)
    (hf : ContDiff ℝ ∞ (fun y => v y - approxPeriodic W T t y))
    (hp : IsPeriodic (fun y => v y - approxPeriodic W T t y))
    (hd : ∀ x, divergenceAt (fun y => v y - approxPeriodic W T t y) x = 0) :
    IntegrableOn (fun x => ‖v x - selfSimilar W T t x‖ ^ 2)
        (Metric.ball Periodic.center (1 / 16 : ℝ)) ∧
      (∀ i : Fin 3, IntegrableOn
        (fun x => ‖fderiv ℝ (fun y => v y - selfSimilar W T t y) x (unitVector i)‖ ^ 2)
        (Metric.ball Periodic.center (1 / 16 : ℝ))) ∧
      localH1Norm (fun y => v y - selfSimilar W T t y) ≤
        ‖toV (fun y => v y - approxPeriodic W T t y)‖ := by
  obtain ⟨hL2, hD2⟩ := physicalH1_integrableOn_cell hf
  have hvalue : IntegrableOn (fun x => ‖v x - selfSimilar W T t x‖ ^ 2)
      (Metric.ball Periodic.center (1 / 16 : ℝ)) := by
    refine (hL2.mono_set innerBall_subset_cell).congr_fun (fun x hx => ?_)
      measurableSet_ball
    try dsimp only
    rw [approxPeriodic_eq_selfSimilar_on_innerBall hW hT ht
      (show dist x Periodic.center ≤ (1 / 16 : ℝ) from le_of_lt hx)]
  have hgradient : ∀ i : Fin 3, IntegrableOn
      (fun x => ‖fderiv ℝ (fun y => v y - selfSimilar W T t y) x (unitVector i)‖ ^ 2)
      (Metric.ball Periodic.center (1 / 16 : ℝ)) := by
    intro i
    refine ((hD2 i).mono_set innerBall_subset_cell).congr_fun (fun x hx => ?_)
      measurableSet_ball
    try dsimp only
    rw [fderiv_error_eq_on_innerBall hW hT ht v hx]
  refine ⟨hvalue, hgradient, ?_⟩
  rw [localH1_profile_error_eq_periodic_error hW hT ht v]
  exact localH1Norm_le_toV hf hp hd hL2 hD2

/-- Undoing the quarter-power normalization on an entire glued time window.
The matching condition is precisely what SeqPerturbation returns. -/
theorem normalized_glue_window {T lam : ℝ}
    (hT : 0 < T) (hl : 0 < lam) (hl1 : lam < 1)
    (u : ℕ → Piece V (1 - lam))
    (hlink : ∀ n, extendPiece (u (n + 1)) 0 =
      lam ^ (1 / 4 : ℝ) • pieceEnd (1 - lam) (u n))
    (n : ℕ) (s : Icc (0 : ℝ) (1 - lam)) :
    (stepScale T lam n) ^ (1 / 4 : ℝ) •
      gluePieces T lam u (stepStart T lam n + stepScale T lam n * (s : ℝ)) =
        u n s := by
  rw [Glue.Internal.glue_at hT hl hl1 u hlink n s s.property,
    TransferAssemblyInternal.extendPiece_of_mem _ s.property, smul_smul,
    ← Real.rpow_add (stepScale_pos hT hl n)]
  norm_num

/-- A uniform bound on the correction sequence gives the geometric error
bound on every time window, not merely at the window endpoints. -/
theorem normalized_glue_error_le {T lam θ Z : ℝ}
    (hT : 0 < T) (hl : 0 < lam) (hl1 : lam < 1) (hθ : 0 ≤ θ)
    (ub z : ℕ → Piece V (1 - lam))
    (hz : ∀ n, ‖z n‖ ≤ Z)
    (hlink : ∀ n,
      extendPiece (ub (n + 1) + θ ^ (n + 1) • z (n + 1)) 0 =
        lam ^ (1 / 4 : ℝ) • pieceEnd (1 - lam) (ub n + θ ^ n • z n))
    (n : ℕ) (s : Icc (0 : ℝ) (1 - lam)) :
    ‖(stepScale T lam n) ^ (1 / 4 : ℝ) •
        gluePieces T lam (fun m => ub m + θ ^ m • z m)
          (stepStart T lam n + stepScale T lam n * (s : ℝ)) - ub n s‖ ≤
      θ ^ n * Z := by
  rw [normalized_glue_window hT hl hl1 _ hlink n s]
  have he : (ub n + θ ^ n • z n) s - ub n s = θ ^ n • z n s := by simp
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hθ n)]
  exact mul_le_mul_of_nonneg_left (((z n).norm_coe_le_norm s).trans (hz n))
    (pow_nonneg hθ n)

/-- Along any choice of positions inside the shrinking windows, the
normalized correction tends to zero. -/
theorem normalized_glue_error_tendsto_zero {T lam θ Z : ℝ}
    (hT : 0 < T) (hl : 0 < lam) (hl1 : lam < 1)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (ub z : ℕ → Piece V (1 - lam)) (hz : ∀ n, ‖z n‖ ≤ Z)
    (hlink : ∀ n,
      extendPiece (ub (n + 1) + θ ^ (n + 1) • z (n + 1)) 0 =
        lam ^ (1 / 4 : ℝ) • pieceEnd (1 - lam) (ub n + θ ^ n • z n))
    (s : ℕ → Icc (0 : ℝ) (1 - lam)) :
    Tendsto (fun n =>
      ‖(stepScale T lam n) ^ (1 / 4 : ℝ) •
          gluePieces T lam (fun m => ub m + θ ^ m • z m)
            (stepStart T lam n + stepScale T lam n * (s n : ℝ)) - ub n (s n)‖)
      atTop (𝓝 0) := by
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n =>
    normalized_glue_error_le hT hl hl1 hθ ub z hz hlink n (s n)) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ hθ1).mul_const Z

end Breakdown.Theorem11.Torus
