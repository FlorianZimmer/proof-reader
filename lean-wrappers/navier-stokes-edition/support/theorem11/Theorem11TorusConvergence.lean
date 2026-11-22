/-
New continuous-time convergence bridge. Validation: NOT COMPILED.
The assumptions retain the specific approximation/correction pieces produced
inside Assembly.lean. This does not strengthen TorusBlowup by fiat.
-/
import Theorem11GeometricRate
import Theorem11TorusRates

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Breakdown.Theorem11.Torus

open Breakdown.Periodic

/-- The geometric contraction determines a positive exponent below 1/4.
All logarithms have strictly positive arguments; log(lam) is nonzero. -/
theorem geometric_decay_exponent {lam θ : ℝ}
    (hl : 0 < lam) (hl1 : lam < 1)
    (hθlo : lam ^ (1 / 4 : ℝ) < θ) (hθ1 : θ < 1) :
    ∃ κ : ℝ, 0 < κ ∧ κ < (1 / 4 : ℝ) ∧ θ = lam ^ κ := by
  exact _root_.Theorem11GeometricRate.geometric_decay_exponent hl hl1 hθlo hθ1

/-- Extract the error against the periodic approximate field itself. -/
theorem glued_approx_error_on_window
    {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C T lam θ Z : ℝ}
    (hW : IsSimilarityProfile W q C) (hT : 0 < T) (hT1 : T ≤ 1)
    (hl : 0 < lam) (hl1 : lam < 1) (hθ : 0 ≤ θ)
    (z : ℕ → Piece V (1 - lam)) (hz : ∀ n, ‖z n‖ ≤ Z)
    (hlink : ∀ n,
      extendPiece (approxPiece W T lam (n + 1) + θ ^ (n + 1) • z (n + 1)) 0 =
        lam ^ (1 / 4 : ℝ) • pieceEnd (1 - lam) (approxPiece W T lam n + θ ^ n • z n))
    (n : ℕ) (s : Icc (0 : ℝ) (1 - lam)) :
    let t := stepStart T lam n + stepScale T lam n * (s : ℝ)
    ‖gluePieces T lam (fun m => approxPiece W T lam m + θ ^ m • z m) t -
        toV (approxPeriodic W T t)‖ ≤
      ((stepScale T lam n) ^ (-(1 / 4 : ℝ)) * θ ^ n) * Z := by
  dsimp only
  have hμ : 0 < stepScale T lam n := stepScale_pos hT hl n
  have hgl := Glue.Internal.glue_at hT hl hl1
    (fun m => approxPiece W T lam m + θ ^ m • z m) hlink n s s.property
  rw [TransferAssemblyInternal.extendPiece_of_mem _ s.property] at hgl
  have happ := (approximation_links W q C T lam hW hT hT1 hl hl1 n).1 s
  have hcancel : (stepScale T lam n) ^ (-(1 / 4 : ℝ)) *
      (stepScale T lam n) ^ (1 / 4 : ℝ) = 1 := by
    rw [← Real.rpow_add hμ]
    norm_num
  have he : gluePieces T lam (fun m => approxPiece W T lam m + θ ^ m • z m)
      (stepStart T lam n + stepScale T lam n * (s : ℝ)) -
      toV (approxPeriodic W T (stepStart T lam n + stepScale T lam n * (s : ℝ))) =
      ((stepScale T lam n) ^ (-(1 / 4 : ℝ)) * θ ^ n) • z n s := by
    rw [hgl]
    simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, happ, smul_add, smul_smul]
    rw [hcancel, one_smul, add_sub_cancel_left]
  rw [he, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hμ.le _) (pow_nonneg hθ n))]
  exact mul_le_mul_of_nonneg_left (((z n).norm_coe_le_norm s).trans (hz n))
    (mul_nonneg (Real.rpow_nonneg hμ.le _) (pow_nonneg hθ n))

/-- The quarter-power normalization and geometric correction combine exactly.
The T^(-κ) factor is necessary on a unit torus with variable blow-up time. -/
theorem geometric_coefficient_eq {T lam θ κ : ℝ}
    (hT : 0 < T) (hl : 0 < lam) (hθ : θ = lam ^ κ) (n : ℕ) :
    (stepScale T lam n) ^ (-(1 / 4 : ℝ)) * θ ^ n =
      T ^ (-κ) * (stepScale T lam n) ^ (κ - (1 / 4 : ℝ)) := by
  simpa only [stepScale] using
    (_root_.Theorem11GeometricRate.geometric_coefficient_eq hT hl hθ n)

/-- Continuous-time error estimate with the same exponent throughout [0,T).
No asymptotic notation and no sequence-only reading is needed. -/
theorem glued_approx_error_le_power
    {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C T lam θ Z : ℝ}
    (hW : IsSimilarityProfile W q C) (hT : 0 < T) (hT1 : T ≤ 1)
    (hl : 0 < lam) (hl1 : lam < 1)
    (hθlo : lam ^ (1 / 4 : ℝ) < θ) (hθ1 : θ < 1) (hZ : 0 ≤ Z)
    (z : ℕ → Piece V (1 - lam)) (hz : ∀ n, ‖z n‖ ≤ Z)
    (hlink : ∀ n,
      extendPiece (approxPiece W T lam (n + 1) + θ ^ (n + 1) • z (n + 1)) 0 =
        lam ^ (1 / 4 : ℝ) • pieceEnd (1 - lam) (approxPiece W T lam n + θ ^ n • z n)) :
    ∃ κ : ℝ, 0 < κ ∧ κ < (1 / 4 : ℝ) ∧ ∀ t ∈ Ico (0 : ℝ) T,
      ‖gluePieces T lam (fun m => approxPiece W T lam m + θ ^ m • z m) t -
          toV (approxPeriodic W T t)‖ ≤
        (Z * T ^ (-κ)) * (T - t) ^ (κ - (1 / 4 : ℝ)) := by
  obtain ⟨κ, hκ, hκq, hθeq⟩ := geometric_decay_exponent hl hl1 hθlo hθ1
  have hθ : 0 < θ := (Real.rpow_pos_of_pos hl _).trans hθlo
  refine ⟨κ, hκ, hκq, ?_⟩
  intro t ht
  have ht0 : stepStart T lam 0 ≤ t := by
    simpa only [stepStart, stepScale, pow_zero, mul_one, sub_self] using ht.1
  obtain ⟨n, -, s, hs⟩ := window_cover_from hT hl hl1 0 ht0 ht.2
  have hμ : 0 < stepScale T lam n := stepScale_pos hT hl n
  have hgap : 0 < T - t := sub_pos.2 ht.2
  have hle : T - t ≤ stepScale T lam n := by
    rw [hs]
    dsimp only [stepStart]
    nlinarith [mul_nonneg hμ.le s.property.1]
  have hpow : (stepScale T lam n) ^ (κ - (1 / 4 : ℝ)) ≤
      (T - t) ^ (κ - (1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hgap hle (by linarith)
  have hb := glued_approx_error_on_window hW hT hT1 hl hl1 hθ.le z hz hlink n s
  dsimp only at hb
  rw [← hs] at hb
  calc
    ‖gluePieces T lam (fun m => approxPiece W T lam m + θ ^ m • z m) t -
        toV (approxPeriodic W T t)‖ ≤
        ((stepScale T lam n) ^ (-(1 / 4 : ℝ)) * θ ^ n) * Z := hb
    _ = (Z * T ^ (-κ)) * (stepScale T lam n) ^ (κ - (1 / 4 : ℝ)) := by
      rw [geometric_coefficient_eq hT hl hθeq n]
      ring
    _ ≤ (Z * T ^ (-κ)) * (T - t) ^ (κ - (1 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg hZ (Real.rpow_nonneg hT.le _))

/-- The rescaled error decays as (T-t)^κ. -/
theorem rescaled_glued_approx_error_le_power
    {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C T lam θ Z : ℝ}
    (hW : IsSimilarityProfile W q C) (hT : 0 < T) (hT1 : T ≤ 1)
    (hl : 0 < lam) (hl1 : lam < 1)
    (hθlo : lam ^ (1 / 4 : ℝ) < θ) (hθ1 : θ < 1) (hZ : 0 ≤ Z)
    (z : ℕ → Piece V (1 - lam)) (hz : ∀ n, ‖z n‖ ≤ Z)
    (hlink : ∀ n,
      extendPiece (approxPiece W T lam (n + 1) + θ ^ (n + 1) • z (n + 1)) 0 =
        lam ^ (1 / 4 : ℝ) • pieceEnd (1 - lam) (approxPiece W T lam n + θ ^ n • z n)) :
    ∃ κ : ℝ, 0 < κ ∧ κ < (1 / 4 : ℝ) ∧ ∀ t ∈ Ico (0 : ℝ) T,
      (T - t) ^ (1 / 4 : ℝ) *
        ‖gluePieces T lam (fun m => approxPiece W T lam m + θ ^ m • z m) t -
            toV (approxPeriodic W T t)‖ ≤ (Z * T ^ (-κ)) * (T - t) ^ κ := by
  obtain ⟨κ, hκ, hκq, hb⟩ :=
    glued_approx_error_le_power hW hT hT1 hl hl1 hθlo hθ1 hZ z hz hlink
  refine ⟨κ, hκ, hκq, ?_⟩
  intro t ht
  have hgap : 0 < T - t := sub_pos.2 ht.2
  have he : (T - t) ^ (1 / 4 : ℝ) * (T - t) ^ (κ - (1 / 4 : ℝ)) = (T - t) ^ κ := by
    rw [← Real.rpow_add hgap]
    congr 1
    ring
  calc
    (T - t) ^ (1 / 4 : ℝ) *
        ‖gluePieces T lam (fun m => approxPiece W T lam m + θ ^ m • z m) t -
            toV (approxPeriodic W T t)‖ ≤
        (T - t) ^ (1 / 4 : ℝ) * ((Z * T ^ (-κ)) * (T - t) ^ (κ - (1 / 4 : ℝ))) :=
      mul_le_mul_of_nonneg_left (hb t ht) (Real.rpow_nonneg hgap.le _)
    _ = (Z * T ^ (-κ)) * ((T - t) ^ (1 / 4 : ℝ) * (T - t) ^ (κ - (1 / 4 : ℝ))) := by ring
    _ = (Z * T ^ (-κ)) * (T - t) ^ κ := by rw [he]

end Breakdown.Theorem11.Torus
