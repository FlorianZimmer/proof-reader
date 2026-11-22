/-
New quantitative gluing lemmas. Validation: NOT COMPILED.
These turn the bounds retained in the torus construction into two-sided
quarter-power bounds, conditional on retaining its matching pieces.
They do not assert that the public TorusBlowup proposition retains the pieces.
-/
import Theorem11TorusHelpers

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Breakdown.Theorem11.Torus

open Breakdown.Periodic

/-- A small correction cannot destroy a positive lower norm bound. -/
theorem norm_bounds_of_small_correction {X : Type*} [NormedAddCommGroup X]
    {a b : X} {c M d : ℝ} (hc : c ≤ ‖a‖) (hM : ‖a‖ ≤ M)
    (hb : ‖b‖ ≤ d) (hd : d ≤ c / 2) :
    c / 2 ≤ ‖a + b‖ ∧ ‖a + b‖ ≤ M + d := by
  have hlo : ‖a‖ ≤ ‖a + b‖ + ‖b‖ := by
    calc
      ‖a‖ = ‖(a + b) - b‖ := by simp
      _ ≤ ‖a + b‖ + ‖b‖ := norm_sub_le _ _
  exact ⟨by linarith, (norm_add_le _ _).trans (add_le_add hM hb)⟩

/-- Compare the normalization on one geometric time window with the actual
remaining physical time μ r. -/
theorem quarter_scale_comparison {μ lam r : ℝ}
    (hμ : 0 < μ) (hl : 0 < lam) (hlr : lam ≤ r) (hr1 : r ≤ 1) :
    μ ^ (-(1 / 4 : ℝ)) ≤ (μ * r) ^ (-(1 / 4 : ℝ)) ∧
      lam ^ (1 / 4 : ℝ) * (μ * r) ^ (-(1 / 4 : ℝ)) ≤ μ ^ (-(1 / 4 : ℝ)) := by
  have hr : 0 < r := hl.trans_le hlr
  have hp : r ^ (-(1 / 4 : ℝ)) ≤ lam ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hl hlr (by norm_num)
  refine ⟨Real.rpow_le_rpow_of_nonpos (mul_pos hμ hr)
    (mul_le_of_le_one_right hμ.le hr1) (by norm_num), ?_⟩
  calc
    lam ^ (1 / 4 : ℝ) * (μ * r) ^ (-(1 / 4 : ℝ)) =
        μ ^ (-(1 / 4 : ℝ)) * (lam ^ (1 / 4 : ℝ) * r ^ (-(1 / 4 : ℝ))) := by
      rw [Real.mul_rpow hμ.le hr.le]
      ring
    _ ≤ μ ^ (-(1 / 4 : ℝ)) * (lam ^ (1 / 4 : ℝ) * lam ^ (-(1 / 4 : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hl.le _))
        (Real.rpow_nonneg hμ.le _)
    _ = μ ^ (-(1 / 4 : ℝ)) := by
      rw [← Real.rpow_add hl]
      norm_num

/-- The actual glued trajectory has the two-sided quarter-power rate on
every sufficiently late time window. The constants are explicit in the
uniform profile-piece lower/upper bounds and the correction bound. -/
theorem glued_window_two_sided_rate {T lam θ c M Z : ℝ}
    (hT : 0 < T) (hl : 0 < lam) (hl1 : lam < 1)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hc : 0 < c) (hM : 0 ≤ M) (hZ : 0 ≤ Z)
    (ub z : ℕ → Piece V (1 - lam))
    (hublo : ∀ n (s : Icc (0 : ℝ) (1 - lam)), c ≤ ‖ub n s‖)
    (hubhi : ∀ n, ‖ub n‖ ≤ M) (hz : ∀ n, ‖z n‖ ≤ Z)
    (hlink : ∀ n,
      extendPiece (ub (n + 1) + θ ^ (n + 1) • z (n + 1)) 0 =
        lam ^ (1 / 4 : ℝ) • pieceEnd (1 - lam) (ub n + θ ^ n • z n)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ s : Icc (0 : ℝ) (1 - lam),
      let t := stepStart T lam n + stepScale T lam n * (s : ℝ)
      (lam ^ (1 / 4 : ℝ) * (c / 2)) * (T - t) ^ (-(1 / 4 : ℝ)) ≤
          ‖gluePieces T lam (fun m => ub m + θ ^ m • z m) t‖ ∧
        ‖gluePieces T lam (fun m => ub m + θ ^ m • z m) t‖ ≤
          (M + Z) * (T - t) ^ (-(1 / 4 : ℝ)) := by
  have hlim : Tendsto (fun n : ℕ => θ ^ n * Z) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ hθ1).mul_const Z
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (hlim.eventually (Iio_mem_nhds (half_pos hc)))
  refine ⟨N, ?_⟩
  intro n hn s
  dsimp only
  have hb : ‖θ ^ n • z n s‖ ≤ θ ^ n * Z := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hθ n)]
    exact mul_le_mul_of_nonneg_left (((z n).norm_coe_le_norm s).trans (hz n))
      (pow_nonneg hθ n)
  have hd : θ ^ n * Z ≤ c / 2 := le_of_lt (hN n hn)
  have hnorm := norm_bounds_of_small_correction (hublo n s)
    (((ub n).norm_coe_le_norm s).trans (hubhi n)) hb hd
  have hnormhi : ‖ub n s + θ ^ n • z n s‖ ≤ M + Z :=
    hnorm.2.trans (add_le_add le_rfl
      (mul_le_of_le_one_left hZ (pow_le_one₀ hθ hθ1.le)))
  have hμ : 0 < stepScale T lam n := stepScale_pos hT hl n
  have htime : T - (stepStart T lam n + stepScale T lam n * (s : ℝ)) =
      stepScale T lam n * (1 - (s : ℝ)) := by
    simp only [stepStart]
    ring
  have hrlo : lam ≤ 1 - (s : ℝ) := by linarith [s.property.2]
  have hrhi : 1 - (s : ℝ) ≤ 1 := by linarith [s.property.1]
  have hcmp := quarter_scale_comparison hμ hl hrlo hrhi
  rw [← htime] at hcmp
  have hu : ‖gluePieces T lam (fun m => ub m + θ ^ m • z m)
      (stepStart T lam n + stepScale T lam n * (s : ℝ))‖ =
      (stepScale T lam n) ^ (-(1 / 4 : ℝ)) * ‖ub n s + θ ^ n • z n s‖ := by
    rw [Glue.Internal.glue_at hT hl hl1 _ hlink n s s.property,
      TransferAssemblyInternal.extendPiece_of_mem _ s.property,
      norm_smul, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hμ _)] <;> rfl
  rw [hu]
  constructor
  · calc
      (lam ^ (1 / 4 : ℝ) * (c / 2)) *
          (T - (stepStart T lam n + stepScale T lam n * (s : ℝ))) ^ (-(1 / 4 : ℝ)) =
          (c / 2) * (lam ^ (1 / 4 : ℝ) *
            (T - (stepStart T lam n + stepScale T lam n * (s : ℝ))) ^ (-(1 / 4 : ℝ))) := by ring
      _ ≤ (c / 2) * (stepScale T lam n) ^ (-(1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hcmp.2 (half_pos hc).le
      _ ≤ (stepScale T lam n) ^ (-(1 / 4 : ℝ)) * ‖ub n s + θ ^ n • z n s‖ := by
        rw [mul_comm (c / 2)]
        exact mul_le_mul_of_nonneg_left hnorm.1 (Real.rpow_nonneg hμ.le _)
  · calc
      (stepScale T lam n) ^ (-(1 / 4 : ℝ)) * ‖ub n s + θ ^ n • z n s‖ ≤
          (stepScale T lam n) ^ (-(1 / 4 : ℝ)) * (M + Z) :=
        mul_le_mul_of_nonneg_left hnormhi (Real.rpow_nonneg hμ.le _)
      _ ≤ (M + Z) *
          (T - (stepStart T lam n + stepScale T lam n * (s : ℝ))) ^ (-(1 / 4 : ℝ)) := by
        rw [mul_comm _ (M + Z)]
        exact mul_le_mul_of_nonneg_left hcmp.1 (add_nonneg hM hZ)

/-- Later geometric windows start later. -/
theorem stepStart_mono {T lam : ℝ} (hT : 0 < T) (hl : 0 < lam) (hl1 : lam < 1) :
    Monotone (stepStart T lam) := by
  intro m n hmn
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hl.le hl1.le hmn) hT.le
  dsimp only [stepStart, stepScale]
  linarith

/-- Every time from the Nth window to T lies in one of the later windows.
This explicitly closes the discrete-window/continuous-time coverage step. -/
theorem window_cover_from {T lam t : ℝ}
    (hT : 0 < T) (hl : 0 < lam) (hl1 : lam < 1) (N : ℕ)
    (htN : stepStart T lam N ≤ t) (htT : t < T) :
    ∃ n ≥ N, ∃ s : Icc (0 : ℝ) (1 - lam),
      t = stepStart T lam n + stepScale T lam n * (s : ℝ) := by
  classical
  have hex : ∃ n : ℕ, t < stepStart T lam n := by
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos (sub_pos.2 htT) hT) hl1
    refine ⟨n, ?_⟩
    rw [lt_div_iff₀ hT, mul_comm] at hn
    dsimp only [stepStart, stepScale]
    linarith
  cases hfind : Nat.find hex with
  | zero =>
      have hfound : t < stepStart T lam 0 := by
        simpa only [hfind] using Nat.find_spec hex
      have hle := (stepStart_mono hT hl hl1 (Nat.zero_le N)).trans htN
      exact False.elim ((not_lt_of_ge hle) hfound)
  | succ n =>
      have hthi : t < stepStart T lam (n + 1) := by
        simpa only [hfind, Nat.succ_eq_add_one] using Nat.find_spec hex
      have htlo : stepStart T lam n ≤ t := by
        apply le_of_not_gt
        apply Nat.find_min hex
        omega
      have hnN : N ≤ n := by
        by_contra h
        have hle : n + 1 ≤ N := by omega
        have hle' := (stepStart_mono hT hl hl1 hle).trans htN
        exact (not_lt_of_ge hle') hthi
      have hμ : 0 < stepScale T lam n := stepScale_pos hT hl n
      have hs : (t - stepStart T lam n) / stepScale T lam n ∈ Icc (0 : ℝ) (1 - lam) := by
        constructor
        · exact div_nonneg (sub_nonneg.2 htlo) hμ.le
        · apply (div_le_iff₀ hμ).2
          rw [Glue.Internal.start_succ] at hthi
          nlinarith
      refine ⟨n, hnN, ⟨_, hs⟩, ?_⟩
      exact (Glue.Internal.affine_cancel hμ.ne' (stepStart T lam n) t).symm

/-- Continuous-time version: the V-valued glued trajectory has the rate
on a whole final interval, not just a sequence of times. This is still a
conditional bridge from retained construction data, not a new existence proof. -/
theorem glued_eventual_two_sided_rate {T lam θ c M Z : ℝ}
    (hT : 0 < T) (hl : 0 < lam) (hl1 : lam < 1)
    (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hc : 0 < c) (hM : 0 ≤ M) (hZ : 0 ≤ Z)
    (ub z : ℕ → Piece V (1 - lam))
    (hublo : ∀ n (s : Icc (0 : ℝ) (1 - lam)), c ≤ ‖ub n s‖)
    (hubhi : ∀ n, ‖ub n‖ ≤ M) (hz : ∀ n, ‖z n‖ ≤ Z)
    (hlink : ∀ n,
      extendPiece (ub (n + 1) + θ ^ (n + 1) • z (n + 1)) 0 =
        lam ^ (1 / 4 : ℝ) • pieceEnd (1 - lam) (ub n + θ ^ n • z n)) :
    ∃ t₀ ∈ Ico (0 : ℝ) T, ∀ t ∈ Ico t₀ T,
      (lam ^ (1 / 4 : ℝ) * (c / 2)) * (T - t) ^ (-(1 / 4 : ℝ)) ≤
          ‖gluePieces T lam (fun m => ub m + θ ^ m • z m) t‖ ∧
        ‖gluePieces T lam (fun m => ub m + θ ^ m • z m) t‖ ≤
          (M + Z) * (T - t) ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨N, hN⟩ := glued_window_two_sided_rate hT hl hl1 hθ hθ1 hc hM hZ
    ub z hublo hubhi hz hlink
  refine ⟨stepStart T lam N, Internal.Unbounded.stepStart_mem hT hl hl1 N, ?_⟩
  intro t ht
  obtain ⟨n, hn, s, hs⟩ := window_cover_from hT hl hl1 N ht.1 ht.2
  rw [hs]
  exact hN n hn s

end Breakdown.Theorem11.Torus
