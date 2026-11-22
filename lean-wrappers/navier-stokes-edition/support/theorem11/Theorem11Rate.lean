import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-!
New wrapper lemmas for the pinned Navier--Stokes review.
Compilation: checked with Lean v4.33.1 and the pinned Mathlib.
See rate_compile_receipt.json. No authors' library theorem is assumed here.

This file isolates the elementary quantitative argument. In particular, it
does not claim that an abstract norm is already a physical gradient norm.
-/

open Set Filter Real
open scoped Topology

namespace Theorem11Rate

theorem norm_window {X : Type*} [SeminormedAddCommGroup X]
    (v w : X) (c M E : ℝ)
    (hlo : c ≤ ‖w‖) (hhi : ‖w‖ ≤ M)
    (herr : ‖v - w‖ ≤ E) (hsmall : E ≤ c / 2) :
    c / 2 ≤ ‖v‖ ∧ ‖v‖ ≤ M + c / 2 := by
  have hl : ‖w‖ ≤ ‖v - w‖ + ‖v‖ := by
    calc
      ‖w‖ = ‖(w - v) + v‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - v‖ + ‖v‖ := norm_add_le _ _
      _ = ‖v - w‖ + ‖v‖ := by rw [norm_sub_rev]
  have hu : ‖v‖ ≤ ‖v - w‖ + ‖w‖ := by
    calc
      ‖v‖ = ‖(v - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖v - w‖ + ‖w‖ := norm_add_le _ _
  constructor <;> linarith

theorem undo_quarter_scaling {μ N A B S : ℝ} (hμ : 0 < μ)
    (hscale : S = μ ^ (1 / 4 : ℝ) * N) (hlo : A ≤ S) (hhi : S ≤ B) :
    A * μ ^ (-(1 / 4 : ℝ)) ≤ N ∧ N ≤ B * μ ^ (-(1 / 4 : ℝ)) := by
  have hp : 0 < μ ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hμ _
  simp only [Real.rpow_neg hμ.le, ← div_eq_mul_inv]
  constructor
  · apply (div_le_iff₀ hp).2
    simpa [hscale, mul_comm] using hlo
  · apply (le_div_iff₀ hp).2
    simpa [hscale, mul_comm] using hhi

theorem power_error_small {C κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, |t - 1| < δ →
      C * (1 - t) ^ κ ≤ c / 2 := by
  have hb : Tendsto (fun t : ℝ => 1 - t) (𝓝 (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hh : Continuous (fun t : ℝ => 1 - t) := continuous_const.sub continuous_id
    simpa using hh.tendsto 1
  have hp := (Real.continuousAt_rpow_const 0 κ (Or.inr hκ.le)).tendsto.comp hb
  rw [Real.zero_rpow hκ.ne'] at hp
  have he : Tendsto (fun t : ℝ => C * (1 - t) ^ κ) (𝓝 (1 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using hp.const_mul C
  have hs : ∀ᶠ t : ℝ in 𝓝 (1 : ℝ), C * (1 - t) ^ κ < c / 2 :=
    he.eventually (gt_mem_nhds (half_pos hc))
  rw [Metric.eventually_nhds_iff] at hs
  obtain ⟨δ, hδ, hs⟩ := hs
  refine ⟨δ, hδ, fun t ht => ?_⟩
  exact (hs (by simpa [Real.dist_eq] using ht)).le

/-- A power error tending to zero and a nonzero bounded comparison orbit give
the two-sided quarter-power rate near the endpoint. -/
theorem late_rate {X : Type*} [SeminormedAddCommGroup X]
    (u v w : ℝ → X) (c M C κ : ℝ) (hc : 0 < c) (hκ : 0 < κ)
    (hlo : ∀ t ∈ Ico (0 : ℝ) 1, c ≤ ‖w t‖)
    (hhi : ∀ t ∈ Ico (0 : ℝ) 1, ‖w t‖ ≤ M)
    (hscale : ∀ t ∈ Ico (0 : ℝ) 1, ‖v t‖ = (1 - t) ^ (1 / 4 : ℝ) * ‖u t‖)
    (herr : ∀ t ∈ Ico (0 : ℝ) 1, ‖v t - w t‖ ≤ C * (1 - t) ^ κ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Ico (0 : ℝ) 1, 1 - δ < t →
      (c / 2) * (1 - t) ^ (-(1 / 4 : ℝ)) ≤ ‖u t‖ ∧
      ‖u t‖ ≤ (M + c / 2) * (1 - t) ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨δ, hδ, hsmall⟩ := power_error_small (C := C) hκ hc
  refine ⟨δ, hδ, fun t ht hnear => ?_⟩
  have hd : |t - 1| < δ := by
    rw [abs_of_neg (by linarith [ht.2] : t - 1 < 0)]
    linarith
  have hn := norm_window (v t) (w t) c M (C * (1 - t) ^ κ)
    (hlo t ht) (hhi t ht) (herr t ht) (hsmall t hd)
  exact undo_quarter_scaling (by linarith [ht.2] : 0 < 1 - t) (hscale t ht) hn.1 hn.2

/-- Compactness supplies the early-time constants once the trajectory is
continuous and never zero. The endpoint rate itself is unchanged. -/
theorem globalize_rate {X : Type*} [NormedAddCommGroup X]
    (u : ℝ → X) (hcont : ContinuousOn u (Ico (0 : ℝ) 1))
    (hne : ∀ t ∈ Ico (0 : ℝ) 1, u t ≠ 0)
    (c C δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (hlate : ∀ t ∈ Ico (0 : ℝ) 1, 1 - δ < t →
      c * (1 - t) ^ (-(1 / 4 : ℝ)) ≤ ‖u t‖ ∧
      ‖u t‖ ≤ C * (1 - t) ^ (-(1 / 4 : ℝ))) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ t ∈ Ico (0 : ℝ) 1,
      a * (1 - t) ^ (-(1 / 4 : ℝ)) ≤ ‖u t‖ ∧
      ‖u t‖ ≤ b * (1 - t) ^ (-(1 / 4 : ℝ)) := by
  let T : ℝ := max 0 (1 - δ / 2)
  have hT0 : 0 ≤ T := le_max_left _ _
  have hT1 : T < 1 := max_lt (by norm_num) (by linarith)
  have hTnear : 1 - δ < T := by
    have := le_max_right (0 : ℝ) (1 - δ / 2)
    dsimp [T]
    linarith
  let f : ℝ → ℝ := fun t => (1 - t) ^ (1 / 4 : ℝ) * ‖u t‖
  have hp : Continuous (fun t : ℝ => (1 - t) ^ (1 / 4 : ℝ)) :=
    (continuous_const.sub continuous_id).rpow_const (fun _ => Or.inr (by norm_num))
  have hf : ContinuousOn f (Icc (0 : ℝ) T) :=
    hp.continuousOn.mul ((hcont.mono (Icc_subset_Ico_right hT1)).norm)
  obtain ⟨s, hs, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, le_rfl, hT0⟩ hf
  obtain ⟨r, hr, hmax⟩ := isCompact_Icc.exists_isMaxOn ⟨0, le_rfl, hT0⟩ hf
  have hsI : s ∈ Ico (0 : ℝ) 1 := ⟨hs.1, hs.2.trans_lt hT1⟩
  have hrI : r ∈ Ico (0 : ℝ) 1 := ⟨hr.1, hr.2.trans_lt hT1⟩
  have hfs : 0 < f s :=
    mul_pos (Real.rpow_pos_of_pos (by linarith [hsI.2]) _) (norm_pos_iff.mpr (hne s hsI))
  have hfr : 0 ≤ f r := mul_nonneg (Real.rpow_nonneg (by linarith [hrI.2]) _) (norm_nonneg _)
  refine ⟨min c (f s), max C (f r + 1), lt_min hc hfs,
    lt_of_lt_of_le (by linarith : 0 < f r + 1) (le_max_right _ _), ?_⟩
  intro t ht
  by_cases htT : t ≤ T
  · have htI : t ∈ Icc (0 : ℝ) T := ⟨ht.1, htT⟩
    have hlow : min c (f s) ≤ f t := (min_le_right _ _).trans (hmin htI)
    have hupp : f t ≤ max C (f r + 1) :=
      (hmax htI).trans ((by linarith : f r ≤ f r + 1).trans (le_max_right _ _))
    exact undo_quarter_scaling (by linarith [ht.2] : 0 < 1 - t) rfl hlow hupp
  · have hnear : 1 - δ < t := hTnear.trans (lt_of_not_ge htT)
    have h := hlate t ht hnear
    have hpow := Real.rpow_nonneg (by linarith [ht.2] : 0 ≤ 1 - t) (-(1 / 4 : ℝ))
    exact ⟨(mul_le_mul_of_nonneg_right (min_le_left _ _) hpow).trans h.1,
      h.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)⟩

end Theorem11Rate
