/-
Geometric correction rates: independent Mathlib-only lemmas.
Status: COMPILED with Lean v4.33.1; see the exact-byte validation receipt.

These lemmas prove a logarithmic exponent choice and its exact scaling
identity. They assume no Navier--Stokes library, orbit, or physical solution.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Theorem11GeometricRate

/-- For λ^(1/4) < θ < 1 and 0 < λ < 1, geometric decay θ^n is
λ^(κ n) for the positive exponent κ = log θ / log λ, with κ < 1/4. -/
theorem geometric_decay_exponent {lam θ : ℝ}
    (hl : 0 < lam) (hl1 : lam < 1)
    (hθlo : lam ^ (1 / 4 : ℝ) < θ) (hθ1 : θ < 1) :
    ∃ κ : ℝ, 0 < κ ∧ κ < (1 / 4 : ℝ) ∧ θ = lam ^ κ := by
  have hθ : 0 < θ := (Real.rpow_pos_of_pos hl _).trans hθlo
  have hlog : Real.log lam < 0 := Real.log_neg hl hl1
  have hlogθ : Real.log θ < 0 := Real.log_neg hθ hθ1
  have hpowlog : Real.log (lam ^ (1 / 4 : ℝ)) = Real.log lam * (1 / 4 : ℝ) := by
    rw [Real.rpow_def_of_pos hl, Real.log_exp]
  have hloglt := Real.log_lt_log (Real.rpow_pos_of_pos hl (1 / 4 : ℝ)) hθlo
  rw [hpowlog] at hloglt
  refine ⟨Real.log θ / Real.log lam, div_pos_of_neg_of_neg hlogθ hlog, ?_, ?_⟩
  · apply (div_lt_iff_of_neg hlog).2
    linarith
  · rw [Real.rpow_def_of_pos hl]
    have he : Real.log lam * (Real.log θ / Real.log lam) = Real.log θ := by
      field_simp [ne_of_lt hlog]
    rw [he, Real.exp_log hθ]

/-- At the physical window scale T λ^n, the quarter-power normalization
and geometric correction combine exactly. The factor T^(-κ) is retained.
No assumption λ<1 or κ>0 is needed for this algebraic identity. -/
theorem geometric_coefficient_eq {T lam θ κ : ℝ}
    (hT : 0 < T) (hl : 0 < lam) (hθ : θ = lam ^ κ) (n : ℕ) :
    (T * lam ^ n) ^ (-(1 / 4 : ℝ)) * θ ^ n =
      T ^ (-κ) * (T * lam ^ n) ^ (κ - (1 / 4 : ℝ)) := by
  have hμ : 0 < T * lam ^ n := mul_pos hT (pow_pos hl n)
  have hcancel : T ^ (-κ) * T ^ κ = 1 := by
    rw [← Real.rpow_add hT, neg_add_cancel, Real.rpow_zero]
  have he : T ^ (-κ) * (T * lam ^ n) ^ κ = (lam ^ n) ^ κ := by
    rw [Real.mul_rpow hT.le (pow_nonneg hl.le n), ← mul_assoc, hcancel, one_mul]
  calc
    (T * lam ^ n) ^ (-(1 / 4 : ℝ)) * θ ^ n =
        (T * lam ^ n) ^ (-(1 / 4 : ℝ)) * (lam ^ n) ^ κ := by
      rw [hθ, Real.rpow_pow_comm hl.le]
    _ = (T * lam ^ n) ^ (-(1 / 4 : ℝ)) *
        (T ^ (-κ) * (T * lam ^ n) ^ κ) := by rw [he]
    _ = T ^ (-κ) * ((T * lam ^ n) ^ κ *
        (T * lam ^ n) ^ (-(1 / 4 : ℝ))) := by ring
    _ = T ^ (-κ) * (T * lam ^ n) ^ (κ - (1 / 4 : ℝ)) := by
      rw [← Real.rpow_add hμ, sub_eq_add_neg]

end Theorem11GeometricRate
