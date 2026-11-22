import Theorem71Statements

/-!
Status: NOT COMPILED.
Elementary translations between the proposed statement and the paper's
printed conventions. These lemmas do not supply the analytic wrapper.
-/

open scoped ENNReal

namespace Breakdown.Theorem71

/-- The formal Sobolev product constant agrees algebraically with the paper's displayed constant. -/
theorem supBoundFactor_paper (w : ℝ) :
    supBoundFactor w = 1 / Real.sqrt (4 * Real.pi * Real.sqrt w) := by
  unfold supBoundFactor
  rw [show (2 : ℝ) * Real.pi * (2 * Real.sqrt w) =
    4 * Real.pi * Real.sqrt w by ring]

/-- `M >= 0` is supplied by the certificate. Finiteness must be retained when
converting back from a real-valued square root to an extended integral. -/
theorem squared_integral_bound_iff {A : ℝ≥0∞} (hA : A ≠ ⊤)
    {M : ℝ} (hM : 0 ≤ M) :
    A ≤ ENNReal.ofReal (M ^ 2) ↔ Real.sqrt A.toReal ≤ M := by
  rw [← ENNReal.toReal_le_toReal hA ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (sq_nonneg M)]
  constructor
  · intro h
    exact (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_sq hM)
  · intro h
    exact (Real.sqrt_le_iff.1 h).2

/-- The source uses `W(s + shift)(R y) = R(W(s,y))`; the paper writes the
equivalent inverse-coordinate form. No invariance of pressure is requested. -/
theorem prescribedSymmetries_paper {Γ : Set Symmetry} {P : ℝ}
    {W : ℝ → Space → Space} :
    PrescribedSymmetries Γ P W ↔
      ∀ γ ∈ Γ, ∀ s y, W (s + γ.2 * P) y = γ.1 (W s (γ.1.symm y)) := by
  constructor
  · intro h γ hγ s y
    simpa using h γ hγ s (γ.1.symm y)
  · intro h γ hγ s y
    simpa using h γ hγ s (γ.1 y)

end Breakdown.Theorem71
