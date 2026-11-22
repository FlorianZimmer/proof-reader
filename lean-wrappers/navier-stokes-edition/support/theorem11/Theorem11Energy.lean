import Breakdown.Uniqueness.SmoothUniqueness

/-!
# The energy inequality for the library's smooth solutions

For a smooth solution on [0,T] in the authors' class `IsSolutionOn` with finite
energy at every time, the energy at every time is at most the energy of the
datum. The proof is the authors' localized energy argument from
`Breakdown.Uniqueness.SmoothUniqueness.eq_of_isSolutionOn`, run with the zero
solution as the second solution: the cutoff energy grows at most by a term of
order 1/r, and r goes to infinity. The bound does not depend on T, which is
what a single finite-energy solution on [0,1) needs.
-/

open scoped ContDiff ENNReal Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Theorem11Energy

open Breakdown

/-- The zero velocity field. -/
def zeroVel : ℝ → Space → Space := fun _ _ => 0

/-- The zero pressure. -/
def zeroPres : ℝ → Space → ℝ := fun _ _ => 0

theorem zeroVel_t (t : ℝ) : zeroVel t = fun _ => (0 : Space) := rfl

theorem zeroPres_t (t : ℝ) : zeroPres t = fun _ => (0 : ℝ) := rfl

theorem zero_isSolutionOn (T : ℝ) : IsSolutionOn T zeroVel zeroPres := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show ContDiffOn ℝ ∞ (fun _ : ℝ × Space => (0 : Space)) _
    exact contDiffOn_const
  · show ContDiffOn ℝ ∞ (fun _ : ℝ × Space => (0 : ℝ)) _
    exact contDiffOn_const
  · intro t _ x
    simp [zeroVel_t, zeroPres_t, advectionAt, sumSecondPartialsAt, gradientAt]
  · intro t _ x
    simp [zeroVel_t, divergenceAt]

/-- Monotonicity of the authors' cutoff in its radius (their proof, which is
private in `SmoothUniqueness`). -/
theorem cutoffPow_mono' {R r : ℝ} (hR : 0 < R) (hRr : R ≤ r) (x : Space) :
    cutoffPow R x ≤ cutoffPow r x := by
  have h1 : ‖x‖ / r ≤ ‖x‖ / R := div_le_div_of_nonneg_left (norm_nonneg x) hR hRr
  have h2 : radialCutoff R x ≤ radialCutoff r x :=
    Real.smoothTransition.monotone (by linarith)
  exact pow_le_pow_left₀ (radialCutoff_nonneg R x) h2 4

theorem cutoffPow_nonneg' (r : ℝ) (x : Space) : 0 ≤ cutoffPow r x :=
  pow_nonneg (radialCutoff_nonneg r x) 4

theorem cutoffPow_le_one' (r : ℝ) (x : Space) : cutoffPow r x ≤ 1 :=
  pow_le_one₀ (radialCutoff_nonneg r x) (radialCutoff_le_one r x)

/-- The n-th localized density, with cutoff radius n + 1. -/
def cutoffSeq (g : Space → ℝ) (n : ℕ) (x : Space) : ℝ≥0∞ :=
  ENNReal.ofReal (cutoffPow ((n : ℝ) + 1) x * g x)

/-- Monotone convergence in the cutoff radius: if every localized integral of a
continuous nonnegative density is at most the real part of a finite M, then so
is the full integral. -/
theorem lintegral_ofReal_le_of_cutoff {g : Space → ℝ} (hg : Continuous g)
    (hg0 : ∀ x, 0 ≤ g x) {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (h : ∀ R : ℝ, 1 ≤ R → ∫ x, cutoffPow R x * g x ≤ M.toReal) :
    ∫⁻ x, ENNReal.ofReal (g x) ≤ M := by
  have hmeas : ∀ n : ℕ, Measurable (cutoffSeq g n) := fun n =>
    (((Internal.CutoffEnergy.contDiff_cutoffPow
      (by positivity : (0 : ℝ) < (n : ℝ) + 1)).continuous.mul hg).measurable).ennreal_ofReal
  have hmono : Monotone (cutoffSeq g) := by
    intro m n hmn x
    have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by
      have := (Nat.cast_le (α := ℝ)).2 hmn
      linarith
    have hm0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    show ENNReal.ofReal (cutoffPow ((m : ℝ) + 1) x * g x) ≤
      ENNReal.ofReal (cutoffPow ((n : ℝ) + 1) x * g x)
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (cutoffPow_mono' hm0 hmn' x) (hg0 x))
  have hpt : ∀ x, ENNReal.ofReal (g x) = ⨆ n : ℕ, cutoffSeq g n x := by
    intro x
    apply le_antisymm
    · obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
      refine le_iSup_of_le N (le_of_eq ?_)
      have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have hle : ‖x‖ ≤ (N : ℝ) + 1 := by linarith
      have h1 : cutoffPow ((N : ℝ) + 1) x = 1 := by
        simp [cutoffPow, radialCutoff_eq_one hpos hle]
      show ENNReal.ofReal (g x) = ENNReal.ofReal (cutoffPow ((N : ℝ) + 1) x * g x)
      rw [h1, one_mul]
    · refine iSup_le fun n => ?_
      show ENNReal.ofReal (cutoffPow ((n : ℝ) + 1) x * g x) ≤ ENNReal.ofReal (g x)
      exact ENNReal.ofReal_le_ofReal
        (mul_le_of_le_one_left (hg0 x) (cutoffPow_le_one' _ x))
  have hfin : ∀ n : ℕ, ∫⁻ x, cutoffSeq g n x ≤ M := by
    intro n
    have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    have hint := Internal.CutoffEnergy.integrable_cutoffPow_mul hn0 hg
    have hrw := ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun x => mul_nonneg (cutoffPow_nonneg' _ x) (hg0 x))
    calc ∫⁻ x, cutoffSeq g n x
        = ENNReal.ofReal (∫ x, cutoffPow ((n : ℝ) + 1) x * g x) := hrw.symm
      _ ≤ ENNReal.ofReal M.toReal := ENNReal.ofReal_le_ofReal (h _ hn1)
      _ = M := ENNReal.ofReal_toReal hM
  calc ∫⁻ x, ENNReal.ofReal (g x)
      = ∫⁻ x, ⨆ n : ℕ, cutoffSeq g n x := lintegral_congr hpt
    _ = ⨆ n : ℕ, ∫⁻ x, cutoffSeq g n x := lintegral_iSup hmeas hmono
    _ ≤ M := iSup_le hfin

set_option maxHeartbeats 400000 in
/-- The energy inequality: a smooth solution on [0,T] with finite energy at
every time has, at every time, energy at most that of its datum. -/
theorem energy_le_initial {T : ℝ} {v : ℝ → Space → Space} {q : ℝ → Space → ℝ}
    (hv : IsSolutionOn T v q) (hEv : EnergyBoundedOn T v) {t : ℝ} (ht : t ∈ Icc 0 T) :
    ∫⁻ x, ENNReal.ofReal (‖v t x‖ ^ 2) ≤ ∫⁻ x, ENNReal.ofReal (‖v 0 x‖ ^ 2) := by
  have hu := zero_isSolutionOn T
  have hEu : EnergyBoundedOn T zeroVel := ⟨0, fun _ _ => by simp [zeroVel]⟩
  obtain ⟨Av, hAv⟩ := id hEv
  obtain ⟨K, hK⟩ := differenceRHS_le
  have hT : 0 ≤ T := ht.1.trans ht.2
  have h0T : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hsub : ∀ τ, v τ - zeroVel τ = v τ := fun τ => by
    funext x
    simp [zeroVel]
  have hM0top : (∫⁻ x, ENNReal.ofReal (‖v 0 x‖ ^ 2)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hAv 0 h0T)
  obtain ⟨A, hA0, hA2⟩ : ∃ A : ℝ, 0 ≤ A ∧ A ^ 2 = max Av 0 :=
    ⟨_, Real.sqrt_nonneg _, Real.sq_sqrt (le_max_right _ _)⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = |K * (1 + 0) * (A ^ 2 + A ^ 6)| := ⟨_, rfl⟩
  have hdata : ∀ τ ∈ Ioo 0 T, IsDifferenceData A 0 0 (zeroVel τ) (v τ - zeroVel τ) := by
    intro τ hτ
    have hτ' := Ioo_subset_Icc_self hτ
    rw [hsub τ]
    refine ⟨⟨hv.contDiff_velocity hτ', hv.incompressible τ hτ', hA0, ?_⟩, ?_,
      hu.incompressible τ hτ', fun x => by simp [zeroVel], fun x => by simp [zeroVel_t]⟩
    · rw [hA2]
      exact (hAv τ hτ').trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
    · show ContDiff ℝ ∞ (fun _ : Space => (0 : Space))
      exact contDiff_const
  have hderiv : ∀ r : ℝ, 0 < r → ∀ τ ∈ Ioo 0 T,
      HasDerivAt (fun τ => cutoffEnergy r (v τ - zeroVel τ))
        (differenceRHS r (zeroVel τ) (v τ - zeroVel τ)) τ := by
    intro r hr0 τ hτ
    convert hasDerivAt_cutoffEnergy hu hv hr0 hτ using 1
    rw [integral_pressure_difference hu hv hEu hEv hr0 hτ]
    simp only [differenceRHS, Pi.sub_apply, add_sub_cancel]
  -- The localized energy at time t exceeds that of the datum by at most O(1/r).
  have hbound : ∀ r : ℝ, 1 ≤ r → ∫ x, cutoffPow r x * ‖v t x‖ ^ 2 ≤
      (∫⁻ x, ENNReal.ofReal (‖v 0 x‖ ^ 2)).toReal + 2 * (B * T) / r := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le one_pos hr
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = K * (1 + 0) * (A ^ 2 + A ^ 6) / r := ⟨_, rfl⟩
    have hanti : AntitoneOn (fun τ => cutoffEnergy r (v τ - zeroVel τ) - c * τ) (Icc 0 T) := by
      refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
        (f' := fun τ => differenceRHS r (zeroVel τ) (v τ - zeroVel τ) - c) ?_ ?_ ?_
      · exact (continuousOn_cutoffEnergy hu hv hr0).sub
          (continuous_const.mul continuous_id).continuousOn
      · intro τ hτ
        rw [interior_Icc] at hτ
        have h2 := (hderiv r hr0 τ hτ).sub ((hasDerivAt_id τ).const_mul c)
        exact (h2.congr_deriv (by ring)).hasDerivWithinAt
      · intro τ hτ
        rw [interior_Icc] at hτ
        have hk := hK A 0 0 (zeroVel τ) (v τ - zeroVel τ) (hdata τ hτ) r hr
        show differenceRHS r (zeroVel τ) (v τ - zeroVel τ) - c ≤ 0
        rw [hc]
        linarith
    have hg := hanti h0T ht ht.1
    simp only [mul_zero, sub_zero] at hg
    rw [hsub t, hsub 0] at hg
    have hc0 : Continuous fun x => ‖v 0 x‖ ^ 2 :=
      (hv.contDiff_velocity h0T).continuous.norm.pow 2
    have hint0 := Internal.CutoffEnergy.integrable_cutoffPow_mul hr0 hc0
    have hE0 : ∫ x, cutoffPow r x * ‖v 0 x‖ ^ 2 ≤
        (∫⁻ x, ENNReal.ofReal (‖v 0 x‖ ^ 2)).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x =>
        mul_nonneg (cutoffPow_nonneg' r x) (by positivity)) hint0.aestronglyMeasurable]
      exact ENNReal.toReal_mono hM0top (lintegral_mono fun x => ENNReal.ofReal_le_ofReal
        (mul_le_of_le_one_left (by positivity) (cutoffPow_le_one' r x)))
    have hct : c * t ≤ B * T / r := by
      rw [hc, hB]
      calc K * (1 + 0) * (A ^ 2 + A ^ 6) / r * t
          = (K * (1 + 0) * (A ^ 2 + A ^ 6) * t) * r⁻¹ := by ring
        _ ≤ (|K * (1 + 0) * (A ^ 2 + A ^ 6)| * T) * r⁻¹ :=
          mul_le_mul_of_nonneg_right (mul_le_mul (le_abs_self _) ht.2 ht.1 (abs_nonneg _))
            (inv_nonneg.2 hr0.le)
        _ = |K * (1 + 0) * (A ^ 2 + A ^ 6)| * T / r := by ring
    unfold cutoffEnergy at hg
    have h2 : B * T / r * 2 = 2 * (B * T) / r := by ring
    linarith
  have hwc : Continuous fun x => ‖v t x‖ ^ 2 := (hv.contDiff_velocity ht).continuous.norm.pow 2
  -- Every fixed localization is bounded by the datum's energy.
  have hJ : ∀ R : ℝ, 1 ≤ R → ∫ x, cutoffPow R x * ‖v t x‖ ^ 2 ≤
      (∫⁻ x, ENNReal.ofReal (‖v 0 x‖ ^ 2)).toReal := by
    intro R hR1
    have hR0 : 0 < R := lt_of_lt_of_le one_pos hR1
    have hmono : ∀ r : ℝ, R ≤ r →
        ∫ x, cutoffPow R x * ‖v t x‖ ^ 2 ≤ ∫ x, cutoffPow r x * ‖v t x‖ ^ 2 :=
      fun r hr => integral_mono (Internal.CutoffEnergy.integrable_cutoffPow_mul hR0 hwc)
        (Internal.CutoffEnergy.integrable_cutoffPow_mul (lt_of_lt_of_le hR0 hr) hwc)
        (fun x => mul_le_mul_of_nonneg_right (cutoffPow_mono' hR0 hr x) (by positivity))
    have htend : Tendsto (fun r : ℝ => (∫⁻ x, ENNReal.ofReal (‖v 0 x‖ ^ 2)).toReal +
        2 * (B * T) / r) atTop
        (𝓝 ((∫⁻ x, ENNReal.ofReal (‖v 0 x‖ ^ 2)).toReal + 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.div_atTop tendsto_id)
    rw [add_zero] at htend
    exact ge_of_tendsto htend ((eventually_ge_atTop R).mono fun r hr =>
      (hmono r hr).trans (hbound r (hR1.trans hr)))
  exact lintegral_ofReal_le_of_cutoff (g := fun x => ‖v t x‖ ^ 2) hwc
    (fun x => sq_nonneg _) hM0top hJ

end Theorem11Energy
