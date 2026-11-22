import Breakdown.Transfer.Exports
import Breakdown.Spectral.RealDichotomy
import Breakdown.FreqTr.Realization
import Breakdown.Torus.Main
import Breakdown.Uniqueness.Space

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace NavierStokes

/-!
# Sections 2–6: proved statements and reductions

`lemma_3_2`, `lemma_3_3` and `lemma_3_5` retain the complete analytic conclusions
of those lemmas. Other declarations in this file are explicitly named
`..._available`: they are proved ingredients, not substitutes for the numbered
open targets in `OpenTargets.lean`.

A `HeatBilinear X` specifies a strongly continuous contraction semigroup G,
symmetric bounded bilinear operators K, continuity for positive time lag,
the heat-shift identity, and ‖K(τ)‖ ≤ CK τ^(-3/4) for 0 < τ ≤ 1.
A `MildFramework X` adds the dilations, their scaling identities and compactness
of K on a dense set of first inputs. These are the abstract hypotheses of §3.4.
-/

/-- Lemma 3.2. For every u in the solenoidal homogeneous H¹ space and every
τ > 0, the operator v ↦ K(τ)(u,v) is compact. The authors prove this first for
the dense span of compactly supported smooth solenoidal fields. Continuity in
u and closure of the compact operators extend it to every u. -/
theorem lemma_3_2 (u : Breakdown.Freq.X) (τ : ℝ) (hτ : 0 < τ) :
    IsCompactOperator (Breakdown.Freq.bilinX τ u) := by
  have hc : IsClosed {x : Breakdown.Freq.X |
      IsCompactOperator (Breakdown.Freq.bilinX τ x)} :=
    (isClosed_setOfPred_isCompactOperator (σ₁₂ := RingHom.id ℝ)
      (M₁ := Breakdown.Freq.X) (M₂ := Breakdown.Freq.X)).preimage
      (Breakdown.Freq.bilinX τ).continuous
  have hsub : (Breakdown.Freq.testSpan : Set Breakdown.Freq.X) ⊆
      {x : Breakdown.Freq.X | IsCompactOperator (Breakdown.Freq.bilinX τ x)} := by
    intro x hx
    exact Breakdown.Freq.bilinCompact_holds x hx τ hτ
  exact closure_minimal hsub hc (Breakdown.Freq.testDense_holds.2 u)

/-- Lemma 3.3. If u and v are continuous on [a,b], their Duhamel integral is
Bochner integrable at every t ∈ [a,b] and depends continuously on t. No bound
on u or v is an extra hypothesis: the proof obtains both from compactness of
[a,b] before applying the authors' quantitative integral theorem. -/
theorem lemma_3_3 {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (H : Breakdown.HeatBilinear X) (u v : ℝ → X) (a b : ℝ)
    (hab : a ≤ b) (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b)) :
    (∀ t ∈ Icc a b,
      IntervalIntegrable (fun s => H.K (t - s) (u s) (v s)) volume a t) ∧
    ContinuousOn (fun t => ∫ s in a..t, H.K (t - s) (u s) (v s)) (Icc a b) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hu
  obtain ⟨N, hN⟩ := isCompact_Icc.exists_bound_of_continuousOn hv
  have h := Breakdown.varConstIntegral X H u v a b M N hab hu hv hM hN
  exact ⟨h.1, h.2.2⟩

/-- Lemma 3.5, the change of the initial time for independent factors f and h,
together with uniqueness of the nonlinear mild solution. The restriction
identity uses the original Duhamel formula at m and t. The final conjunct
asserts uniqueness for two quadratic mild solutions on [a,b]. -/
theorem lemma_3_5 {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (H : Breakdown.HeatBilinear X) (f h u : ℝ → X)
    (a b : ℝ) (hab : a < b) (hf : ContinuousOn f (Icc a b))
    (hh : ContinuousOn h (Icc a b))
    (hu : ∀ t ∈ Icc a b,
      u t = H.G (t - a) (u a) + ∫ s in a..t, H.K (t - s) (f s) (h s)) :
    (∀ m ∈ Icc a b, ∀ t ∈ Icc m b,
      u t = H.G (t - m) (u m) + ∫ s in m..t, H.K (t - s) (f s) (h s)) ∧
    (∀ v w : ℝ → X, H.IsMildOnIcc v a b → H.IsMildOnIcc w a b →
      v a = w a → ∀ t ∈ Icc a b, v t = w t) := by
  refine ⟨?_, fun v w => (Breakdown.mildUnique X H v w a b).2⟩
  intro m hm t ht
  have hat : a ≤ t := hm.1.trans ht.1
  have htab : t ∈ Icc a b := ⟨hat, ht.2⟩
  have hi := (lemma_3_3 H f h a b hab.le hf hh).1
  have him := hi m hm
  have hit := hi t htab
  have heq : EqOn (fun s => H.G (t - m) (H.K (m - s) (f s) (h s)))
      (fun s => H.K (t - s) (f s) (h s)) (Ioo a m) := by
    intro s hs
    simp only
    rw [H.K_shift _ _ (sub_nonneg.2 ht.1) (sub_pos.2 hs.2), sub_add_sub_cancel]
  have hG : IntervalIntegrable
      (fun s => H.G (t - m) (H.K (m - s) (f s) (h s))) volume a m :=
    ⟨(H.G (t - m)).integrable_comp him.1, (H.G (t - m)).integrable_comp him.2⟩
  have hA : IntervalIntegrable (fun s => H.K (t - s) (f s) (h s)) volume a m :=
    hG.congr_uIoo (by rw [uIoo_of_le hm.1]; exact heq)
  have hB : IntervalIntegrable (fun s => H.K (t - s) (f s) (h s)) volume m t :=
    hit.mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le hat]
      exact Icc_subset_Icc_left hm.1)
  have hs : H.G (t - m) (u m) =
      H.G (t - a) (u a) + ∫ s in a..m, H.K (t - s) (f s) (h s) := by
    rw [hu m hm, map_add, ← ContinuousLinearMap.intervalIntegral_comp_comm _ him,
      intervalIntegral.integral_congr_Ioo_of_le hm.1 heq,
      ← ContinuousLinearMap.comp_apply,
      ← H.G_add _ _ (sub_nonneg.2 ht.1) (sub_nonneg.2 hm.1), sub_add_sub_cancel]
  rw [hu t htab, hs, add_assoc, intervalIntegral.integral_add_adjacent_intervals hA hB]

/-- Available for Proposition 2.1: a mild trajectory from an arbitrarily close
datum in any dense linear subspace, converging to the prescribed orbit in
self-similar variables. This does not quantify over every nearby datum or keep
one fixed finite-dimensional correction space. -/
theorem proposition_2_1_available : Breakdown.TransferHolds :=
  Breakdown.transferHolds_of_dichotomy Breakdown.dichotomyHolds

/-- Available for Lemma 2.3: on each closed finite interval, the authors'
Fourier mild solution from smooth compactly supported solenoidal data has a
jointly smooth velocity-pressure representative and finite energy. This
statement alone does not assert energy nonincrease or periodic regularity. -/
theorem lemma_2_3_available :
    Breakdown.MildRegular Breakdown.Freq.realization Breakdown.Freq.velocity :=
  Breakdown.mildRegular_realization

/-- Available for Lemma 3.1: the bilinear kernel has the τ^(-3/4) bound, the
heat-shift identity and continuity for every pair of homogeneous H¹ inputs.
The arbitrary L^(3/2) forcing assertion is a separate open target. -/
theorem lemma_3_1_available :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ τ, 0 < τ → ∀ u v : Breakdown.Freq.X,
      ‖Breakdown.Freq.bilinX τ u v‖ ≤ C * τ ^ (-(3 / 4 : ℝ)) * ‖u‖ * ‖v‖) ∧
    (∀ s τ, 0 ≤ s → 0 < τ → ∀ u v : Breakdown.Freq.X,
      Breakdown.Freq.heatX s (Breakdown.Freq.bilinX τ u v) =
        Breakdown.Freq.bilinX (s + τ) u v) ∧
    (∀ u v : Breakdown.Freq.X,
      ContinuousOn (fun τ => Breakdown.Freq.bilinX τ u v) (Ioi 0)) :=
  ⟨Breakdown.Freq.bilin_holds.2, Breakdown.Freq.bilinShift_holds,
    Breakdown.Freq.bilinCont_holds⟩

/-- Available for Lemma 3.4: bounded bilinearity of the Duhamel operator and
boundedness of the free heat operator on C([0,T];X). Arbitrary-interval
invertibility of I-2B(f,·) is not part of this conclusion. -/
theorem lemma_3_4_available : Breakdown.PieceOperatorStatement :=
  Breakdown.pieceOperator

/-- Available for Lemma 3.6: a weak solution with the authors' explicit decay
and L²-difference assumptions is mild. The open target removes those extra
assumptions and retains the paper's continuous H¹ weak-solution class. -/
theorem lemma_3_6_available (v : ℝ → Breakdown.Space → Breakdown.Space)
    (a b : ℝ) (hab : a < b) (hv : Breakdown.Freq.IsWeakSolution v a b) :
    Breakdown.Freq.IsMildX (fun t => Breakdown.Freq.embedX (v t)) a b :=
  Breakdown.Freq.mild_holds v a b hab hv

/-- Available for Lemma 3.7: the authors' bilinear estimate on the unit torus,
in its inhomogeneous H¹ Fourier space and for time lags at most one. The
period-independent homogeneous estimate for arbitrary L^(3/2) forces remains
separate. -/
theorem lemma_3_7_available : Breakdown.Periodic.KernelSharpBound :=
  Breakdown.Periodic.kernelSharpBound_holds

/-- Available for Proposition 4.1: a continuous solution of the similarity
Duhamel equation becomes a mild solution on [0,1) after the self-similar change
of variables. The full numbered target also records recurrence and nonzero
velocity. -/
theorem proposition_4_1_available : Breakdown.OrbitPhysicalStatement :=
  Breakdown.orbitPhysical

/-- Available for Lemma 4.2: every nonzero recurrent mild orbit has a positive
uniform lower norm bound and a finite uniform upper norm bound. Together with
the exact dilation law these are the ingredients for the physical blow-up
rate; the numbered target retains the iterated recurrence as well. -/
theorem lemma_4_2_available {X : Type} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] (F : Breakdown.MildFramework X)
    (ρ : X ≃ₗᵢ[ℝ] X) (hcomm : F.Commutes ρ) (w : ℝ → X) (S : ℝ)
    (hw : F.IsOrbit ρ w S) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ s, c ≤ ‖w s‖ ∧ ‖w s‖ ≤ C := by
  obtain ⟨c, hc, hlow⟩ := Breakdown.orbitNorm X F ρ hcomm w S hw
  obtain ⟨C, hupp⟩ := Breakdown.orbitBound X F ρ w S hw
  exact ⟨c, C, hc, (hlow 0).trans (hupp 0), fun s => ⟨hlow s, hupp s⟩⟩

/-- Available for Proposition 4.3: a bounded right inverse on sequences of
short-time solution pieces with finite-dimensional correction. The target in
OpenTargets keeps the paper's single weighted trajectory space. -/
theorem proposition_4_3_available : Breakdown.StepDataStatement :=
  Breakdown.stepData Breakdown.dichotomyHolds

/-- Available for Lemma 4.4: the monodromy assembled from sufficiently short
steps differs compactly from its free evolution, whose norm is at most
exp(-S/4). The exact single-period operator in the paper still needs to be
identified with this step product. -/
theorem lemma_4_4_available : Breakdown.MonodromyStatement :=
  Breakdown.monodromy

/-- Lemma 4.5 in the authors' quantitative spectral form. A compact
perturbation of an operator of norm at most b has a commuting finite-rank
unstable projection between any radii α and β with b ≤ α < β. Stable powers
and inverse unstable powers have geometric bounds with a strict gap r₁<r₂.
Choosing Θ strictly between the two radii yields the two summable series of
(4.11); this declaration records the stronger geometric estimates directly. -/
theorem lemma_4_5 {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] (T₀ C : X →L[ℝ] X) (b α β : ℝ)
    (hb : 0 ≤ b) (hba : b ≤ α) (hab : α < β) (hT : ‖T₀‖ ≤ b)
    (hC : IsCompactOperator C) :
    ∃ (r₁ r₂ K : ℝ) (Pu : X →L[ℝ] X),
      α < r₁ ∧ r₁ < r₂ ∧ r₂ < β ∧ 0 < K ∧
      Pu * Pu = Pu ∧ Pu * (T₀ + C) = (T₀ + C) * Pu ∧
      FiniteDimensional ℝ (LinearMap.range (Pu : X →ₗ[ℝ] X)) ∧
      (∀ n : ℕ, ‖(T₀ + C) ^ n * (1 - Pu)‖ ≤ K * r₁ ^ n) ∧
      (∀ n : ℕ, ∀ x, ‖Pu x‖ ≤ K * r₂⁻¹ ^ n * ‖((T₀ + C) ^ n) (Pu x)‖) ∧
      (∀ y ∈ LinearMap.range (Pu : X →ₗ[ℝ] X),
        ∃ x ∈ LinearMap.range (Pu : X →ₗ[ℝ] X), (T₀ + C) x = y) :=
  Breakdown.dichotomyHolds X T₀ C b α β hb hba hab hT hC

/-- Available for Lemma 4.6: the discrete Lyapunov–Perron estimate for a
recursion with a spectral gap. The paper also identifies its forcing sequence
from the weighted continuous-time source, which is a separate target. -/
theorem lemma_4_6_available : Breakdown.DiscreteDichotomyStatement :=
  Breakdown.discreteDichotomy

/-- Available for Lemma 4.7: the local Duhamel integral estimate, including
4 CK (t-a)^(1/4) MN when t-a≤1. It does not itself prove the global weighted
norm estimates near t=1. -/
theorem lemma_4_7_available : Breakdown.VarConstIntegralStatement :=
  Breakdown.varConstIntegral

/-- Available for Lemma 4.8: a contraction corrects a sequence of short-time
pieces when a bounded right inverse is supplied. This is a different
presentation from the paper's arbitrary weighted residual and has its own
smallness constant. -/
theorem lemma_4_8_available : Breakdown.ContractionStatement :=
  Breakdown.contraction

/-- Available for Lemma 5.1: the fixed-radius, centred solenoidal cutoff is
smooth, agrees with the similarity field on the inner ball and vanishes
outside the outer ball. The arbitrary-radius quantitative statement is kept
as an open target. -/
theorem lemma_5_1_available : Breakdown.Periodic.ApproxFieldProperties :=
  Breakdown.Periodic.approxFieldProperties_holds

/-- Available for Lemma 6.1: the localized comparison between periodic and
whole-space projected heat evolution used by the authors. Its quantifiers
and small parameter differ from the explicit large-period estimate (6.2). -/
theorem lemma_6_1_available : Breakdown.Periodic.HeatDivFreeComparison :=
  Breakdown.Periodic.heatDivFreeComparison Breakdown.Freq.fieldOpRealized_holds
    Breakdown.Freq.freqTrL1L2.1
    (Breakdown.Freq.freqTrConjSym Breakdown.Freq.fieldOpRealized_holds)
    Breakdown.Freq.velocityInverts_holds Breakdown.Freq.freqTrL1L2.2

/-- Available for Lemma 6.2: the normalized periodic approximate pieces have
uniform upper and positive lower bounds and geometrically weighted residual
bounds. These are complete proved assertions, with the profile's second
velocity derivatives and pressure-gradient decay still required. -/
theorem lemma_6_2_available :
    Breakdown.Periodic.ApproxSizes ∧ Breakdown.Periodic.ApproxResidualSmall := by
  constructor
  · exact Breakdown.Periodic.approxSizes
      (Breakdown.Periodic.transplantNorm Breakdown.Periodic.transplantSmooth)
      Breakdown.Periodic.approxFieldProperties_holds Breakdown.Periodic.approxLinks_holds
      Breakdown.Freq.embedNormLinear_holds.1 Breakdown.Freq.embedNormLinear_holds.2
  · exact Breakdown.Periodic.approxResidualSmall
      Breakdown.Periodic.approxFieldProperties_holds
      (Breakdown.Periodic.approxResidualBound Breakdown.Periodic.selfSimilarSolves
        Breakdown.Periodic.homotopyCurl Breakdown.Periodic.approxFieldProperties_holds)
      Breakdown.Periodic.approxLinks_holds Breakdown.Periodic.transplantSmooth

/-- Available for Lemma 6.3: sufficiently close localized operator data
transfer an exact bounded right inverse to the periodic problem. The paper
instead states a particular approximate inverse and an explicit L^(-1/2)
defect bound. -/
theorem lemma_6_3_available : Breakdown.Periodic.ShellInverseTransfer :=
  Breakdown.Periodic.shellInverseTransfer Breakdown.Periodic.rightInversePerturb

end NavierStokes
