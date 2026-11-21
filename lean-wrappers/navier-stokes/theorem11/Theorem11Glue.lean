import Theorem11Challenge
import Theorem11PhysicalBridges
import Breakdown.Uniqueness.Restrict

/-!
# Gluing the slab solutions into one solution on [0,1)

The library gives, for every T in (0,1), a smooth solution on [0,T]. Their
velocities agree on overlaps. Their pressures are fixed by the velocity only
up to a function of time, because the momentum equation sees only the pressure
gradient; we normalize each pressure to vanish at the origin, which makes the
pressures agree on overlaps too. The glued velocity and pressure take, at time
t, the values of the slab ending at `slabEnd t`, a time strictly after t.
-/

open MeasureTheory Set Filter
open scoped ContDiff Topology

noncomputable section

namespace Theorem11Glue

open Breakdown

/-- From the authors' `Breakdown.Periodic.MovingFrame.Internal`. -/
theorem eq_of_apply_unitVector {A B : Space →L[ℝ] ℝ}
    (h : ∀ i, A (unitVector i) = B (unitVector i)) : A = B := by
  have : (A : Space →ₗ[ℝ] ℝ) = (B : Space →ₗ[ℝ] ℝ) :=
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext fun i => by simpa [unitVector] using h i
  exact ContinuousLinearMap.coe_injective this

/-- From the authors' `Breakdown.Periodic.MovingFrame.Internal`. -/
theorem gradientAt_apply (q : Space → ℝ) (x : Space) (j : Fin 3) :
    gradientAt q x j = fderiv ℝ q x (unitVector j) := by
  simp [gradientAt, unitVector, Pi.single_apply]

/-- Two smooth solutions whose velocities agree on [0,m] have pressures that
differ, at each time of [0,m], by a constant in space. -/
theorem pressure_agree {S T : ℝ} {U V : ℝ → Space → Space} {p q : ℝ → Space → ℝ}
    (hU : IsSolutionOn S U p) (hV : IsSolutionOn T V q)
    (hUV : ∀ t ∈ Icc (0 : ℝ) (min S T), U t = V t) (hm : 0 < min S T) :
    ∀ t ∈ Icc (0 : ℝ) (min S T), ∀ x, p t x - p t 0 = q t x - q t 0 := by
  have hint : ∀ t ∈ Ioo (0 : ℝ) (min S T), ∀ x, p t x - p t 0 = q t x - q t 0 := by
    intro t ht x
    have htS : t ∈ Ioo 0 S := ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩
    have htT : t ∈ Ioo 0 T := ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩
    have hpd : Differentiable ℝ (p t) :=
      (hU.contDiff_pressure (Ioo_subset_Icc_self htS)).differentiable (by simp)
    have hqd : Differentiable ℝ (q t) :=
      (hV.contDiff_pressure (Ioo_subset_Icc_self htT)).differentiable (by simp)
    have hgrad : ∀ y, gradientAt (p t) y = gradientAt (q t) y := by
      intro y
      have hd : deriv (fun τ => U τ y) t = deriv (fun τ => V τ y) t :=
        Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (Icc_mem_nhds ht.1 ht.2)
          fun τ hτ => congrFun (hUV τ hτ) y)
      have e1 := hU.momentum t htS y
      have e2 := hV.momentum t htT y
      rw [hd, hUV t (Ioo_subset_Icc_self ht)] at e1
      exact sub_right_inj.1 (e1.symm.trans e2)
    have hzero : ∀ y, fderiv ℝ (fun z => p t z - q t z) y = 0 := by
      intro y
      rw [fderiv_fun_sub (hpd y) (hqd y), sub_eq_zero]
      apply eq_of_apply_unitVector
      intro i
      rw [← gradientAt_apply, ← gradientAt_apply, hgrad y]
    have hc : p t x - q t x = p t 0 - q t 0 :=
      is_const_of_fderiv_eq_zero (hpd.sub hqd) hzero x 0
    linarith
  have hcont : ∀ (r : ℝ → Space → ℝ) (R : ℝ), IsSolutionOn R V r → min S T ≤ R →
      ∀ y, ContinuousOn (fun τ => r τ y) (Icc 0 (min S T)) := by
    intro r R hr hR y
    have hpair : Continuous (fun τ : ℝ => (τ, y)) := by fun_prop
    exact hr.smooth_pressure.continuousOn.comp hpair.continuousOn
      (fun τ hτ => ⟨⟨hτ.1, hτ.2.trans hR⟩, mem_univ _⟩)
  have hcontU : ∀ y, ContinuousOn (fun τ => p τ y) (Icc 0 (min S T)) := by
    intro y
    have hpair : Continuous (fun τ : ℝ => (τ, y)) := by fun_prop
    exact hU.smooth_pressure.continuousOn.comp hpair.continuousOn
      (fun τ hτ => ⟨⟨hτ.1, hτ.2.trans (min_le_left _ _)⟩, mem_univ _⟩)
  intro t ht x
  have heq : EqOn (fun τ => p τ x - p τ 0) (fun τ => q τ x - q τ 0) (Icc 0 (min S T)) :=
    Set.EqOn.of_subset_closure (fun τ hτ => hint τ hτ x) ((hcontU x).sub (hcontU 0))
      ((hcont q T hV (min_le_right _ _) x).sub (hcont q T hV (min_le_right _ _) 0))
      Ioo_subset_Icc_self (closure_Ioo hm.ne).ge
  exact heq ht

end Theorem11Glue

namespace Theorem11

/-- The end time, in (0,1), of the slab used at time t. -/
def slabEndVal (t : ℝ) : ℝ := if t < 1 then (max t 0 + 1) / 2 else 1 / 2

theorem slabEndVal_mem (t : ℝ) : slabEndVal t ∈ Ioo (0 : ℝ) 1 := by
  unfold slabEndVal
  split_ifs with h
  · have h0 := le_max_right t 0
    have h1 : max t 0 < 1 := max_lt h one_pos
    exact ⟨by linarith, by linarith⟩
  · exact ⟨by norm_num, by norm_num⟩

def slabEnd (t : ℝ) : Ioo (0 : ℝ) 1 := ⟨slabEndVal t, slabEndVal_mem t⟩

theorem lt_slabEnd {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1) : t < (slabEnd t : ℝ) := by
  show t < slabEndVal t
  rw [slabEndVal, if_pos ht.2, max_eq_left ht.1]
  linarith [ht.2]

/-- A pressure normalized to vanish at the origin at every time. -/
def normalizedPressure (p : Pressure) : Pressure := fun t y => p t y - p t 0

/-- The velocity glued from a family of slab velocities. -/
def gluedVelocity (U : Ioo (0 : ℝ) 1 → Velocity) : Velocity := fun t => U (slabEnd t) t

/-- The pressure glued from the normalized slab pressures. -/
def gluedPressure (p : Ioo (0 : ℝ) 1 → Pressure) : Pressure :=
  fun t => normalizedPressure (p (slabEnd t)) t

theorem normalizedPressure_contDiffOn {T : ℝ} {p : Pressure}
    (hp : ContDiffOn ℝ ∞ (fun z : ℝ × Space => p z.1 z.2) (Icc 0 T ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => normalizedPressure p z.1 z.2) (Icc 0 T ×ˢ univ) := by
  have hf : ContDiff ℝ ∞ (fun z : ℝ × Space => (z.1, (0 : Space))) := by
    first
    | fun_prop
    | exact contDiff_fst.prodMk contDiff_const
  have h2 : ContDiffOn ℝ ∞ (fun z : ℝ × Space => p z.1 0) (Icc 0 T ×ˢ univ) :=
    hp.comp hf.contDiffOn (fun z hz => ⟨hz.1, mem_univ _⟩)
  exact hp.sub h2

/-- A function glued from slab functions that agree on overlaps is smooth on
[0,1) × R³ when every slab function is smooth on its closed slab. -/
theorem glued_contDiffOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Ioo (0 : ℝ) 1 → ℝ → Space → E)
    (hF : ∀ T : Ioo (0 : ℝ) 1,
      ContDiffOn ℝ ∞ (fun z : ℝ × Space => F T z.1 z.2) (Icc 0 (T : ℝ) ×ˢ univ))
    (hagree : ∀ S T : Ioo (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) (min (S : ℝ) T), F S t = F T t) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => F (slabEnd z.1) z.1 z.2) (Ico 0 1 ×ˢ univ) := by
  apply contDiffOn_of_locally_contDiffOn
  intro z hz
  refine ⟨Iio ((slabEnd z.1 : ℝ)) ×ˢ univ, isOpen_Iio.prod isOpen_univ,
    ⟨lt_slabEnd hz.1, mem_univ _⟩, ?_⟩
  refine ((hF (slabEnd z.1)).mono ?_).congr ?_
  · intro w hw
    exact ⟨⟨hw.1.1.1, le_of_lt (Set.mem_Iio.1 hw.2.1)⟩, mem_univ _⟩
  · intro w hw
    have hw0 : w.1 ∈ Icc (0 : ℝ) (min ((slabEnd w.1 : ℝ)) (slabEnd z.1)) :=
      ⟨hw.1.1.1, le_min (lt_slabEnd hw.1.1).le (le_of_lt (Set.mem_Iio.1 hw.2.1))⟩
    exact congrFun (hagree (slabEnd w.1) (slabEnd z.1) w.1 hw0) w.2

/-- The glued velocity is the slab velocity on each closed slab. -/
theorem gluedVelocity_eq (U : Ioo (0 : ℝ) 1 → Velocity)
    (hagree : ∀ S T : Ioo (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) (min (S : ℝ) T), U S t = U T t)
    (T : Ioo (0 : ℝ) 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : gluedVelocity U t = U T t := by
  have ht1 : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1, ht.2.trans_lt T.2.2⟩
  exact hagree (slabEnd t) T t ⟨ht.1, le_min (lt_slabEnd ht1).le ht.2⟩

/-- The glued velocity and pressure form one smooth solution on [0,1). -/
theorem glued_solution (φ : VectorField) (U : Ioo (0 : ℝ) 1 → Velocity)
    (p : Ioo (0 : ℝ) 1 → Pressure)
    (hs : ∀ T : Ioo (0 : ℝ) 1, Breakdown.IsSolutionOn T (U T) (p T))
    (h0 : ∀ T : Ioo (0 : ℝ) 1, U T 0 = φ)
    (hagree : ∀ S T : Ioo (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) (min (S : ℝ) T), U S t = U T t) :
    IsSmoothSolutionBefore 1 1 φ (gluedVelocity U) (gluedPressure p) := by
  have hpagree : ∀ S T : Ioo (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) (min (S : ℝ) T),
      normalizedPressure (p S) t = normalizedPressure (p T) t := fun S T t ht =>
    funext (Theorem11Glue.pressure_agree (hs S) (hs T) (hagree S T) (lt_min S.2.1 T.2.1) t ht)
  refine { smooth_velocity := ?_, smooth_pressure := ?_, initial := ?_,
           momentum := ?_, incompressible := ?_ }
  · exact glued_contDiffOn U (fun T => (hs T).smooth_velocity) hagree
  · exact glued_contDiffOn (fun T => normalizedPressure (p T))
      (fun T => normalizedPressure_contDiffOn (hs T).smooth_pressure) hpagree
  · intro x
    show U (slabEnd 0) 0 x = φ x
    rw [h0]
  · intro t ht x
    have ht1 : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
    have htT : t < (slabEnd t : ℝ) := lt_slabEnd ht1
    have hd : deriv (fun τ => gluedVelocity U τ x) t =
        deriv (fun τ => U (slabEnd t) τ x) t :=
      Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (Ioo_mem_nhds ht.1 htT)
        fun τ hτ => congrFun (gluedVelocity_eq U hagree (slabEnd t) (t := τ) ⟨hτ.1.le, hτ.2.le⟩) x)
    have hpg : pressureGradientAt (gluedPressure p t) x =
        pressureGradientAt (p (slabEnd t) t) x := by
      show pressureGradientAt (fun y => p (slabEnd t) t y - p (slabEnd t) t 0) x = _
      first
      | simp only [pressureGradientAt, fderiv_sub_const]
      | simp [pressureGradientAt]
    have hm := (smooth_before_of_library (hs (slabEnd t)) (h0 (slabEnd t))).momentum
      t ⟨ht.1, htT⟩ x
    rw [hd, hpg]
    exact hm
  · intro t ht x
    exact (hs (slabEnd t)).incompressible t ⟨ht.1, (lt_slabEnd ht).le⟩ x

end Theorem11
