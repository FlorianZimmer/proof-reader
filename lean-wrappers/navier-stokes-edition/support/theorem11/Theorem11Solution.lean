import Theorem11Challenge
import SpaceCore
import SmoothReadings
import Theorem11PhysicalBridges
import Theorem11Energy
import Theorem11Glue
import Theorem11Continuation
import Breakdown.Uniqueness.SmoothUniqueness

/-!
Proofs of the Theorem 1.1 contracts on R³ for a profile of the library's class.

`theorem11SpaceLocal` and `theorem11SpaceSlabs` give a solution on every slab
[0,T), T < 1. `theorem11SpaceBlowup` glues those slab solutions into one smooth
finite-energy solution on [0,1) (the velocities agree by the library's
uniqueness, the pressures after normalizing them to vanish at the origin, and
the energy is bounded by that of the datum through the energy inequality in
`Theorem11Energy`). It also proves that every smooth finite-energy solution
with the same datum is this one, and that none extends smoothly with finite
energy to the closed interval [0,1]. `theorem11Space` is its first part.

`Theorem11.theorem11Torus` is not declared: see `Theorem11OpenTargets`.
-/

open MeasureTheory Set Real
open scoped ContDiff ENNReal

noncomputable section

namespace Theorem11

/-- Same-profile, arbitrary-tolerance quantitative construction in the
library's concrete frequency space, with local smooth physical readings. -/
theorem theorem11SpaceCore (W : Velocity) (q : Pressure) (P : ℝ)
    (R : Space ≃ₗᵢ[ℝ] Space) (A : ℝ) (h : IsLibraryProfile W q P R A)
    (ε : ℝ) (hε : 0 < ε) : Nonempty (Theorem11Core.SpaceWitness W ε) := by
  have hs := libraryProfile_to_similarity h
  rcases h with ⟨hP, _, _, _, _, hper, hn, _, _⟩
  exact Theorem11Core.space_core W q P R A hP hs hper hn ε hε

/-- A physical weaker endpoint: one compact datum, arbitrarily close to the
selected profile, admits a smooth finite-energy solution on each compact
subinterval before time one. The energy constant may depend on that interval.
This does not assert the full physical blow-up or convergence theorem. -/
theorem theorem11SpaceLocal : Theorem11SpaceLocal := by
  intro W q P R A h ε hε
  obtain ⟨d⟩ := theorem11SpaceCore W q P R A h ε hε
  refine ⟨d.datum, d.datum_test.1, d.datum_test.2.1, d.datum_test.2.2,
    d.initial_gradient_finite, d.initial_gradient_close, ?_⟩
  intro T hT hT1
  obtain ⟨U, p, hs, hi, hE, _, _⟩ := d.local_physical T hT hT1
  exact ⟨U, p, smooth_before_of_library hs hi, energy_before_of_library hE⟩

/-- The same compact datum and quantitative constants work on every compact
slab. The physical norm and rescaled error are genuine spatial integrals.
The global endpoints below glue these slabs into one solution.
-/
theorem theorem11SpaceSlabs : Theorem11SpaceSlabs := by
  intro W q P R A h ε hε
  have hp := libraryProfile_to_similarity h
  obtain ⟨d⟩ := theorem11SpaceCore W q P R A h ε hε
  let C : ℝ := max d.lowerConstant (max d.upperConstant d.errorConstant)
  have hcu : d.upperConstant ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hce : d.errorConstant ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨d.datum, d.lowerConstant, C, d.exponent,
    d.datum_test.1, d.datum_test.2.1, d.datum_test.2.2,
    d.initial_gradient_finite, d.initial_gradient_close,
    d.lowerConstant_pos, le_max_left _ _, d.exponent_pos, d.exponent_lt_quarter, ?_⟩
  intro T hT hT1
  obtain ⟨U, p, hs, hi, hE, _, _, hquant⟩ :=
    Theorem11Core.local_physical_quantitative W q A ε hp d T hT hT1
  refine ⟨U, p, smooth_before_of_library hs hi, energy_before_of_library hE, ?_⟩
  intro t ht
  obtain ⟨hf, _, hlo, hhi, he, hconv⟩ := hquant t ⟨ht.1, ht.2.le⟩
  have hdt : 0 ≤ 1 - t := by linarith [ht.2, hT1]
  refine ⟨hf, hlo, ?_, he, ?_⟩
  · exact hhi.trans (mul_le_mul_of_nonneg_right hcu (Real.rpow_nonneg hdt _))
  · exact hconv.trans (mul_le_mul_of_nonneg_right hce (Real.rpow_nonneg hdt _))

/-- The old existential statement is a consequence of the selected profile.
This compatibility theorem does not discard the selected profile in Core. -/
theorem profile_exists_of_libraryProfile (W : Velocity) (q : Pressure) (P : ℝ)
    (R : Space ≃ₗᵢ[ℝ] Space) (A : ℝ) (h : IsLibraryProfile W q P R A) :
    Breakdown.PeriodicSimilarityProfileExists :=
  libraryProfile_to_exists h

/-- A smooth solution on [0,T) with T > S restricts to the library's class on
the closed slab [0,S]. -/
theorem isSolutionOn_of_before {T S : ℝ} {φ : VectorField} {v : Velocity} {q : Pressure}
    (hv : IsSmoothSolutionBefore 1 T φ v q) (hST : S < T) : Breakdown.IsSolutionOn S v q := by
  refine ⟨hv.smooth_velocity.mono ?_, hv.smooth_pressure.mono ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans_lt hST⟩, hz.2⟩
  · intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans_lt hST⟩, hz.2⟩
  · intro t ht x
    have h := hv.momentum t ⟨ht.1, ht.2.trans hST⟩ x
    rw [one_smul] at h
    exact h
  · intro t ht x
    exact hv.incompressible t ⟨ht.1, ht.2.trans_lt hST⟩ x

theorem energyBoundedOn_of_before {T S : ℝ} {v : Velocity}
    (hv : UniformFiniteEnergyBefore T v) (hST : S < T) : Breakdown.EnergyBoundedOn S v := by
  obtain ⟨E, _, hE⟩ := hv
  exact ⟨E, fun t ht => hE t ⟨ht.1, ht.2.trans_lt hST⟩⟩

/-- A smooth solution on [0,T] restricts to the library's class on [0,S], S ≤ T. -/
theorem isSolutionOn_of_through {T S : ℝ} {φ : VectorField} {v : Velocity} {q : Pressure}
    (hv : IsSmoothSolutionThrough 1 T φ v q) (hST : S ≤ T) : Breakdown.IsSolutionOn S v q := by
  refine ⟨hv.smooth_velocity.mono ?_, hv.smooth_pressure.mono ?_, ?_, ?_⟩
  · intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans hST⟩, hz.2⟩
  · intro z hz
    exact ⟨⟨hz.1.1, hz.1.2.trans hST⟩, hz.2⟩
  · intro t ht x
    have h := hv.momentum t ⟨ht.1, ht.2.trans_le hST⟩ x
    rw [one_smul] at h
    exact h
  · intro t ht x
    exact hv.incompressible t ⟨ht.1, ht.2.trans hST⟩ x

theorem energyBoundedOn_of_through {T S : ℝ} {v : Velocity}
    (hv : UniformFiniteEnergyThrough T v) (hST : S ≤ T) : Breakdown.EnergyBoundedOn S v := by
  obtain ⟨E, _, hE⟩ := hv
  exact ⟨E, fun t ht => hE t ⟨ht.1, ht.2.trans hST⟩⟩

/-- Theorem 1.1 on R³, conditional on the profile premise.

Conditional on the profile premise `IsLibraryProfile W q P R A`: a smooth
pair (W, q) on ℝ × R³, not identically zero, solving the profile equations (1.2)
(the similarity residual vanishes and div W = 0), periodic up to the isometry
R with period P > 0, W(s+P, y) = R W(s, R⁻¹y), with the decay bounds
‖∇ʲW(s,y)‖ ≤ A (1+|y|)^-(j+1) for j = 0, 1, 2 and |∇q(s,y)| ≤ A (1+|y|)^-3.
This is the premise of the authors' route (`Breakdown.IsSimilarityProfile`);
it is stronger than the printed hypothesis (1.2)-(1.3), see
`Theorem11.OpenTarget.PaperSpace`.

Under this premise, for every ε > 0, in the paper's words: there exist a divergence-free datum u₀ in C_c^∞(R³; R³), within ε of the
profile's slice W(0) in the Ḣ¹ seminorm, and a smooth solution u of the
Navier–Stokes equations on [0,1) × R³ with datum u₀ and finite energy, which
blows up at time 1: there exist κ in (0, 1/4) and constants 0 < c ≤ C with
c (1-t)^(-1/4) ≤ ‖∇u(t)‖_{L²} ≤ C (1-t)^(-1/4), and, in self-similar variables,
‖∇(√(1-t) u(t, √(1-t) ·) - W(-log(1-t)))‖_{L²} ≤ C (1-t)^κ, for t in [0,1).
Moreover every smooth finite-energy solution with datum u₀ on an interval
[0,T), T ≤ 1, is u there, and no smooth solution with datum u₀ and finite
energy exists on the closed interval [0,1]. -/
theorem theorem11SpaceBlowup : Theorem11SpaceBlowup := by
  intro W q P R A h ε hε
  have hp := libraryProfile_to_similarity h
  obtain ⟨d⟩ := theorem11SpaceCore W q P R A h ε hε
  obtain ⟨hP, -, -, -, -, hper, hn, -, -⟩ := h
  have hslab := fun T : Ioo (0 : ℝ) 1 =>
    Theorem11Core.local_physical_quantitative W q A ε hp d T T.2.1 T.2.2
  choose U p hs h0 hE hB hread hquant using hslab
  have hagree : ∀ S T : Ioo (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) (min (S : ℝ) T), U S t = U T t :=
    fun S T => Theorem11Core.local_velocity_unique d.state (hs S) (hs T) (hread S) (hread T)
  have hsol := glued_solution d.datum U p hs h0 hagree
  have hE0 : (∫⁻ x, ENNReal.ofReal (‖d.datum x‖ ^ 2)) ≠ ⊤ := by
    obtain ⟨B, hB0⟩ := hE (slabEnd 0)
    have h00 := hB0 0 ⟨le_rfl, (slabEnd 0).2.1.le⟩
    rw [h0] at h00
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h00
  have henergy : UniformFiniteEnergyBefore 1 (gluedVelocity U) := by
    refine ⟨(∫⁻ x, ENNReal.ofReal (‖d.datum x‖ ^ 2)).toReal, ENNReal.toReal_nonneg,
      fun t ht => ?_⟩
    have hle := Theorem11Energy.energy_le_initial (hs (slabEnd t)) (hE (slabEnd t))
      ⟨ht.1, (lt_slabEnd ht).le⟩
    rw [h0] at hle
    exact hle.trans (ENNReal.ofReal_toReal hE0).ge
  -- Any smooth finite-energy solution with the same datum agrees with a slab.
  have hunique : ∀ (S : Ioo (0 : ℝ) 1) (v : Velocity) (q' : Pressure),
      Breakdown.IsSolutionOn S v q' → Breakdown.EnergyBoundedOn S v → v 0 = d.datum →
      ∀ t ∈ Icc (0 : ℝ) S, v t = U S t := by
    intro S v q' hvS hvE hv0 t ht
    have heq := Breakdown.eq_of_isSolutionOn (hs S) hvS (hE S) hvE (hB S)
      (by rw [h0 S, hv0])
    exact (heq t ht).symm
  let C : ℝ := max d.lowerConstant (max d.upperConstant d.errorConstant)
  have hcu : d.upperConstant ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hce : d.errorConstant ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨d.datum, gluedVelocity U, gluedPressure p, d.lowerConstant, C, d.exponent,
    d.datum_test.1, d.datum_test.2.1, d.datum_test.2.2,
    d.initial_gradient_finite, d.initial_gradient_close, hsol, henergy,
    d.lowerConstant_pos, le_max_left _ _, d.exponent_pos, d.exponent_lt_quarter,
    ?_, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨hf, _, hlo, hhi, _, _⟩ := hquant (slabEnd t) t ⟨ht.1, (lt_slabEnd ht).le⟩
    have hdt : 0 ≤ 1 - t := by linarith [ht.2]
    exact ⟨hf, hlo, hhi.trans (mul_le_mul_of_nonneg_right hcu (Real.rpow_nonneg hdt _))⟩
  · intro t ht
    obtain ⟨_, _, _, _, he, hconv⟩ := hquant (slabEnd t) t ⟨ht.1, (lt_slabEnd ht).le⟩
    have hdt : 0 ≤ 1 - t := by linarith [ht.2]
    exact ⟨he, hconv.trans (mul_le_mul_of_nonneg_right hce (Real.rpow_nonneg hdt _))⟩
  · intro T hT1 v q' hv hvE t ht
    obtain ⟨S, hS⟩ : ∃ S : Ioo (0 : ℝ) 1, (S : ℝ) = (t + T) / 2 :=
      ⟨⟨(t + T) / 2, by linarith [ht.1, ht.2], by linarith [ht.2]⟩, rfl⟩
    have htS : t ∈ Icc (0 : ℝ) S := ⟨ht.1, by rw [hS]; linarith [ht.2]⟩
    have hST : (S : ℝ) < T := by rw [hS]; linarith [ht.2]
    rw [gluedVelocity_eq U hagree S htS]
    exact hunique S v q' (isSolutionOn_of_before hv hST) (energyBoundedOn_of_before hvE hST)
      (funext hv.initial) t htS
  · rintro ⟨v, q', hv, hvE⟩
    refine Theorem11Core.no_continuous_continuation W q P R A hP hp hper hn d
      hv.smooth_velocity.continuousOn (fun t ht => ?_)
    obtain ⟨S, hS⟩ : ∃ S : Ioo (0 : ℝ) 1, (S : ℝ) = (t + 1) / 2 :=
      ⟨⟨(t + 1) / 2, by linarith [ht.1], by linarith [ht.2]⟩, rfl⟩
    have htS : t ∈ Icc (0 : ℝ) S := ⟨ht.1, by rw [hS]; linarith [ht.2]⟩
    have hS1 : (S : ℝ) ≤ 1 := by rw [hS]; linarith [ht.2]
    have hvt := hunique S v q' (isSolutionOn_of_through hv hS1)
      (energyBoundedOn_of_through hvE hS1) (funext hv.initial) t htS
    rw [hvt]
    exact hread S t htS

/-- The requested endpoint `Theorem11Space`, the first part of
`theorem11SpaceBlowup`. Conditional on the profile premise `IsLibraryProfile W q P R A`: a smooth
pair (W, q) on ℝ × R³, not identically zero, solving the profile equations (1.2)
(the similarity residual vanishes and div W = 0), periodic up to the isometry
R with period P > 0, W(s+P, y) = R W(s, R⁻¹y), with the decay bounds
‖∇ʲW(s,y)‖ ≤ A (1+|y|)^-(j+1) for j = 0, 1, 2 and |∇q(s,y)| ≤ A (1+|y|)^-3.
This is the premise of the authors' route (`Breakdown.IsSimilarityProfile`);
it is stronger than the printed hypothesis (1.2)-(1.3), see
`Theorem11.OpenTarget.PaperSpace`.
Under it: one smooth finite-energy solution on [0,1) from a compactly supported
datum ε-close to W(0) in Ḣ¹, with the two-sided rate c(1-t)^(-1/4) ≤ ‖∇u(t)‖₂ ≤
C(1-t)^(-1/4) and the self-similar convergence rate (1-t)^κ. -/
theorem theorem11Space : Theorem11Space := by
  intro W q P R A h ε hε
  obtain ⟨u₀, u, p, c, C, κ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, -, -⟩ :=
    theorem11SpaceBlowup W q P R A h ε hε
  exact ⟨u₀, u, p, c, C, κ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩

end Theorem11
