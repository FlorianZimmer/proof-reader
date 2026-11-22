/-
# Full extended-certificate conclusion

Status: NOT COMPILED. Target: Lean 4.33.1 / ad53419 with added keep modules and no source replacement.
Every output below belongs to the same selected parameter and exact profile.
No extra hypothesis represents the desired conclusion or a missing bridge.
-/
import Theorem71Keep
import Theorem71Smooth
import Theorem71Statements
import Theorem71Transport
import Theorem71GradientBound

open MeasureTheory Filter
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Breakdown.Theorem71

open Cert

/-- Keep the selected construction and promote its actual correction to the
C1 representative supplied by the smooth exact profile. -/
theorem extendedConclusion_of_held {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) (a : HeldWitness d) : ExtendedConclusion d := by
  obtain ⟨W, q, C, hS, hDecay, hraw⟩ := a.smoothWithData
  let V : VelField := correction (d.period a.parameter) (d.profile a.parameter) W
  let G : GradField := gradient V
  have hA : ContDiff ℝ 1 (fun z : ℝ × Space => d.profile a.parameter z.1 z.2) :=
    Cert.Internal.AtProfile.profile_slice_smooth hd a.parameter
  have hC1 : ContDiff ℝ 1 (fun z : ℝ × Space => V z.1 z.2) :=
    Transport.normalized_error_C1 hS.smooth_field hA
  have hPeriod : ∀ s y, W (s + d.period a.parameter) y = W s y :=
    fun s y => (hS.periodic s y).trans rfl
  have hVPeriod : IsTimePeriodic V :=
    Transport.normalized_error_periodic hPeriod (hd.profile_periodic a.parameter)
  have he : ∀ᵐ σ : ℝ, V σ =ᵐ[volume] a.correction σ := by
    filter_upwards [hraw] with σ hσ
    filter_upwards [hσ] with y hy
    change W (d.period a.parameter * σ) y - d.profile a.parameter σ y = a.correction σ y
    rw [hy]
    abel
  have hr : IsReadingOf (freeInv (d.period a.parameter) a.forcing) V G a.second :=
    Transport.reading_of_C1_representative a.reading hC1 hVPeriod he
  obtain ⟨g, hPert, -⟩ := constructionNodes.freePerturbation
    d.symmetries (d.period a.parameter) hS.period_pos a.forcing a.held.invariant
    V G a.second hr
  have hWeight : IsAdmissibleWeight d.weightFn d.weight :=
    ⟨hd.weight_pos, hd.weightFn_measurable, hd.weightFn_lower,
      ⟨d.weightMax, hd.weightFn_upper⟩⟩
  have hFinite : periodLIntegral (fun σ y =>
      ‖secondDerivTrace (a.second σ y)‖ ^ 2 + d.weightFn y * matSq (G σ y)) < ⊤ :=
    Transport.weighted_integral_finite hPert hWeight
  have hSize : weightedEnergy d.weightFn G a.second
      + d.multiplierWeight ^ 2 * (∑ i, d.multiplier a.parameter i ^ 2)
      ≤ 4 * d.sizeBound ^ 2 := held_energy_bound hd a hr
  have hWd : ∀ s y, ‖fderiv ℝ (W s) y‖ ≤ C / (1 + ‖y‖) ^ 2 := by
    intro s y
    have h := hDecay.1 s y 1 (by norm_num)
    rw [norm_iteratedFDeriv_one] at h
    simpa using h
  have hVd : ∀ σ y, ‖fderiv ℝ (V σ) y‖ ≤ (C + d.decay) / (1 + ‖y‖) ^ 2 :=
    Transport.normalized_error_gradient_decay hS.smooth_field hA hWd
      (fun σ y => (hd.profile_decay a.parameter a.parameter_mem σ y).2.1)
  have hSup : ∀ σ : ℝ, ∫⁻ y, ENNReal.ofReal (matSq (G σ y))
      ≤ ENNReal.ofReal (d.supBound ^ 2) :=
    Transport.gradient_lintegral_bound_everywhere hr hC1 hVd hd.supBound_pos.le a.held.sup
  have hPins : ∀ i, pinValue (d.pin i) G = d.targetGap a.parameter i :=
    held_pin_value hd a hr
  have hInvariant : ∀ γ ∈ d.symmetries, ∀ σ y,
      V (σ + γ.2) (γ.1 y) = γ.1 (V σ y) :=
    Transport.invariant_everywhere hC1.continuous hPert.invariant
  have hSymmetry : PrescribedSymmetries d.symmetries (d.period a.parameter) W := by
    intro γ hγ
    exact Transport.physical_symmetry hS.period_pos.ne'
      (hd.profile_invariant a.parameter a.parameter_mem γ hγ) (hInvariant γ hγ)
  refine ⟨a.parameter, a.parameter_mem, W, q, ?_, ?_, hSymmetry⟩
  · exact ⟨hS.period_pos, hS.smooth_field, hS.smooth_pressure, hS.residual,
      hS.divergence, hPeriod, hS.nonzero, C, hDecay.1, hDecay.2⟩
  · exact ⟨a.second, g, hPert, hFinite, hSize, hSup, hPins⟩

/-- The full public conclusion, obtained from a certificate without any
additional premise. Kernel compilation is still required for this new file. -/
theorem extendedConclusion {k : ℕ} (d : ExtendedCertificateData k)
    (hd : IsExtendedCertificate d) : ExtendedConclusion d := by
  obtain ⟨a⟩ := heldWitness_exists d hd
  exact extendedConclusion_of_held hd a

/-- The retained Theorem 7.1 construction holds for every formal extended certificate. -/
theorem extended : Breakdown.Theorem71Extended := by
  intro k d hd
  exact extendedConclusion d hd

end Breakdown.Theorem71
