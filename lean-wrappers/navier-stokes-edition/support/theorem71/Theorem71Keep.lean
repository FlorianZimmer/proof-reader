/-
Theorem 7.1: retaining the chosen parameter and correction.
Target: Lean 4.33.1, authors' unchanged ad53419 library.
This version imports three added witness-retaining modules. No authors' file is replaced.
See the return validation record for compilation status.
-/
import Theorem71KeepTypes
import Theorem71KeepSigma
import Theorem71KeepRescale
import Theorem71KeepOrbit
import Breakdown.Cert.ExtendedMain
import Breakdown.Weak.Main

open MeasureTheory Filter
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Breakdown.Theorem71

open Cert Freq

/-- The normalization already used in `extended_certificate_orbit_proved`. -/
def normalData {k : ℕ} (d : ExtendedCertificateData k) : ExtendedCertificateData k :=
  d.withUnitWeight.atProfile

/-- The authors' unit-weight and at-profile reductions make every formal extended certificate normalized. -/
theorem normalData_isNormal {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) : IsNormalExtendedCertificate (normalData d) :=
  ⟨extendedAtProfileHolds (extendedUnitWeightHolds hd), rfl, rfl, rfl, rfl⟩

/-- Concrete imported nodes needed before any existential witness is forgotten. -/
structure ConstructionNodes : Prop where
  zeroHeld : ExtendedExistsZeroHeldHolds
  sliceReading : SliceReadingHolds
  weakEquation : ExtendedHeldWeakEquationHolds
  nonzero : ExtendedHeldNonzeroHolds
  readingEnergy : ReadingEnergyHolds
  freePerturbation : FreePerturbationHolds
  data : ExtendedDataHolds

/-- This is the dependency composition in `ExtendedAssembly`, with useful
    intermediate conclusions retained. No analytical lemma is reproved. -/
theorem constructionNodes : ConstructionNodes := by
  have proj : ProjectionHolds :=
    ⟨exists_projSpec, norm_solProj_le, inner_solProj, solProj_toPhysH⟩
  have graph : GraphClosedHolds := fun q => halfSsp_of_xbar q
  have prop : PropagatorBoundHolds :=
    ⟨fun τ hτ x => by simpa only [neg_div] using norm_slicePropagator_le τ hτ x,
      fun x => GradInv.Internal.continuousOn_slicePropagator x⟩
  have gradInvProof : GradInvHolds :=
    fun P _ => ⟨integrable_propagatorIntegrand P, exists_gradInvSpec P⟩
  have reading : ReadingExistsHolds := readingExistsHolds_proof
  have energy : ReadingEnergyHolds := readingEnergyHolds_of graph
  have free : FreeInvHolds := freeInvHolds_of prop gradInvProof graph
  have localEnergy : FreeEnergyLocalHolds := freeEnergyLocalHolds_of prop gradInvProof graph free
  have equiv : FreeEquivariantHolds := freeEquivariantHolds_of free
  have perturbation : FreePerturbationHolds :=
    freePerturbationHolds_of free equiv reading proj testPairingHolds_proof prop gradInvProof graph
  have slices : SliceReadingHolds := sliceReadingHolds_of localEnergy reading graph gradInvProof free
  have product : ProductBoundHolds := productBoundHolds_of (sliceSupBoundHolds_of graph) reading energy
  have pairing : ProductPairingHolds := productPairingHolds_of product proj testPairingHolds_proof reading
  have subtraction : ProductSubHolds := productSubHolds_of reading product
  have convection : ExtendedConvectionHolds := extendedConvectionHolds_of reading proj testPairingHolds_proof
  have invariance : ExtendedInvarianceHolds :=
    extendedInvarianceHolds_of convection proj testPairingHolds_proof testDenseHolds_proof
  have data : ExtendedDataHolds := extendedDataHolds_of proj testPairingHolds_proof energy
  have coercive : ExtendedCoerciveBorderedHolds :=
    extendedCoerciveBorderedHolds_of reading energy perturbation convection data testPairingHolds_proof
  have sup : ExtendedSupBoundHolds := extendedSupBoundHolds_of localEnergy
    (extendedFrozenBridgeHolds_of slices equiv proj) invariance data energy convection equiv
  have compact : LocalCompactnessHolds := localCompactnessHolds_of
    (timeModulusHolds_of free reading proj prop gradInvProof graph)
    (spaceModulusHolds_of reading graph) translationCriterionHolds_proof free reading
  have inverse : ExtendedBorderedInvertibleHolds := extendedBorderedInvertibleHolds_of
    (extendedConvectionCompactHolds_of compact convection free) coercive invariance equiv
  have metric : ExtendedHeldMetricHolds := extendedHeldMetricHolds_of graph energy
  have unique : ExtendedHeldExistsUniqueHolds := extendedHeldExistsUniqueHolds_of
    contractionFixedPointHolds_proof metric
    (extendedHeldMapsToHolds_of inverse coercive sup product pairing data invariance equiv rowNormHolds)
    (extendedHeldContractsHolds_of inverse coercive sup product pairing subtraction data invariance equiv rowNormHolds)
    inverse equiv invariance
  have limit : ExtendedHeldLimitHolds := extendedHeldLimitHolds_of (periodContinuityHolds_of free)
    compact (extendedConvectionContinuityHolds_of convection) (extendedDataContinuityHolds_of data)
    pairing product free data reading testDenseHolds_proof
  have adjoint : ExtendedAdjointEnclosureHolds := extendedAdjointEnclosureHolds_of
    (extendedAdjointPairingHolds_of proj testPairingHolds_proof) perturbation reading energy
    convection data product testPairingHolds_proof proj Held.adjointEnclosure
  exact
    { zeroHeld := extendedExistsZeroHeldHolds_of unique (extendedMultiplierContinuityHolds_of limit unique)
        adjoint extendedStiffEnclosureHolds Held.testSetZero
      sliceReading := slices
      weakEquation := extendedHeldWeakEquationHolds_of perturbation convection data pairing product testPairingHolds_proof
      nonzero := extendedHeldNonzeroHolds_of energy
      readingEnergy := energy
      freePerturbation := perturbation
      data := data }

/-- A single certificate construction, before rescaling or regularization. -/
structure HeldWitness {k : ℕ} (d : ExtendedCertificateData k) where
  parameter : Fin k → ℝ
  parameter_mem : parameter ∈ d.params
  forcing : HH
  multiplierCorrection : Fin k → ℝ
  correction : VelField
  gradient : GradField
  second : SecondField
  constant : ℝ
  held : (normalData d).IsHeldSolution parameter forcing multiplierCorrection
  multiplier_cancel : (normalData d).multiplier parameter + multiplierCorrection = 0
  reading : IsReadingOf (freeInv (d.period parameter) forcing) correction gradient second
  sigma : IsSigmaProfile (d.period parameter)
    (fun σ y => d.profile parameter σ y + correction σ y)
    (fun σ y => fderiv ℝ (d.profile parameter σ) y + gradient σ y)
    (fun σ y => d.profileSecondDeriv parameter σ y + second σ y) constant

/-- The selected parameter and all its correction data are retained together. -/
theorem heldWitness_exists {k : ℕ} (d : ExtendedCertificateData k)
    (hd : IsExtendedCertificate d) : Nonempty (HeldWitness d) := by
  let n := constructionNodes
  have hn := normalData_isNormal hd
  obtain ⟨α, hα, f, κ, hf, hcancel⟩ := n.zeroHeld (normalData d) hn
  obtain ⟨v, G, H, hr, C, hσ⟩ := Cert.extendedSigmaProfileOfHeld_keep
    n.sliceReading n.weakEquation n.nonzero (normalData d) hn.certificate α hα f κ hf hcancel
  exact ⟨{
    parameter := α
    parameter_mem := hα
    forcing := f
    multiplierCorrection := κ
    correction := v
    gradient := G
    second := H
    constant := C
    held := hf
    multiplier_cancel := hcancel
    reading := hr
    sigma := hσ }⟩

/-- The abstract orbit represents the prescribed weak profile, at its exact period. -/
theorem weakOrbitKeeping {W : VelField} {G : GradField} {H : SecondField}
    {P C : ℝ} {R : Space ≃ₗᵢ[ℝ] Space} (h : WeakProfileAt W G H P R C) :
    ∃ w : ℝ → X, realization.F.IsOrbit (realization.rot R) w P ∧
      ∀ᵐ s, ∀ᵐ y, (velocity (w s) : Space → Space) y = W s y :=
  WeakProfile.weakOrbitOfParts_keep WeakProfile.pairingVelocity_holds
    WeakProfile.velocityWeakGradient_holds WeakProfile.zeroGradientSix_holds
    WeakProfile.gradientFreqTr_holds WeakProfile.sliceEmbedding_holds
    WeakProfile.advectionByParts_holds WeakProfile.pairingDilate_holds
    WeakProfile.trilinearDilate_holds WeakProfile.sliceMeasurable_holds
    WeakProfile.scaledTestField_holds WeakProfile.sliceIntegrand_holds WeakProfile.similarityIdentity_holds
    (WeakProfile.physicalIdentity_of_parts WeakProfile.pairingVelocity_holds WeakProfile.velocityWeakGradient_holds)
    WeakProfile.constOfWeakDeriv_holds WeakProfile.goodTimes_holds WeakProfile.bilinIntegrable_holds
    WeakProfile.varConstInner_holds WeakProfile.varConstGood_holds WeakProfile.continuousVarConst_holds
    WeakProfile.mildFromGood_holds WeakProfile.globalRepresentative_holds
    WeakProfile.timeChangeNull_holds WeakProfile.physicalCurveMeasurable_holds h

/-- Rescaling keeps both the parameter's period and the identity isometry. -/
theorem HeldWitness.orbit {k : ℕ} {d : ExtendedCertificateData k} (a : HeldWitness d) :
    ∃ w : ℝ → X,
      realization.F.IsOrbit (realization.rot (LinearIsometryEquiv.refl ℝ Space)) w (d.period a.parameter) ∧
      ∀ᵐ s, ∀ᵐ y, (velocity (w s) : Space → Space) y =
        d.profile a.parameter ((d.period a.parameter)⁻¹ * s) y
          + a.correction ((d.period a.parameter)⁻¹ * s) y :=
  weakOrbitKeeping (weakPeriodicSimilarityProfileOf_sigma_keep a.sigma)

/-- The normalized multiplier correction is exactly minus omega times the original multiplier. -/
theorem HeldWitness.multiplierCorrection_eq {k : ℕ} {d : ExtendedCertificateData k}
    (a : HeldWitness d) (i : Fin k) :
    a.multiplierCorrection i = -(d.multiplierWeight * d.multiplier a.parameter i) := by
  have h := congrFun a.multiplier_cancel i
  change d.multiplierWeight * d.multiplier a.parameter i + a.multiplierCorrection i = 0 at h
  linarith

/-- The full first inequality in (7.38), including its multiplier penalty.
    It holds for every reading of this same correction, so it survives changing representatives. -/
theorem held_energy_bound {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) (a : HeldWitness d)
    {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf (freeInv (d.period a.parameter) a.forcing) v G H) :
    weightedEnergy d.weightFn G H
      + d.multiplierWeight ^ 2 * (∑ i, d.multiplier a.parameter i ^ 2) ≤ 4 * d.sizeBound ^ 2 := by
  let u := freeInv (d.period a.parameter) a.forcing
  have hw : ∀ y, 0 ≤ d.weightFn y := fun y => hd.weight_pos.le.trans (hd.weightFn_lower y)
  have he : 0 ≤ energyW d.weightFn u := by
    unfold energyW sliceWeightedGrad
    exact add_nonneg (sq_nonneg _) (integral_nonneg fun t => integral_nonneg fun y =>
      mul_nonneg (hw y) (Finset.sum_nonneg fun i _ => sq_nonneg _))
  have hsum0 : 0 ≤ ∑ i, a.multiplierCorrection i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsize : Real.sqrt (energyW d.weightFn u + ∑ i, a.multiplierCorrection i ^ 2)
      ≤ 2 * d.sizeBound := a.held.size
  have hsquare := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsize 2
  rw [Real.sq_sqrt (add_nonneg he hsum0)] at hsquare
  have hsum : (∑ i, a.multiplierCorrection i ^ 2) =
      d.multiplierWeight ^ 2 * (∑ i, d.multiplier a.parameter i ^ 2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [a.multiplierCorrection_eq i]
    ring
  have hweight : IsAdmissibleWeight d.weightFn d.weight :=
    ⟨hd.weight_pos, hd.weightFn_measurable, hd.weightFn_lower, d.weightMax, hd.weightFn_upper⟩
  have hreading := constructionNodes.readingEnergy d.weightFn d.weight hweight u v G H hr
  rw [hreading.1, ← hsum]
  nlinarith [hsquare]

/-- Pins are values of the correction, hence the right side is targetGap. -/
theorem held_pin_value {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) (a : HeldWitness d)
    {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf (freeInv (d.period a.parameter) a.forcing) v G H) (i : Fin k) :
    pinValue (d.pin i) G = d.targetGap a.parameter i := by
  have hn := normalData_isNormal hd
  have hdata := constructionNodes.data (normalData d) hn.certificate a.parameter a.parameter_mem
  have hpin := hdata.2.2.2.2.2.2
    (freeInv (d.period a.parameter) a.forcing) v G H hr i
  exact hpin.symm.trans (congrFun a.held.pins i)

end Breakdown.Theorem71
