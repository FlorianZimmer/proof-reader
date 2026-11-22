import Theorem71Keep

open MeasureTheory Filter
open scoped ContDiff ENNReal Topology
noncomputable section
namespace NavierStokes.Internal
open Breakdown Breakdown.Cert Breakdown.Freq

/-- The proved analytic ingredients needed in Section 7, with no analytic assumption
left for the caller. Each field is obtained from the authors' unchanged proofs. -/
structure SectionSevenNodes : Prop where
  zeroHeld : ExtendedExistsZeroHeldHolds
  sliceReading : SliceReadingHolds
  weakEquation : ExtendedHeldWeakEquationHolds
  nonzero : ExtendedHeldNonzeroHolds
  readingEnergy : ReadingEnergyHolds
  freePerturbation : FreePerturbationHolds
  data : ExtendedDataHolds
  projection : ProjectionHolds
  graph : GraphClosedHolds
  propagator : PropagatorBoundHolds
  gradientInverse : GradInvHolds
  freeInverse : FreeInvHolds
  localEnergy : FreeEnergyLocalHolds
  equivariance : FreeEquivariantHolds
  compactness : LocalCompactnessHolds
  periodContinuity : PeriodContinuityHolds
  spatialBound : SliceSupBoundHolds
  product : ProductBoundHolds
  convection : ExtendedConvectionHolds
  invariance : ExtendedInvarianceHolds
  convectionCompact : ExtendedConvectionCompactHolds
  borderedInverse : ExtendedBorderedInvertibleHolds
  supremumBound : ExtendedSupBoundHolds

/-- Reassemble the authors' dependency chain and retain the analytic results used
by the numbered statements. No field of this record is an additional hypothesis. -/
theorem sectionSevenNodes : SectionSevenNodes := by
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
      data := data
      projection := proj
      graph := graph
      propagator := prop
      gradientInverse := gradInvProof
      freeInverse := free
      localEnergy := localEnergy
      equivariance := equiv
      compactness := compact
      periodContinuity := periodContinuityHolds_of free
      spatialBound := sliceSupBoundHolds_of graph
      product := product
      convection := convection
      invariance := invariance
      convectionCompact := extendedConvectionCompactHolds_of compact convection free
      borderedInverse := inverse
      supremumBound := sup }


end NavierStokes.Internal
