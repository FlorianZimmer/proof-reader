/-
New adapter using the authors' named declarations, with no copied proof bodies.
Validation: NOT COMPILED in the return-producing environment.

This exports the mild-trajectory existence result that the public torus
breakdown theorem uses internally. It does NOT claim a smooth physical
solution, a two-sided norm rate, or the paper's local convergence estimate.
-/
import Breakdown.Torus.Main

noncomputable section

namespace Breakdown.Theorem11.Torus

open Breakdown.Periodic

/-- Stronger than a pure nonexistence conclusion: an actual unbounded mild
trajectory in the unit-period Fourier H¹ space, from smooth periodic data.
Its blow-up time is existential; its velocity is V-valued, not yet physical. -/
theorem torus_mild_blowup_of_profile (hP : PeriodicSimilarityProfileExists) :
    TorusBlowup := by
  apply torusBlowup_of_parts Freq.realization isFreqTrRealization
  · exact embeddedProfileOrbit_holds
  · exact orbitNorm
  · exact orbitBound
  · exact profilePiece
  · exact Freq.testDense_holds.2
  · exact Freq.testSpan_holds
  · exact baseInverse (stepData dichotomyHolds) seqOpSpec
  · exact r3ChainEq
      (r3Factor Freq.bilinTestFormula_holds Freq.velocityDecay_holds Freq.partial_holds.1)
      r3LambdaBound_holds seqOpSpec pieceCompSpec pieceConvSpec pieceOperator
      (heatDivFree_continuousOn Freq.fieldOpRealized_holds)
  · exact torusChainEq
      (torusFactor torusSeriesSmooth transplantSmooth (freqTrSeriesSpec coefDeriv))
      torusLambdaBound_holds seqOpSpec pieceCompSpec pieceConvSpec pieceOperator
  · exact opDiffBounds seqOpSpec pieceOperator
  · exact operatorNormBounds_holds
  · exact testLiftExists Freq.testSpan_holds Freq.embedNormLinear_holds.2
  · exact torusLiftExists toVAdd transplantSmooth
  · exact comparisonSmall
      (heatDivFreeComparison Freq.fieldOpRealized_holds (Freq.freqTrL1L2).1
        (Freq.freqTrConjSym Freq.fieldOpRealized_holds) Freq.velocityInverts_holds
        (Freq.freqTrL1L2).2)
      (freeHeatComparison coefDeriv transplantSmooth Freq.fieldOpRealized_holds
        Freq.heat_holds Freq.velocityInverts_holds (Freq.freqTrL1L2).2
        (Freq.freqTrL1L2).1 (Freq.freqTrConjSym Freq.fieldOpRealized_holds))
      r3LambdaBound_holds torusLambdaBound_holds
      (restrictR3Bound Freq.velocity_holds Freq.partial_holds.2)
      (transplantNorm transplantSmooth) seqOpSpec pieceConvSpec pieceCompSpec
      operatorNormBounds_holds pieceOperator Freq.fieldOpRealized_holds
      Freq.heat_holds Freq.dilation_holds Freq.velocityCov_holds.2
      Freq.gradSixDecay Freq.embedNormLinear_holds.1
      (Freq.embedDilate Freq.fieldOpRealized_holds Freq.dilation_holds Freq.embedMem_holds)
  · exact approxLinks_holds
  · exact approxResidualSmall approxFieldProperties_holds
      (approxResidualBound selfSimilarSolves homotopyCurl approxFieldProperties_holds)
      approxLinks_holds transplantSmooth
  · exact approxClose (transplantNorm transplantSmooth) transplantSmooth
      approxFieldProperties_holds approxLinks_holds Freq.embedNormLinear_holds.1
      Freq.embedNormLinear_holds.2
      (Freq.embedDilate Freq.fieldOpRealized_holds Freq.dilation_holds Freq.embedMem_holds)
      profilePiece Freq.dilation_holds Freq.dilationCont_holds
      sliceGradientContinuous_holds Freq.gradSixDecay
  · exact approxSizes (transplantNorm transplantSmooth) approxFieldProperties_holds
      approxLinks_holds Freq.embedNormLinear_holds.1 Freq.embedNormLinear_holds.2
  · exact datumClose (transplantNorm transplantSmooth) transplantSmooth
      approxFieldProperties_holds approxLinks_holds Freq.embedNormLinear_holds.1
      Freq.embedNormLinear_holds.2 toVAdd
  · exact toVAdd
  · exact approximantExists Freq.testDense_holds.2 Freq.testSpan_holds
      (Freq.embedRot Freq.fieldOpRealized_holds Freq.rotation_holds
        Freq.embedMem_holds Freq.gradCompatible)
      Freq.embedNormLinear_holds.2 Freq.rotation_holds profilePiece
  · exact transplantSmooth
  · exact seqPerturbation pieceOperator varConstIntegral
  · exact glueMild restrict concat shift varConstIntegral
  · exact glueUnbounded
  · exact rightInversePerturb
  · exact shellInverseTransfer rightInversePerturb
  · exact seqOpSpec
  · exact hP

#print axioms Breakdown.Theorem11.Torus.torus_mild_blowup_of_profile

end Breakdown.Theorem11.Torus
