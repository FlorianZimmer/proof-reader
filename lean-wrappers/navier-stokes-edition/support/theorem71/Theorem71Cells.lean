import Theorem71Statements
import Breakdown.CertTorus.CertificateCorollary

/-!
# Cell-layer adapters for the physical Theorem 7.1 statement

Status: NOT COMPILED.
The final adapter takes a proof of `Theorem71Extended`; the closed cell result
in `Theorem71Solution` supplies that proof. The source certificate constructor
may enlarge `decay`, which leaves the requested output unchanged.
-/

open Breakdown.CertCell

namespace Breakdown.Theorem71

/-- The complete Appendix B cell conditions give a formal extended certificate, with its permitted enlarged decay constant. -/
theorem cell_extendedCertificate {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : CellLayerData k C nE nM)
    (X : Instance.InstanceData k C nE nM)
    (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R)
    (Y : CellLayerEntries D R T) (N : CellLayerSystem.CoerciveNumbers)
    (B : CellLayerSystem.ReductionEntries k)
    (h : CellLayerSystem.CellSystemCondition D X R T Y N B) :
    ∃ b : ℝ, IsExtendedCertificate ({D.cert with decay := b} : ExtendedCertificateData k) := by
  exact CellLayerSystem.isExtendedCertificate_of_parts
    (CellReduction.Instantiation.instantiation_holds_of_open
      CellReduction.Instantiation.stepPhase_holds
      CellReduction.Instantiation.movedFieldJointSmooth_holds
      CellReduction.Instantiation.movedFieldUniformDecay_holds
      CellReduction.Instantiation.pinValueContinuous_holds
      CellReduction.Instantiation.pressureFieldRegular_holds)
    (CellReduction.Instantiation.offsetClause_holds_of
      CellReduction.Instantiation.stepPhase_holds
      CellReduction.Instantiation.pressureFieldRegular_holds
      CellReduction.Instantiation.offsetBallIdentity_holds)
    CertReduction.gapTransferBridgeHolds_proof
    CertReduction.formShiftBridgeHolds_proof
    (CertReduction.frozenFormBridgeHolds_of_convection
      CertReduction.convectionIdentity_holds)
    (CertReduction.adjointQuadraticBridge_of
      (CertReduction.adjointQuadTerm_of CertReduction.matrixFacts
        CertReduction.perturbationSliceHolds CertReduction.energyBoundsHolds_proof
        CertReduction.cubicWeightProductHolds CertReduction.periodGlue)
      CertReduction.periodGlue)
    (AdjointDefect.adjointDefectBridge_of_pieces
      (AdjointDefect.representationHolds_of_density AdjointDefect.testFieldDensityHolds_proof)
      AdjointDefect.potentialBoundHolds_proof
      (AdjointDefect.dualBoundedBound_of_parts
        AdjointDefect.remainderPlainHolds_proof AdjointDefect.remainderAzimuthalHolds_proof)
      AdjointDefect.pinChargeHolds_proof AdjointDefect.freeShiftBoundHolds_proof)
    (CellReduction.Instantiation.adjointStructure_holds_of
      (CellReduction.Instantiation.adjointField_holds_of
        CellReduction.Instantiation.fieldDecayOrder_holds
        CellReduction.Instantiation.fieldPotential_holds
        CellReduction.Instantiation.classicalDivergenceWeak_holds)
      (CellReduction.Instantiation.profilePiecesFlow_of
        CellReduction.Instantiation.stepPhase_holds
        CellReduction.Instantiation.movedFieldUniformDecay_holds))
    CertReduction.smoothShiftPiecesHolds
    PotentialShape.potentialParts_holds h

/-- The cell conditions identify the correction pin targets with the certificate's target gaps. -/
theorem cell_targetGap_zero {k : ℕ} {C : Type} {nE nM : ℕ}
    {D : CellLayerData k C nE nM}
    {X : Instance.InstanceData k C nE nM}
    {R : CellCalculus.CellCalculusEntry D} {T : TreeEntry D R}
    {Y : CellLayerEntries D R T} {N : CellLayerSystem.CoerciveNumbers}
    {B : CellLayerSystem.ReductionEntries k}
    (h : CellLayerSystem.CellSystemCondition D X R T Y N B)
    (α : Fin k → ℝ) (i : Fin k) : D.cert.targetGap α i = 0 := by
  unfold ExtendedCertificateData.targetGap
  rw [h.instantiation.1.target_eq α i]
  exact sub_self _

/-- A full extended wrapper immediately gives the same chosen profile and
the same error bounds for a cell-system certificate. -/
theorem cell_conclusion_of_extended (h71 : Theorem71Extended)
    {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : CellLayerData k C nE nM)
    (X : Instance.InstanceData k C nE nM)
    (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R)
    (Y : CellLayerEntries D R T) (N : CellLayerSystem.CoerciveNumbers)
    (B : CellLayerSystem.ReductionEntries k)
    (h : CellLayerSystem.CellSystemCondition D X R T Y N B) :
    ExtendedConclusion D.cert := by
  obtain ⟨b, hb⟩ := cell_extendedCertificate D X R T Y N B h
  exact (extendedConclusion_decay_update D.cert b).mp (h71 _ hb)

end Breakdown.Theorem71
