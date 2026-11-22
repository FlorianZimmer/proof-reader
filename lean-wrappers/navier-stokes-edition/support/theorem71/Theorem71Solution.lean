/-
Status: NOT COMPILED. Target: Lean 4.33.1, authors ad53419 plus the supplied patch.
The physical definitions are in Theorem71Statements. The comparison modules
contain ordinary proofs, so the challenge needs no admitted theorem.
-/
import Theorem71Statements
import Theorem71Assembly
import Theorem71Cells

open Breakdown.CertCell

namespace Breakdown

/-- A formal extended certificate gives one selected parameter and a smooth identity-periodic profile with the correction bounds and prescribed symmetries of Theorem 7.1. -/
theorem theorem71_extended {k : ℕ} (d : ExtendedCertificateData k)
    (hd : IsExtendedCertificate d) : Theorem71.ExtendedConclusion d := by
  exact Theorem71.extended d hd

/-- Complete Appendix B cell conditions give the same retained parameter, profile, correction bounds and symmetries as the extended certificate theorem. -/
theorem theorem71_cell {k : ℕ} {C : Type} {nE nM : ℕ}
    (D : CellLayerData k C nE nM)
    (X : Instance.InstanceData k C nE nM)
    (R : CellCalculus.CellCalculusEntry D) (T : TreeEntry D R)
    (Y : CellLayerEntries D R T) (N : CellLayerSystem.CoerciveNumbers)
    (B : CellLayerSystem.ReductionEntries k)
    (h : CellLayerSystem.CellSystemCondition D X R T Y N B) :
    Theorem71.ExtendedConclusion D.cert := by
  exact Theorem71.cell_conclusion_of_extended Theorem71.extended D X R T Y N B h

end Breakdown
