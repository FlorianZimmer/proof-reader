import CellLayerChallenge
import DumpSupport

-- Diagnostic only. Do not import this beside ProbeLibrary.
set_option pp.all true
set_option pp.proofs true
set_option pp.universes true
set_option pp.explicit true

#print Breakdown.AdjointDefect.transposeApply
#synth Inner ℝ Breakdown.Space
#synth SMul ℝ Breakdown.Space
#synth Fintype (Fin 3)

noncomputable section
open Breakdown
namespace AuditTranspose

def intended (K : Space →L[ℝ] Space) (z : Space) : Space :=
  ∑ i : Fin 3, _root_.inner ℝ (K (_root_.Breakdown.unitVector i)) z • _root_.Breakdown.unitVector i

-- This tests definitional equality within this one environment, not cross-environment meaning.
-- No success is claimed until this file is run in the complete pinned environment.
example (K : Space →L[ℝ] Space) (z : Space) :
    Breakdown.AdjointDefect.transposeApply K z = intended K z := by
  rfl

end AuditTranspose

#dump_audit "transpose_names.txt"
