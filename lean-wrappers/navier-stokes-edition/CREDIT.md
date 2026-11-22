# Credit and scope

This is a new statement-layer return for packet N7, prepared by Will Cook with AI assistance. The paper, its original mathematics and the original Lean formalisation are by Levent Alpöge and Tristan Buckmaster. The supplied Theorem 1.1 and Theorem 7.1 wrappers originate in Will Cook’s proof-reader project.

The returned source adds statement definitions, proof reductions and bridge proofs. It does not edit any of the authors’ 2,271 Lean source files. Where proof bodies of private helper lemmas are needed for the retained witness, they are copied into added modules and fresh namespaces; those locations are documented in `support/theorem71/provenance.json` and `research/section_7.md`.

No claim of review or endorsement by the authors is made. No concrete numerical certificate or interval-arithmetic verification is included. A historical workflow success is not presented as validation of this return. Current checks and their limits are recorded in `checks/validation.json`.

The original uploaded ZIP is not redistributed in this return. The added files, the necessary supplied wrappers and the small reproducibility metadata are included.
