# Credit and scope

The paper, its mathematics and the original Lean formalisation are by Levent Alpöge and Tristan Buckmaster. These added statements and bridge proofs were prepared by Will Cook with AI assistance; the Theorem 1.1 and Theorem 7.1 wrappers they build on come from this repository. The authors have not reviewed them.

None of the authors' Lean files is edited. Where the proof of a private helper lemma is needed to keep a chosen witness, it is copied into an added module in a fresh namespace; `support/theorem71/provenance.json` records where. No numerical certificate or interval-arithmetic verification is included: the certificate routes take the certificate conditions as hypotheses.
