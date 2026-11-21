import Theorem11Challenge

/-!
Comparator challenge for the global form of Theorem 1.1 on R³.

This file imports only `Theorem11Challenge`, which imports only Mathlib. It
states the two endpoints with `sorry`; the proofs are in `Theorem11Solution`,
which does not import this file. Comparator checks that the two statements
agree and that the proofs use only the permitted axioms.
-/

namespace Theorem11

theorem theorem11Space : Theorem11Space := by
  sorry

theorem theorem11SpaceBlowup : Theorem11SpaceBlowup := by
  sorry

end Theorem11
