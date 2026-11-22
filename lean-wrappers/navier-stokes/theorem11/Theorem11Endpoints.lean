import Theorem11Challenge

/-!
Comparator challenge for the global form of Theorem 1.1 on R³.

This file imports only `Theorem11Challenge`, which imports only Mathlib. It
states the two endpoints with `sorry`; the proofs are in `Theorem11Solution`,
which does not import this file. Comparator checks that the two statements
agree and that the proofs use only the permitted axioms.
-/

namespace Theorem11

/-- Theorem 1.1 on R³ with one finite-energy solution on [0,1), conditional on
the profile premise `IsLibraryProfile` (smooth nonzero periodic profile with
|∇ʲW| ≤ A(1+|y|)^-(j+1), j ≤ 2, and |∇q| ≤ A(1+|y|)^-3). -/
theorem theorem11Space : Theorem11Space := by
  sorry

/-- `theorem11Space` together with uniqueness and no smooth finite-energy
continuation to [0,1], under the same profile premise. -/
theorem theorem11SpaceBlowup : Theorem11SpaceBlowup := by
  sorry

end Theorem11
