import Theorem11Challenge

/-!
Negative control for Comparator: the same endpoint name with a weakened
conclusion, the slab-wise `Theorem11SpaceLocal` (a solution on each [0,T),
T < 1, with no single solution, no uniform energy bound and no rates).
Comparator must reject this pair with a statement mismatch.
-/

namespace Theorem11

theorem theorem11Space : Theorem11SpaceLocal := by
  sorry

end Theorem11
