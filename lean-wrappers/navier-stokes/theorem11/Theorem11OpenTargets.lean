import Theorem11Challenge

/-!
# Paper-faithful forms of Theorem 1.1 that are not yet derived

Each definition below is a proposition with no proof. Its docstring names the
ingredient that the authors' package at commit ad53419 does not supply and that
a proof would need. `Theorem11.theorem11Space` and
`Theorem11.theorem11SpaceBlowup` in `Theorem11Solution` are the forms that are
proved.
-/

namespace Theorem11.OpenTarget

/-- The torus part of Theorem 1.1 for a profile of the library's class (the
contract `Theorem11Torus`): there exist T in (0,1], a smooth periodic
divergence-free datum and a smooth periodic solution on [0,T) × T³ with periodic
pressure which blows up at time T, with c (T-t)^(-1/4) ≤ ‖u(t)‖_{H¹(cell)} ≤
C (T-t)^(-1/4) and the error bound on the ball B_{1/16}.

Missing ingredient: regularity on the torus. The package proves that a smooth
periodic solution is a mild solution in its periodic Fourier space
(`SmoothPeriodicIsMild`), and constructs a periodic mild trajectory that blows
up (`Breakdown.Theorem11.Torus.torus_mild_blowup_of_profile` in this wrapper).
It has no periodic analogue of `Breakdown.MildRegular`: no theorem that a
periodic mild trajectory from smooth periodic data is represented, on each
[0,T'] with T' < T, by a smooth periodic velocity and a smooth periodic
pressure solving the equations. Without it there is no physical solution to
which the norm rates can be transferred. -/
def Torus : Prop := Theorem11Torus

/-- Theorem 1.1 on R³ with the printed hypothesis (the contract
`PaperTheorem11Space`): the profile satisfies (1.2) and the two bounds (1.3)
only, |W| ≤ C_W (1+|y|)^(-1) and |∇W| ≤ C_W (1+|y|)^(-2), and the error is
measured in the original variables against the field (1.4),
‖∇(u(t) - u*_1(t))‖_{L²} ≤ C (1-t)^(κ-1/4).

Missing ingredients: (i) Remark 1.2 in Lean, that is the interior estimate for
bounded smooth solutions that upgrades the printed bounds to the bounds on
∇²W and on the pressure gradient that the library's profile class
(`IsLibraryProfile`) assumes; (ii) the change of variables taking the error
bound in self-similar variables, which `theorem11Space` proves, to the error in
the original variables, for fields that are only smooth with square integrable
gradient (the wrapper's dilation identity `gradientNorm_dilate` is stated for
the library's decay fields). -/
def PaperSpace : Prop := PaperTheorem11Space

/-- The torus part of Theorem 1.1 with the printed hypothesis (the contract
`PaperTheorem11Torus`).

Missing ingredients: both the torus regularity described at `Torus` and the
upgrade of the printed profile bounds described at `PaperSpace` (i). -/
def PaperTorus : Prop := PaperTheorem11Torus

end Theorem11.OpenTarget
