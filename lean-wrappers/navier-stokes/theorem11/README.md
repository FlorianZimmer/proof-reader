# Theorem 1.1 wrapper: one finite-energy solution on [0,1), from the profile premise

Lean modules that state Theorem 1.1 of Alpöge and Buckmaster in physical terms
and prove its R³ part from their package at commit `ad53419`. Every proved
statement here is **conditional on the profile premise** of the authors' route.

## The premise

`IsLibraryProfile W q P R A` (in `Theorem11Challenge.lean`, Mathlib only): a
smooth pair (W, q) on ℝ × R³, not identically zero, that solves the profile
equations (1.2) (the similarity residual vanishes and div W = 0), is periodic
up to a linear isometry R with period P > 0, W(s+P, y) = R W(s, R⁻¹y), and
satisfies

- ‖∇ʲW(s,y)‖ ≤ A (1+|y|)^-(j+1) for j = 0, 1, 2, and
- |∇q(s,y)| ≤ A (1+|y|)^-3.

This is the premise the authors' Lean route uses (`Breakdown.IsSimilarityProfile`
with the periodicity and nonvanishing of `PeriodicSimilarityProfileExists`). It
is stronger than the hypothesis printed in the paper, which has only the bounds
(1.3) on W and ∇W; Remark 1.2 of the paper derives the rest, and that step is
not formalized (open target `Theorem11.OpenTarget.PaperSpace`).

## What is proved

`Theorem11.theorem11Space : Theorem11Space`. For every (W, q, P, R, A)
satisfying the premise and every ε > 0 there are a smooth, compactly supported,
divergence-free datum u₀ with ‖∇(u₀ − W(0))‖₂ < ε, one smooth solution (u, p)
of the Navier–Stokes equations with unit viscosity on [0,1) × R³ with datum
u₀, a bound E with ‖u(t)‖₂² ≤ E for all t in [0,1), and constants 0 < c ≤ C,
0 < κ < 1/4 such that for all t in [0,1)

- c (1−t)^(−1/4) ≤ ‖∇u(t)‖₂ ≤ C (1−t)^(−1/4), and
- ‖∇(√(1−t) u(t, √(1−t)·) − W(−log(1−t)))‖₂ ≤ C (1−t)^κ.

`Theorem11.theorem11SpaceBlowup : Theorem11SpaceBlowup` adds, under the same
premise: every smooth solution with datum u₀ and finite energy on an interval
[0,T), T ≤ 1, equals u there; and no smooth solution with datum u₀ and finite
energy exists on the closed interval [0,1].

The proof glues the library's slab solutions on [0,T], T < 1
(`Theorem11Glue.lean`: velocities by the library's uniqueness, pressures after
normalizing them to vanish at the origin), bounds the energy uniformly by the
datum's energy with a new energy inequality (`Theorem11Energy.lean`, the
authors' localized energy estimate run against the zero solution), and uses the
authors' `false_of_orbit_rate` for the last clause (`Theorem11Continuation.lean`).

## Checks

Run on GitHub Actions by `.github/workflows/navier-stokes-wrappers.yml`, which
fails unless all of the following hold:

- every module listed in the workflow compiles against the package
  (`DegenerateWitnessProbes` is an older probe file that is expected to fail);
- `#print axioms` for both endpoints shows only `propext`, `Classical.choice`
  and `Quot.sound`;
- Comparator (exports by `lean4export` under Lean 4.33.1, judged under Lean
  4.36.0 with Lean's paranoid kernel, con-leche, con-ron, nanoda and Lean's
  default kernel) accepts `comparator-theorem11.json` and
  `comparator-theorem11-blowup.json`, whose challenge `Theorem11Endpoints.lean`
  states the endpoints with `sorry` and imports only Mathlib-level statement
  definitions; and
- it rejects the control `comparator-theorem11-control.json`, whose challenge
  gives `Theorem11.theorem11Space` the weakened conclusion
  `Theorem11SpaceLocal` (a solution on each slab only), for a statement
  mismatch.

The run ids and verdicts are in the pull request that added these files and in
the Theorem 1.1 section of the Navier–Stokes paper page.

## Open targets

`Theorem11OpenTargets.lean` records, as propositions with no proof, the forms
not derived here and what each lacks:

- `OpenTarget.Torus` (the torus part, `Theorem11Torus`): the package has no
  periodic analogue of `Breakdown.MildRegular`, that is no theorem that a
  periodic mild trajectory from smooth data is a smooth periodic solution
  with smooth periodic pressure, so the torus rates cannot be moved to a
  physical solution.
- `OpenTarget.PaperSpace` (`PaperTheorem11Space`): the printed hypothesis
  (1.2)–(1.3) needs Remark 1.2 (the interior estimate giving the bounds on
  ∇²W and ∇q), and the printed error in the original variables,
  ‖∇(u(t) − u*_1(t))‖₂ ≤ C (1−t)^(κ−1/4), needs the change of variables from
  the self-similar bound for fields that are only smooth with square
  integrable gradient.
- `OpenTarget.PaperTorus` (`PaperTheorem11Torus`): both of the above.
