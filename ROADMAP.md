# Research roadmap

Each gate must end in a clean `lake build` and an updated formalization audit.

## Gate 0 — Reproducible foundation

- [x] Pin Lean 4 and Mathlib.
- [x] Define the project-facing statement.
- [x] Connect it to Mathlib's canonical `RiemannHypothesis`.
- [x] Confirm the first GitHub Actions build.

## Gate 1 — Zero taxonomy

- [x] Relate `IsTrivialZero` to Mathlib's trivial-zero theorem (forward direction).
- [x] Prove that a nontrivial zero is distinct from the pole and from zero.
- [x] Derive `re(s) < 1` from Mathlib's nonvanishing theorem.
- [x] Classify zeros of `Gammaℝ` against the project trivial-zero predicate.
- [x] Reflect a hypothetical zero with `re(s) ≤ 0` into the zero-free half-plane.
- [x] Prove `0 < re(s)` for every nontrivial zero.
- [x] Prove full critical-strip localization `0 < re(s) < 1`.

## Gate 2 — Symmetry package

- [x] Define the conjugation and reflection transformations as involutions.
- [x] Package the `s ↦ 1 - s` symmetry for completed-zeta zeros.
- [x] Record totalized all-input conjugation as an explicit stronger proposition.
- [x] Prove ordinary-zeta reflection for zeros already in the critical strip.
- [x] Prove ordinary-zeta conjugation compatibility on `1 < re(s)` from the Dirichlet series.
- [x] Extend conjugation compatibility to `ℂ \ {1}` by analytic continuation.
- [x] Remove the conjugation hypothesis from the nontrivial-zero orbit.
- [x] Derive the four-point orbit unconditionally for every nontrivial zero.
- [x] Isolate precisely why setwise symmetry does not imply the critical-line claim.
- [x] Reformulate RH as pointwise fixation under `s ↦ 1 - conj(s)`.

## Gate 3 — Finiteness and computation boundary

- [x] Define the project-level nontrivial-zero set.
- [x] Transfer discreteness from Mathlib's full zeta-zero set.
- [x] Prove that compact regions contain finitely many nontrivial zeros.
- [x] Separate verification inside a region from global coverage.
- [x] Prove that regional verification entails RH only under explicit coverage.
- [x] Exhibit vacuous verification on the empty region.
- [x] Keep finite or numerical evidence separate from the universal proposition.

## Gate 4 — Equivalent criteria

- [x] Select the zero-free open left half of the critical strip as an RH-equivalent criterion.
- [x] Prove that the dual symmetry preserves project-level nontrivial zeros.
- [x] Formalize the left- and right-half zero-free criteria.
- [x] Prove both implications between RH and each one-sided criterion.
- [x] Prove the two one-sided criteria equivalent through the checked symmetry.
- [x] Document that these reductions do not prove either criterion.

## Gate 5 — Bridge audit

- [ ] Compare analytic, spectral, geometric, and positivity formulations.
- [ ] Record exact translation theorems rather than informal analogies.
- [ ] Identify the smallest currently unproved bridge statement.

The roadmap does not assume that completing these gates yields a proof of RH.

## Gate 6 — 4PEL feasibility test

- [ ] Define positive and negative derivability relative to an explicit theory context.
- [ ] Define translations that preserve each support channel separately.
- [ ] Test the framework on a small proved correspondence before applying it to RH-scale material.
- [ ] State a falsifiable criterion for whether the 4PEL layer adds information beyond provenance
      tracking and ordinary many-sorted metatheory.
