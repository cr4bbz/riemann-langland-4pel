# Research roadmap

Each gate must end in a clean `lake build` and an updated formalization audit.

## Gate 0 — Reproducible foundation

- [x] Pin Lean 4 and Mathlib.
- [x] Define the project-facing statement.
- [x] Connect it to Mathlib's canonical `RiemannHypothesis`.
- [x] Confirm the first GitHub Actions build.

## Gate 1 — Zero taxonomy

- [x] Relate `IsTrivialZero` to Mathlib's trivial-zero theorem (forward direction).
- [x] Prove that a nontrivial zero is distinct from the pole.
- [x] State critical-strip localization with an honest dependency status.
- [x] Derive `re(s) < 1` from Mathlib's nonvanishing theorem.
- [x] Reduce full localization to the still-unproved condition `0 < re(s)`.

## Gate 2 — Symmetry package

- [x] Define the conjugation and reflection transformations as involutions.
- [x] Package the `s ↦ 1 - s` symmetry for completed-zeta zeros.
- [x] Name ordinary-zeta conjugation compatibility as an explicit unproved bridge.
- [x] Prove conditional conjugation transport from that bridge.
- [x] Prove ordinary-zeta reflection for zeros already in the critical strip.
- [x] Derive the expected four-point zeta-zero orbit conditionally on the two remaining bridges.
- [x] Prove ordinary-zeta conjugation compatibility on `1 < re(s)` from the Dirichlet series.
- [ ] Extend ordinary-zeta conjugation compatibility through analytic continuation.
- [x] Isolate precisely why setwise symmetry does not imply the critical-line claim.
- [x] Reformulate RH as pointwise fixation under `s ↦ 1 - conj(s)`.

## Gate 3 — Finiteness and computation boundary

- [ ] Expose discreteness and compact finiteness through project-level lemmas.
- [ ] Specify what a certified finite zero check can and cannot establish.
- [ ] Keep computational evidence separate from the universal proposition.

## Gate 4 — Equivalent criteria

- [ ] Select one documented RH-equivalent criterion.
- [ ] Formalize all objects appearing in the criterion.
- [ ] Prove both implications, or label the missing direction explicitly.

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
