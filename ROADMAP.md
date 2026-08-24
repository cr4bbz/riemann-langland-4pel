# Research roadmap

Each gate must end in a clean `lake build` and an updated formalization audit.

## Gate 0 — Reproducible foundation

- [x] Pin Lean 4 and Mathlib.
- [x] Define the project-facing statement.
- [x] Connect it to Mathlib's canonical `RiemannHypothesis`.
- [ ] Confirm the first GitHub Actions build.

## Gate 1 — Zero taxonomy

- [ ] Relate `IsTrivialZero` to Mathlib's trivial-zero theorem.
- [ ] Prove that a nontrivial zero is distinct from the pole.
- [ ] State the critical-strip localization theorem with an honest dependency status.

## Gate 2 — Symmetry package

- [ ] Package conjugation symmetry.
- [ ] Package the `s ↦ 1 - s` functional-equation symmetry.
- [ ] Derive the expected orbit of a nontrivial zero.
- [ ] Isolate precisely why symmetry does not imply the critical-line claim.

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
