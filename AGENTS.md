# Repository instructions

## Mathematical integrity

- Never claim that the Riemann hypothesis has been proved unless Lean checks a theorem of type
  `RiemannHypothesis` without additional hypotheses or project-defined axioms.
- Do not add `sorry`, `admit`, `axiom`, or `unsafe` as a shortcut.
- Keep conditional results visibly conditional.
- Distinguish a formalized statement, an equivalent reformulation, a partial theorem, numerical
  verification, and a proof.
- Keep the RH, correspondence, and 4PEL layers separated as specified in `SCOPE.md`.
- Do not label a translation “Langlands-like” as a mathematical result without a checked
  preservation or equivalence theorem.

## Required checks

Before a commit:

1. run `lake build`;
2. search project Lean files for forbidden proof placeholders;
3. update `FORMALIZATION.md` and `ROADMAP.md` when the checked surface changes;
4. ensure README status claims match the declarations in the committed tree.

## Dependency discipline

- Keep Lean and Mathlib pinned to matching versions.
- Prefer existing Mathlib definitions and theorems over parallel redefinitions.
- Any dependency upgrade is its own reviewed change and must rebuild from a clean cache.
