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

- [x] Classify analytic, spectral, geometric, and positivity formulation families.
- [x] Inventory which families currently have fully defined nodes.
- [x] Represent exact bridges by proofs in both directions.
- [x] Check analytic-to-geometric and analytic-to-analytic translations.
- [x] Make exact bridges reversible and composable.
- [x] Specify the eta/zeta zero-set compatibility obligation on the critical strip.
- [x] Prove the eta criterion exactly equivalent to RH under that explicit obligation.
- [x] Keep spectral and classical positivity rows unformalized until their objects are selected.
- [x] Record the eta/zeta compatibility as the smallest current interoperability bridge.

The roadmap does not assume that completing these gates yields a proof of RH.

## Gate 6 — 4PEL feasibility test

- [x] Define positive and negative derivability relative to an explicit bilateral theory context.
- [x] Derive gap, true-only, false-only, and glut from the two support channels.
- [x] Define translations that preserve and reflect each support channel separately.
- [x] Prove channel-preserving translations preserve the induced four-value classification.
- [x] Test all four profiles on a small cross-vocabulary correspondence.
- [x] Define a falsifiable criterion for information beyond the bilateral support profile.
- [x] Prove that the minimal four-value classifier fails that novelty criterion.
- [x] Keep the four-valued layer off the RH graph until a richer proposal passes a small-case test.

Gate 6 therefore has a mixed verdict: bilateral transport is feasible, but the minimal classifier
adds no information beyond the two channels from which it is computed. Any renewed 4PEL
integration must supply rule-governed structure and a nontrivial invariant, obstruction, or
consequence that survives exact translation.

## Gate 7 — Concrete Dirichlet eta interoperability

- [x] Define the eta factor `1 - 2 ^ (1 - s)`.
- [x] Define a concrete factorized Dirichlet eta function with the removable value at `s = 1`.
- [x] Prove points in the open critical strip are distinct from the pole location.
- [x] Prove the eta factor is nonzero throughout the open critical strip.
- [x] Prove eta and zeta have exactly the same zero predicate there.
- [x] Discharge `EtaZetaZeroCompatibleOnCriticalStrip dirichletEta`.
- [x] Instantiate the unconditional exact bridge to the eta RH criterion.
- [x] Keep alternating-series agreement and global analyticity outside the claimed Gate 7 surface.

Gate 7 closes the smallest interoperability obligation identified in Gate 5. It creates no proof
of either equivalent RH formulation.

## Gate 8 — Independent alternating eta series

- [x] Encode the eta signs by a function on residue classes modulo two.
- [x] Define the naive alternating Dirichlet series using Mathlib's `LSeries`.
- [x] Define an independent periodic continuation using `ZMod.LFunction`.
- [x] Prove summability on the absolute-convergence half-plane `1 < re(s)`.
- [x] Prove the periodic continuation equals the actual series there.
- [x] Record differentiability away from the possible pole location.
- [x] Prove the coefficient mean is zero and remove the possible pole at `s = 1`.
- [x] Define natural-order real eta partial sums separately from `Summable`.
- [x] Prove their sequential convergence for every positive real exponent.
- [x] Define the complex natural-order partial sums.
- [x] Prove real-axis agreement and transfer positive-real convergence to the complex codomain.
- [x] Define paired complex eta terms.
- [x] Prove every even natural-order partial sum equals the corresponding paired partial sum.
- [x] Define the real-variable complex power kernel used for paired-term estimates.
- [x] Prove its derivative and exact derivative norm on positive real inputs.
- [x] Prove the pointwise mean-value bound for each paired term when `0 < re(s)`.
- [x] Prove a summable norm bound for the paired terms when `0 < re(s)`. for the paired terms when `0 < re(s)`.
- [ ] Extend partial-sum convergence to arbitrary complex `s` with `0 < re(s)`.
- [ ] Identify the independent continuation with the factorized `dirichletEta`.
- [ ] Derive the value `log 2` at `s = 1` from the independent construction.

The completed items establish a genuinely independent construction on the safe convergence domain.
They do not yet identify its values with Gate 7 inside the critical strip.
