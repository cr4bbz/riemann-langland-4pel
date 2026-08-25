# Bridge audit

## Purpose

This audit asks a stricter question than whether two descriptions of RH sound related:

> Are both propositions formalized, and does Lean check translations in both directions?

`RiemannHypothesisLean.BridgeAudit` represents a proposition as a `Formulation` node and a
two-way translation as an `ExactBridge`. An exact bridge contains both implication proofs.
Shared terminology, matching diagrams, or a conjectured correspondence do not create an edge.

## Status vocabulary

| Status | Meaning |
|---|---|
| checked node | The proposition and all objects appearing in it are defined in the project/imports |
| checked bridge | Lean has accepted both implication proofs |
| conditional bridge | Lean has accepted the translation assuming an explicit named obligation |
| not formalized | No project node is created because essential mathematical objects are absent |

## Node inventory

| Family | Formulation | Lean node | Status |
|---|---|---|---|
| analytic | canonical zeta zero-location RH | `analyticStatementFormulation` | checked node |
| analytic | left-half critical-strip zero-free | `analyticLeftHalfZeroFreeFormulation` | checked node |
| analytic | right-half critical-strip zero-free | `analyticRightHalfZeroFreeFormulation` | checked node |
| geometric | every nontrivial zero fixed by `s ↦ 1 - conj(s)` | `geometricDualFixedFormulation` | checked node |
| analytic | critical-strip criterion for a supplied eta function | `analyticEtaFormulation eta` | checked parameterized node |
| analytic | concrete factorized Dirichlet eta criterion | `analyticEtaFormulation dirichletEta` | checked concrete node |
| spectral | Hilbert–Pólya-style operator realization | none | not formalized |
| positivity | Weil/Li-style positivity criterion | none | not formalized |

The spectral row is not a proposition yet: no operator, domain, self-adjointness proof, spectral
encoding, or zero-spectrum correspondence has been selected. The positivity row likewise lacks a
formal test-function space, functional, convergence conditions, and exact sign criterion. Giving
either row an arbitrary `Prop` placeholder would make the graph look denser without adding
mathematical content, so the repository does not do that.

## Checked translation graph

| Source | Target | Lean declaration | Status |
|---|---|---|---|
| canonical analytic RH | dual-symmetry fixed points | `statement_dualFixed_exactBridge` | checked bridge |
| canonical analytic RH | left-half zero-free | `statement_leftHalfZeroFree_exactBridge` | checked bridge |
| canonical analytic RH | right-half zero-free | `statement_rightHalfZeroFree_exactBridge` | checked bridge |
| dual-symmetry fixed points | left-half zero-free | `dualFixed_leftHalfZeroFree_exactBridge` | checked by composition |
| canonical analytic RH | supplied eta criterion | `statement_eta_exactBridge` | conditional bridge |
| canonical analytic RH | concrete Dirichlet eta criterion | `statement_dirichletEta_exactBridge` | checked bridge |

`ExactBridge.refl`, `ExactBridge.symm`, and `ExactBridge.trans` check the identity, reversal,
and composition operations used to navigate the graph.

## Closed concrete eta bridge

Gate 7 supplies a concrete function `dirichletEta : ℂ → ℂ`. Away from `s = 1` it is defined
by

```lean
dirichletEtaFactor s * riemannZeta s
```

with `dirichletEtaFactor s = 1 - 2 ^ (1 - s)`; at the removable point `s = 1` it is assigned
the standard value `log 2`.

The former open obligation is now discharged by
`dirichletEta_zetaZeroCompatible`. The key theorem
`dirichletEtaFactor_ne_zero_of_inCriticalStrip` proves that the factor cannot vanish when
`0 < re(s) < 1`: the norm of `2 ^ (1 - s)` is strictly greater than one there.

Consequently:

- `statement_dirichletEta_exactBridge` is unconditional;
- `statement_iff_dirichletEtaCriticalStripCriterion` is checked in both directions;
- the generic conditional bridge remains useful for other eta implementations.

This closes an interoperability edge, not RH. The eta criterion is equivalent to the same open
zero-location statement.

## Current frontier

There is no longer an unresolved edge among the concrete analytic and geometric nodes in the
current graph. Gate 8 has now begun the independent eta alternative: period-two coefficient data,
the naive `LSeries`, and its `ZMod.LFunction` continuation are formalized, and their equality is
checked on `1 < re(s)`. The coefficient mean is proved zero, so the independent continuation is
entire. Explicit natural-order real partial sums now converge for every real exponent `x > 0`.
The complex partial sums are defined independently and agree with those real sums on the embedded
real axis. Even complex partial sums are now exactly rewritten as finite sums of the pairs
`(2n+1)^(-s) - (2n+2)^(-s)`. The real-variable kernel `t ↦ t^(-s)`, its derivative, and the
exact derivative norm on positive inputs are also checked. The mean-value inequality now supplies
the pointwise estimate `‖pair(s,n)‖ ≤ ‖s‖(2n+1)^(-re(s)-1)` for `0 < re(s)`.
Comparison with the odd-index subsequence of a p-series now proves summability of these norms and
absolute summability of the paired complex series. The paired partial sums and, by the exact finite
pairing identity, the even natural-order eta partial sums converge to the paired-series sum. The
unpaired term is now checked to vanish, and the odd partial sums converge to that same value. A
general parity lemma combines the two subsequences, so the full natural-order alternating eta
partial sums converge for every `s` with `0 < re(s)`. Their common limit is now named through
the absolutely summable paired series. On `1 < re(s)`, an exact finite identity compares a
cofinal family of Mathlib `LSeries` partial sums with the paired partial sums; uniqueness of limits
therefore identifies the natural value with both the naive `LSeries` and the independent periodic
continuation. Splitting the absolutely summable shifted zeta series into odd and even denominators
also proves the classical factorization on that half-plane. The identity theorem on
`ℂ \\ {1}` first identifies the independent periodic continuation with the factorized
`dirichletEta` away from one. The eta-factor derivative at one and the zeta residue then give the
product limit `log 2`; continuity of the entire periodic continuation closes the removable point.
The independent periodic continuation is therefore globally equal to Gate 7 `dirichletEta`.
Harmonic-number asymptotics and an exact finite partial-sum identity also prove independently that
the natural alternating harmonic series has value `log 2`, closing the series/continuation edge at
one. The remaining series-level edge is equality of the conditionally convergent natural value
with that continuation on `0 < re(s) ≤ 1` away from one. A classical positivity criterion
remains a separate future expansion family.

## Availability findings

The pinned Mathlib surface supplies `riemannZeta`, its functional equation, critical
nonvanishing results, zero discreteness, and the canonical `RiemannHypothesis` proposition. The
Mathlib formalization report explicitly notes an earlier Lean Dirichlet-eta formulation and
identifies equivalence with Mathlib's formulation as useful future work. Gate 7 closes the
project-level zero-set bridge for the concrete factorized eta definition above. It does not import
or identify this definition with every object from the earlier standalone formalization.

No spectral or classical positivity criterion is imported into the present project. These
families remain audit categories, not theorem nodes. Gate 5 therefore does not pretend that the
current graph spans all four families.

## Consequence for the later 4PEL layer

The graph already distinguishes:

- theorem-backed nodes;
- theorem-backed bidirectional edges;
- explicit unresolved obligations; and
- informal candidate families with missing objects.

This distinction can be represented in ordinary Lean without a four-valued logic. Gate 6 tested
a minimal bilateral four-value layer and proved that its classifier adds no information beyond the
two support channels from which it is computed. Accordingly, no 4PEL labels are attached to this
graph unless a richer rule-governed proposal first passes the documented small-case novelty test.

## Sources

- [Pinned Mathlib zeta-zero source](https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/NumberTheory/LSeries/ZetaZeros.lean)
- [Mathlib Riemann zeta documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/RiemannZeta.html)
- [Formalizing zeta and L-functions in Lean](https://arxiv.org/abs/2503.00959)
- [Gomes–Kontorovich Dirichlet-eta formalization](https://github.com/bhgomes/lean-riemann-hypothesis)
