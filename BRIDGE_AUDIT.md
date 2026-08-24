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

`ExactBridge.refl`, `ExactBridge.symm`, and `ExactBridge.trans` check the identity, reversal,
and composition operations used to navigate the graph.

## Smallest explicit open bridge

For a concrete function `eta : ℂ → ℂ`, the remaining obligation is:

```lean
EtaZetaZeroCompatibleOnCriticalStrip eta :=
  ∀ s : ℂ, InCriticalStrip s →
    (eta s = 0 ↔ riemannZeta s = 0)
```

Once this is supplied, `statement_eta_exactBridge` checks both downstream translations. This
isolates the interoperability work from RH itself:

1. define the intended Dirichlet eta function in the current Lean/Mathlib environment;
2. prove its zeros agree with Mathlib's zeta zeros on `0 < re(s) < 1`;
3. instantiate the already checked exact bridge.

The obligation is deliberately zero-set compatibility rather than global function equality. It is
the smallest statement used by the criterion translation.

## Availability findings

The pinned Mathlib surface supplies `riemannZeta`, its functional equation, critical
nonvanishing results, zero discreteness, and the canonical `RiemannHypothesis` proposition. The
Mathlib formalization report explicitly notes an earlier Lean Dirichlet-eta formulation and says
that proving its equivalence with Mathlib's formulation would be a useful future formalization.
That documented interoperability gap motivates the conditional eta bridge above.

No spectral or classical positivity criterion is imported into the present project. These
families remain audit categories, not theorem nodes. Gate 5 therefore does not pretend that the
current graph spans all four families.

## Consequence for the later 4PEL layer

The graph already distinguishes:

- theorem-backed nodes;
- theorem-backed bidirectional edges;
- explicit unresolved obligations; and
- informal candidate families with missing objects.

This distinction can be represented in ordinary Lean without a four-valued logic. Gate 6 must
therefore demonstrate something additional—such as separate, compositional support channels—on a
small checked correspondence before applying 4PEL terminology to the RH graph.

## Sources

- [Pinned Mathlib zeta-zero source](https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/NumberTheory/LSeries/ZetaZeros.lean)
- [Mathlib Riemann zeta documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/RiemannZeta.html)
- [Formalizing zeta and L-functions in Lean](https://arxiv.org/abs/2503.00959)
- [Gomes–Kontorovich Dirichlet-eta formalization](https://github.com/bhgomes/lean-riemann-hypothesis)
