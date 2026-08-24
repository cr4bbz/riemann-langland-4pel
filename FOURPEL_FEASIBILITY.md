# 4PEL feasibility audit

## Question

Can a four-valued layer add mathematically useful information to the RH bridge graph, rather than
only renaming the two facts “positively supported” and “negatively supported”?

Gate 6 tests the smallest possible implementation before it is applied to any RH-scale statement.

## Formal objects

| Role | Lean declaration | Meaning |
|---|---|---|
| explicit theory context | `BilateralTheory Sentence` | supplies separate positive and negative derivability predicates |
| positive channel | `PositiveDerivable theory sentence` | positive support relative to the context |
| negative channel | `NegativeDerivable theory sentence` | negative support relative to the context |
| four profiles | `FourSupportValue` | gap, true-only, false-only, glut |
| classifier | `fourSupportValue` | computes the profile from the two channels |
| exact translation | `ExactSupportTranslation` | preserves and reflects each channel separately |
| novelty test | `AddsInformationBeyondSupportChannels` | asks whether an observation distinguishes equal bilateral profiles |

The theory context is intentionally only an interface. Gate 6 does not yet claim a complete 4PEL
syntax, proof calculus, semantics, soundness theorem, or completeness theorem.

## Four checked profiles

The finite source theory contains four sentences:

| Sentence | Positive | Negative | Checked value |
|---|---:|---:|---|
| `MiniSourceSentence.theorem` | yes | no | `trueOnly` |
| `MiniSourceSentence.refutation` | no | yes | `falseOnly` |
| `MiniSourceSentence.conflict` | yes | yes | `glut` |
| `MiniSourceSentence.undecided` | no | no | `gap` |

A second vocabulary uses `affirmed`, `denied`, `contested`, and `openQuestion`.
`miniExactSupportTranslation` proves that the mapping between the two vocabularies preserves and
reflects positive and negative derivability independently. The theorem
`miniTranslation_preserves_fourSupportValue` then proves preservation of the induced four-value
classification.

This is a successful feasibility result: gaps and gluts can be represented without explosion or
forced collapse, and an exact correspondence can transport both support channels separately.

## Falsifiable novelty criterion

For a theory and an additional observation, the current criterion asks for two sentences with:

1. equivalent positive derivability;
2. equivalent negative derivability; and
3. different values under the additional observation.

In Lean this is `AddsInformationBeyondSupportChannels theory observe`. A proposed enrichment can
therefore be tested by supplying a concrete `observe` and a witness pair.

Passing this test is necessary but not sufficient for a scientifically useful 4PEL layer. An
arbitrary label or stored provenance field could also distinguish two sentences. A convincing
future enrichment must additionally show that the observation is invariant under the intended
translations and affects a formally stated inference, obstruction, or bridge-stability theorem.

## Result

`fourSupportValue_not_addsInformation` proves for every bilateral theory:

```lean
¬AddsInformationBeyondSupportChannels theory (fourSupportValue theory)
```

The reason is exact, not empirical. If two sentences agree in both derivability channels, their
four-value classifications are definitionally forced to agree. The minimal classifier is therefore
a lossless presentation of a two-bit support profile, but it contains no further mathematical
information.

## Interpretation

The minimal 4PEL layer succeeds as:

- a vocabulary for gap and glut;
- a discipline for keeping positive and negative support separate;
- a transport contract across translations.

It does not yet succeed as:

- a source of new consequences;
- a method for closing an RH bridge;
- information beyond bilateral support bookkeeping;
- a replacement for missing analytic, spectral, or positivity theorems.

Accordingly, no four-valued status is attached to the RH formulation graph in Gate 6. Doing so now
would add labels but no theorem-producing structure.

## What would overturn the negative result?

A richer proposal can pass the next test by formalizing all of the following:

1. a syntax and rule-governed positive/negative derivability relation;
2. an additional structural observation or consequence relation;
3. preservation of that structure across exact translations;
4. two cases with the same bilateral support profile but a provably different structural outcome;
5. a proof that the difference is not merely an arbitrary annotation or provenance label.

Candidates include bridge-stability under composition, rule-sensitive obstruction certificates, or
proof-relevant support objects. These are research directions, not results claimed by this gate.

## Consequence for the project

The RH formalization and exact bridge graph remain useful independently of 4PEL. Gate 6 has
prevented the project from attaching a logically decorative layer to RH. Any renewed 4PEL
integration must first beat the checked bilateral baseline on a small non-RH example.
