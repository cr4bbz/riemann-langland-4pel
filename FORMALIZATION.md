# Formalization boundary

## Exact target

For `s : ℂ`, the repository names:

- `IsTrivialZero s := ∃ n : ℕ, s = -2 * (n + 1)`;
- `IsNontrivialZero s := riemannZeta s = 0 ∧ ¬IsTrivialZero s ∧ s ≠ 1`;
- `OnCriticalLine s := s.re = 1 / 2`;
- `Statement := ∀ s, IsNontrivialZero s → OnCriticalLine s`.

`statement_iff_mathlib` checks that this target is equivalent to Mathlib's
`RiemannHypothesis` definition.

## What “fully formalize RH” means here

The initial objective is complete **specification**, not a claimed proof:

1. use Mathlib's actual analytic continuation of zeta;
2. state every exclusion and coercion explicitly;
3. connect the project statement to Mathlib's canonical statement;
4. inventory every imported result on zeros, poles, symmetry, and discreteness;
5. formalize proposed equivalent criteria only when both implications are checked.

## Present Mathlib surface at v4.30.0

| Mathematical object | Lean declaration | Status |
|---|---|---|
| Riemann zeta function | `riemannZeta` | imported |
| Functional equation | `riemannZeta_one_sub` | imported |
| Completed functional equation | `completedRiemannZeta_one_sub` | imported |
| Trivial zeros | `riemannZeta_neg_two_mul_nat_add_one` | imported |
| Nonvanishing on `1 ≤ re(s)` | `riemannZeta_ne_zero_of_one_le_re` | imported |
| Zero set | `riemannZetaZeros` | imported |
| Discreteness of zeros | `isDiscrete_riemannZetaZeros` | imported |
| Finitely many zeros in compact sets | `IsCompact.inter_riemannZetaZeros_finite` | imported |
| Riemann-hypothesis proposition | `RiemannHypothesis` | imported, unproved |
| Project equivalence | `statement_iff_mathlib` | checked in this repository |

## Gate 1: checked zero taxonomy

`RiemannHypothesisLean.ZeroTaxonomy` adds the following checked surface:

| Claim | Lean declaration | Status |
|---|---|---|
| Every named trivial zero is a zeta zero | `IsTrivialZero.riemannZeta_eq_zero` | checked |
| A nontrivial zero is not the pole location | `IsNontrivialZero.ne_one` | checked |
| A nontrivial zero is not zero | `IsNontrivialZero.ne_zero` | checked |
| The real Gamma factor is nonzero there | `IsNontrivialZero.Gammaℝ_ne_zero` | checked |
| A nontrivial zero satisfies `re(s) < 1` | `IsNontrivialZero.re_lt_one` | checked |
| A nontrivial zero satisfies `0 < re(s)` | `IsNontrivialZero.re_pos` | checked |
| Positive-real-part proposition | `positiveRealPartForNontrivialZeros` | checked |
| Full localization in `0 < re(s) < 1` | `criticalStripLocalization` | checked |
| Reduction of localization to left boundary | `criticalStripLocalization_iff_positiveRealPart` | checked |

For the left boundary, Mathlib's `Gammaℝ_eq_zero_iff` identifies the only obstruction to lifting
a zeta zero to the completed function. Those points are either `0` or the named trivial zeros.
The completed functional equation then reflects any remaining hypothetical zero with
`re(s) ≤ 0` to a zero with `re(1-s) ≥ 1`, contradicting Mathlib's nonvanishing theorem.

## Gate 2: symmetry boundary

`RiemannHypothesisLean.Symmetry` distinguishes transformations, zero transport, and fixed points:

| Claim | Lean declaration | Status |
|---|---|---|
| `s ↦ 1 - s` is an involution | `criticalReflection_involutive` | checked |
| `s ↦ conj(s)` is an involution | `conjugationPoint_involutive` | checked |
| `s ↦ 1 - conj(s)` is an involution | `dualSymmetry_involutive` | checked |
| Fixed points of the dual symmetry form the critical line | `dualSymmetry_fixed_iff_onCriticalLine` | checked |
| Completed-zeta zeros reflect under `s ↦ 1 - s` | `completedZetaZero_criticalReflection_iff` | checked |
| Totalized conjugation including `s = 1` | `RiemannZetaConjugationCompatibility` | stronger named proposition, not needed for RH |
| Transport from totalized compatibility | `riemannZeta_eq_zero_conjugationPoint` | checked conditionally |
| RH is pointwise fixation under the dual symmetry | `statement_iff_nontrivialZerosFixedByDualSymmetry` | checked reformulation |
| Setwise symmetry alone need not imply pointwise fixation | `setwiseDualInvariant_not_pointwiseFixed` | checked generic counterexample |

`RiemannHypothesisLean.Conjugation` closes the natural analytic-domain bridge:

| Claim | Lean declaration | Status |
|---|---|---|
| Zeta commutes with conjugation on `1 < re(s)` | `riemannZeta_conjugation_of_one_lt_re` | checked from the Dirichlet series |
| Zeta commutes with conjugation on `s ≠ 1` | `riemannZeta_conjugation_of_ne_one` | checked by the identity principle |
| Project-facing form on `s ≠ 1` | `riemannZeta_conjugationPoint_of_ne_one` | checked |
| Conjugation transports nontrivial zeros | `IsNontrivialZero.riemannZeta_conjugationPoint_eq_zero` | checked unconditionally |

The first proof moves conjugation through Mathlib's convergent `tsum` and checks every Dirichlet
term using conjugation of complex powers. The second proves analyticity of
`z ↦ conj (ζ (conj z))` and applies the identity principle on the connected set `ℂ \ {1}`.
The excluded point is the pole and cannot be a project-level nontrivial zero.

The completed functional equation therefore supplies a genuine checked transport theorem. Even
after setwise closure is established, RH would still require proving that every nontrivial zero is
individually fixed by the combined symmetry.

## Gate 2: zero-orbit reduction

`RiemannHypothesisLean.Orbit` connects the completed functional equation back to ordinary zeta:

| Claim | Lean declaration | Status |
|---|---|---|
| Positive-real-part zeta zeros are completed-zeta zeros | `completedZetaZero_of_riemannZetaZero_of_re_pos` | checked |
| Critical-strip zeta zeros reflect under `s ↦ 1 - s` | `riemannZetaZero_criticalReflection` | checked |
| The four orbit points are zeta zeros | `RiemannZetaZeroOrbit` | project structure |
| Localization yields the orbit | `riemannZetaZeroOrbit_of_localization` | checked |
| Positive real part yields the orbit | `riemannZetaZeroOrbit_of_positiveRealPart` | checked |
| Every nontrivial zero has the orbit | `IsNontrivialZero.riemannZetaZeroOrbit` | checked unconditionally |

Reflection, conjugation, and critical-strip localization are now all discharged for project-level
nontrivial zeros, so the full four-point orbit is checked without hypotheses. This orbit closure is
still only setwise information and does not imply the pointwise fixation equivalent to RH.

## Gate 3: finiteness and computation boundary

`RiemannHypothesisLean.Finiteness` transfers Mathlib's discrete-zero results and separates local
verification from global coverage:

| Claim | Lean declaration | Status |
|---|---|---|
| Project-level nontrivial-zero set | `nontrivialZeroSet` | defined |
| Inclusion in Mathlib's zero set | `nontrivialZeroSet_subset_riemannZetaZeros` | checked |
| Nontrivial zeros form a discrete set | `isDiscrete_nontrivialZeroSet` | checked |
| Compact regions contain finitely many nontrivial zeros | `IsCompact.inter_nontrivialZeroSet_finite` | checked |
| Critical-line verification inside a region | `VerifiedOnRegion` | defined |
| Global coverage by a region | `CompleteForNontrivialZeros` | defined separately |
| Proof-level compact check | `CertifiedCompactCheck` | project structure |
| RH implies every regional verification | `verifiedOnRegion_of_statement` | checked |
| Verification plus coverage implies RH | `statement_of_verifiedOnRegion_of_complete` | checked |
| Equivalence under explicit coverage | `statement_iff_verifiedOnRegion_of_complete` | checked |
| Empty-region verification is vacuous | `verifiedOnRegion_empty` | checked |

Compactness makes the in-region zero set finite, but does not prove that all nontrivial zeros lie
there. The completeness hypothesis is therefore a separate field of mathematical content, not
metadata that a numerical program may silently assume. No floating-point computation or finite
height cutoff is represented as evidence for the universal proposition.

## Gate 4: equivalent half-strip criteria

`RiemannHypothesisLean.EquivalentCriteria` turns the checked zero symmetry into two explicit
one-sided formulations:

| Claim | Lean declaration | Status |
|---|---|---|
| Positive real part excludes named trivial zeros | `not_isTrivialZero_of_re_pos` | checked |
| Dual symmetry preserves nontrivial zeros | `IsNontrivialZero.dualSymmetry_isNontrivialZero` | checked |
| No nontrivial zero lies left of the critical line | `LeftHalfCriticalStripZeroFree` | defined |
| No nontrivial zero lies right of the critical line | `RightHalfCriticalStripZeroFree` | defined |
| RH iff left-half zero-free | `statement_iff_leftHalfCriticalStripZeroFree` | both directions checked |
| RH iff right-half zero-free | `statement_iff_rightHalfCriticalStripZeroFree` | both directions checked |
| Left and right criteria are equivalent | `leftHalfCriticalStripZeroFree_iff_rightHalfCriticalStripZeroFree` | checked |

For the nontrivial direction, the one-sided bound is applied both to `s` and to the checked
nontrivial zero `1 - conj(s)`. Since their real parts add to `1`, the two inequalities force
`re(s) = 1 / 2`. This is an exact reduction, not evidence for the one-sided criterion itself:
proving either zero-free claim remains equivalent to proving RH.

## Gate 5: exact bridge audit

`RiemannHypothesisLean.BridgeAudit` distinguishes formulation families from actual proposition
nodes and requires both implication proofs for every `ExactBridge`:

| Claim | Lean declaration | Status |
|---|---|---|
| Formulation-family vocabulary | `FormulationFamily` | analytic/geometric/spectral/positivity |
| Typed proposition node | `Formulation` | project structure |
| Bidirectional checked translation | `ExactBridge` | project structure |
| Bridge reversal and composition | `ExactBridge.symm`, `ExactBridge.trans` | checked |
| Canonical RH ↔ dual fixed points | `statement_dualFixed_exactBridge` | checked |
| Canonical RH ↔ left-half zero-free | `statement_leftHalfZeroFree_exactBridge` | checked |
| Canonical RH ↔ right-half zero-free | `statement_rightHalfZeroFree_exactBridge` | checked |
| Geometric fixed points ↔ left-half zero-free | `dualFixed_leftHalfZeroFree_exactBridge` | checked by composition |
| Eta critical-strip criterion | `EtaCriticalStripCriterion` | parameterized definition |
| Eta/zeta zero compatibility | `EtaZetaZeroCompatibleOnCriticalStrip` | explicit bridge obligation |
| Canonical RH ↔ eta criterion | `statement_eta_exactBridge` | checked conditional on compatibility |

The concrete checked graph currently spans analytic and geometric nodes. Spectral and classical
positivity formulations remain classified but have no node: the project has not selected a
self-adjoint operator/spectral encoding or a test-function space/positive functional. This absence
is recorded rather than replaced by an arbitrary proposition.

For a supplied Dirichlet eta function, Gate 5 isolates equality of its zero predicate with
Mathlib's zeta zero predicate throughout the open critical strip.
`statement_eta_exactBridge` proves that this obligation is sufficient for both criterion
translations. Gate 7 discharges it for the concrete project eta definition. See
`BRIDGE_AUDIT.md` for the current graph and source record.

## Gate 6: 4PEL feasibility result

`RiemannHypothesisLean.FourPELFeasibility` tests a minimal bilateral four-valued layer away from
the RH graph:

| Claim | Lean declaration | Status |
|---|---|---|
| Explicit bilateral theory context | `BilateralTheory` | project structure |
| Positive derivability | `PositiveDerivable` | defined relative to context |
| Negative derivability | `NegativeDerivable` | defined relative to context |
| Four support profiles | `FourSupportValue` | gap/true-only/false-only/glut |
| Profile characterization theorems | `fourSupportValue_eq_*_iff` | checked |
| Channel-preserving exact translation | `ExactSupportTranslation` | project structure |
| Identity and composition | `ExactSupportTranslation.refl/trans` | checked |
| Four-value preservation | `ExactSupportTranslation.fourSupportValue_map` | checked |
| Finite four-profile correspondence | `miniExactSupportTranslation` | checked |
| Falsifiable novelty criterion | `AddsInformationBeyondSupportChannels` | defined |
| Minimal classifier fails novelty test | `fourSupportValue_not_addsInformation` | checked for every context |

The result is mixed. Separate positive and negative support, gaps, gluts, and channel-preserving
translation are formally coherent. However, the induced four-value classifier contains no
information beyond the pair of support predicates from which it is calculated. This negative
result prevents a merely decorative 4PEL labeling of the RH bridge graph.

A richer proposal must first provide rule-governed derivability and a justified structural
observation or consequence that distinguishes cases with the same bilateral support profile and is
preserved across translations. See `FOURPEL_FEASIBILITY.md` for the acceptance criterion and
research interpretation.

## Gate 7: concrete Dirichlet eta bridge

`RiemannHypothesisLean.DirichletEta` closes the parameterized Gate 5 obligation for a concrete
factorized eta function:

| Claim | Lean declaration | Status |
|---|---|---|
| Eta factor `1 - 2^(1-s)` | `dirichletEtaFactor` | defined |
| Concrete eta with value `log 2` at `s = 1` | `dirichletEta` | defined |
| Critical-strip points avoid `s = 1` | `InCriticalStrip.ne_one` | checked |
| Complex `log 2` is real | `complexLog_two` | checked |
| Exponent has positive real part | `log_two_mul_one_sub_re_pos` | checked |
| Eta factor is nonzero in the strip | `dirichletEtaFactor_ne_zero_of_inCriticalStrip` | checked |
| Eta zero iff zeta zero in the strip | `dirichletEta_eq_zero_iff_riemannZeta_eq_zero_of_inCriticalStrip` | checked |
| Concrete zero-set compatibility | `dirichletEta_zetaZeroCompatible` | checked |
| Unconditional exact RH/eta bridge | `statement_dirichletEta_exactBridge` | checked |
| Proposition-level equivalence | `statement_iff_dirichletEtaCriticalStripCriterion` | checked |

The nonvanishing proof reduces a hypothetical `2^(1-s) = 1` to equality of norms. Mathlib's
complex exponential norm formula gives
`exp (log 2 * (1 - re(s))) = 1`, contradicting positivity of both factors when `re(s) < 1`.

The function is defined through the factorized analytic continuation, with the removable value
specified at one. Gate 7 does not construct eta independently from the alternating series, prove
agreement with that series, or prove global analyticity. It also does not prove either equivalent
RH statement.

## Gate 8: independent alternating eta foundation

`RiemannHypothesisLean.AlternatingEta` starts from period-two coefficient data rather than from
`riemannZeta`:

| Claim | Lean declaration | Status |
|---|---|---|
| Eta residue coefficient on `ZMod 2` | `etaResidueCoefficient` | defined independently |
| Positive-index coefficient sequence | `alternatingEtaCoefficient` | defined |
| Naive eta Dirichlet series | `alternatingDirichletEtaSeries` | defined using `LSeries` |
| Periodic analytic continuation | `alternatingDirichletEtaContinuation` | defined using `ZMod.LFunction` |
| Series summability for `1 < re(s)` | `alternatingDirichletEtaSeries_summable_of_one_lt_re` | checked |
| Continuation equals series for `1 < re(s)` | `alternatingDirichletEtaContinuation_eq_series_of_one_lt_re` | checked |
| Differentiability away from `s = 1` | `differentiableAt_alternatingDirichletEtaContinuation` | checked |
| Coefficient mean is zero | `etaResidueCoefficient_sum` | checked |
| Independent continuation is entire | `differentiable_alternatingDirichletEtaContinuation` | checked |
| Real eta partial sums | `realAlternatingEtaPartialSum` | explicitly defined in natural order |
| Sequential convergence for every `x > 0` | `realAlternatingEtaSeries_converges_of_pos` | checked by the alternating-series test |
| Complex natural-order partial sums | `complexAlternatingEtaPartialSum` | explicitly defined |
| Real-axis agreement of complex and real partial sums | `complexAlternatingEtaPartialSum_ofReal` | checked termwise through `Complex.ofReal_cpow` |
| Complex-codomain convergence on the positive real axis | `complexAlternatingEtaSeries_converges_of_pos_real` | checked by continuous embedding |
| Paired complex eta term | `complexAlternatingEtaPair` | explicitly defined |
| Named natural-order eta value | `alternatingEtaNaturalValue` | defined by the absolutely summable paired series |
| Even partial sums equal paired partial sums | `complexAlternatingEtaPartialSum_two_mul` | checked by a finite-sum pairing lemma |
| Odd/even positive `LSeries` term formulas | `alternatingEtaLSeries_term_odd`, `alternatingEtaLSeries_term_even` | checked |
| Cofinal finite `LSeries`/paired-partial-sum identity | `alternatingEtaLSeries_partialSum_two_mul_add_one` | checked without convergence assumptions |
| Real-variable complex power kernel | `etaCpowKernel` | defined independently |
| Derivative of the power kernel | `hasDerivAt_etaCpowKernel` | checked at nonzero inputs |
| Differentiability on positive inputs | `differentiableAt_etaCpowKernel_of_pos` | checked |
| Exact derivative norm on positive inputs | `norm_etaCpowKernel_derivative` | checked |
| Pointwise norm bound for paired eta terms when `0 < re(s)` | `norm_complexAlternatingEtaPair_le` | checked by the mean-value inequality |
| Summability of paired-term norms when `0 < re(s)` | `summable_norm_complexAlternatingEtaPair` | checked by p-series comparison |
| Absolute summability of the paired series when `0 < re(s)` | `summable_complexAlternatingEtaPair` | checked |
| Holomorphy of the natural paired-series value when `0 < re(s)` | `differentiableAt_alternatingEtaNaturalValue`, `differentiableOn_alternatingEtaNaturalValue` | checked by local uniform p-series majorants |
| Convergence of paired partial sums when `0 < re(s)` | `complexAlternatingEtaPairedPartialSum_tendsto` | checked |
| Convergence of even eta partial sums when `0 < re(s)` | `complexAlternatingEtaPartialSum_even_tendsto` | checked through finite pairing |
| Vanishing unpaired term when `0 < re(s)` | `complexAlternatingEtaOddRemainder_tendsto_zero` | checked through the norm formula |
| Odd/even partial-sum recurrence | `complexAlternatingEtaPartialSum_two_mul_add_one` | checked |
| Convergence of odd eta partial sums when `0 < re(s)` | `complexAlternatingEtaPartialSum_odd_tendsto` | checked |
| Even/odd subsequence combination | `tendsto_nat_of_even_odd` | checked |
| Convergence of all natural-order complex eta partial sums when `0 < re(s)` | `complexAlternatingEtaPartialSum_tendsto` | checked |
| Natural-order complex eta convergence when `0 < re(s)` | `complexAlternatingEtaSeries_converges_of_pos_re` | checked |
| Natural value equals naive `LSeries` when `1 < re(s)` | `alternatingEtaNaturalValue_eq_series_of_one_lt_re` | checked by cofinal partial sums and uniqueness of limits |
| Natural value equals periodic continuation when `1 < re(s)` | `alternatingEtaNaturalValue_eq_continuation_of_one_lt_re` | checked |
| Natural value equals periodic continuation when `0 < re(s)` | `alternatingEtaNaturalValue_eq_continuation_of_pos_re` | checked by the identity theorem on the connected right half-plane |
| Natural value has the factorization `(1-2^(1-s))ζ(s)` when `1 < re(s)` | `alternatingEtaNaturalValue_eq_factor_mul_zeta_of_one_lt_re` | checked by odd/even splitting of the absolutely summable zeta series |
| Natural value equals Gate 7 `dirichletEta` when `1 < re(s)` | `alternatingEtaNaturalValue_eq_dirichletEta_of_one_lt_re` | checked |
| Periodic continuation equals the zeta-factor expression for `s ≠ 1` | `alternatingDirichletEtaContinuation_eq_factor_mul_zeta_of_ne_one` | checked by analytic continuation on `ℂ \\ {1}` |
| Periodic continuation equals Gate 7 `dirichletEta` for `s ≠ 1` | `alternatingDirichletEtaContinuation_eq_dirichletEta_of_ne_one` | checked |
| Eta factor has derivative `log 2` at one | `hasDerivAt_dirichletEtaFactor_one` | checked |
| Eta factor quotient tends to `log 2` at one | `tendsto_dirichletEtaFactor_div_sub_one` | checked |
| Factorized eta product tends to `log 2` at one | `tendsto_dirichletEtaFactor_mul_riemannZeta_one` | checked using `riemannZeta_residue_one` |
| Independent continuation has value `log 2` at one | `alternatingDirichletEtaContinuation_one` | checked by continuity and uniqueness of limits |
| Periodic continuation equals Gate 7 `dirichletEta` globally | `alternatingDirichletEtaContinuation_eq_dirichletEta` | checked |
| Natural value equals Gate 7 `dirichletEta` when `0 < re(s)` | `alternatingEtaNaturalValue_eq_dirichletEta_of_pos_re` | checked |
| Harmonic difference `H_(2N)-H_N` tends to `log 2` | `tendsto_harmonic_two_mul_sub_harmonic` | checked from `Real.tendsto_harmonic_sub_log` |
| Even alternating harmonic partial sum equals `H_(2N)-H_N` | `realAlternatingEtaPartialSum_one_two_mul` | checked by finite pairing |
| Even alternating harmonic partial sums tend to `log 2` | `realAlternatingEtaPartialSum_one_even_tendsto` | checked |
| Natural eta value at one is `log 2` | `alternatingEtaNaturalValue_one` | checked independently of the continuation |
| Natural value and periodic continuation agree at one | `alternatingEtaNaturalValue_eq_continuation_one` | checked |

The convergence results use explicit `Finset.range` partial sums and `Filter.Tendsto`. They do not
mislabel conditional convergence as Mathlib's stronger order-independent `Summable` predicate.

The periodic continuation is identified globally with the factorized Gate 7 function, including
its independently derived value `log 2` at `s = 1`. The natural alternating harmonic series is
independently linked to the continuation at one. Local uniform majorants make the paired-series
value holomorphic on `0 < re(s)`, and the identity theorem closes the remaining conditionally
convergent series/continuation bridge throughout that half-plane. This is a full
series-interoperability result on the natural convergence domain; it does not by itself prove a
new zero-free statement or the Riemann hypothesis.

## Gate 9: Riemann xi foundation

`RiemannHypothesisLean.RiemannXi` constructs the entire function needed for Li-type positivity
criteria directly from pinned Mathlib's completed-zeta infrastructure:

| Claim | Lean declaration | Status |
|---|---|---|
| Entire Riemann xi function | `riemannXi` | defined from `completedRiemannZeta₀` |
| Xi is entire | `differentiable_riemannXi` | checked |
| Functional symmetry `ξ(1-s)=ξ(s)` | `riemannXi_one_sub` | checked |
| Values `ξ(0)=ξ(1)=1/2` | `riemannXi_zero`, `riemannXi_one` | checked |
| Classical completed-zeta product away from zero and one | `riemannXi_eq_completedRiemannZeta` | checked |
| Xi/completed-zeta zero equivalence away from zero and one | `riemannXi_eq_zero_iff_completedRiemannZeta_eq_zero` | checked |
| Xi/zeta zero equivalence on `0 < re(s)`, `s ≠ 1` | `riemannXi_eq_zero_iff_riemannZeta_eq_zero` | checked |
| No xi zeros when `re(s) ≤ 0` | `riemannXi_ne_zero_of_re_nonpos` | checked using reflection and zeta nonvanishing |
| Positive real part of every xi zero | `riemannXi_zero_re_pos` | checked |
| Xi zeros equal project nontrivial zeta zeros | `riemannXi_eq_zero_iff_isNontrivialZero` | checked |
| Xi critical-line criterion | `XiCriticalLineCriterion` | defined |
| Project RH statement equals xi criterion | `statement_iff_xiCriticalLineCriterion` | checked |

The pinned dependency does not provide Li coefficients or Li's criterion. Consequently, no
positivity/RH equivalence is imported or postulated. Gate 9 must next construct the coefficients
using iterated derivatives near `s = 1`, prove their reality, and only then address the classical
nonnegativity equivalence.

## Non-goals of the first milestone

- treating numerical verification as a universal proof;
- adding RH as an axiom;
- disguising an RH-equivalent statement as progress toward its proof;
- importing an informal argument without formalizing its analytic prerequisites.
