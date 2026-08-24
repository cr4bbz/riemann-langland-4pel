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
| A nontrivial zero satisfies `re(s) < 1` | `IsNontrivialZero.re_lt_one` | checked |
| Full localization in `0 < re(s) < 1` | `CriticalStripLocalization` | named proposition, not proved |
| Remaining left boundary `0 < re(s)` | `PositiveRealPartForNontrivialZeros` | named proposition, not proved |
| Reduction of localization to left boundary | `criticalStripLocalization_iff_positiveRealPart` | checked |

The last equivalence is a dependency reduction, not a proof of localization: Mathlib supplies the
right-hand inequality, while the positive-real-part condition remains open in this formalization.

## Gate 2: symmetry boundary

`RiemannHypothesisLean.Symmetry` distinguishes transformations, zero transport, and fixed points:

| Claim | Lean declaration | Status |
|---|---|---|
| `s ↦ 1 - s` is an involution | `criticalReflection_involutive` | checked |
| `s ↦ conj(s)` is an involution | `conjugationPoint_involutive` | checked |
| `s ↦ 1 - conj(s)` is an involution | `dualSymmetry_involutive` | checked |
| Fixed points of the dual symmetry form the critical line | `dualSymmetry_fixed_iff_onCriticalLine` | checked |
| Completed-zeta zeros reflect under `s ↦ 1 - s` | `completedZetaZero_criticalReflection_iff` | checked |
| Ordinary zeta commutes with conjugation globally | `RiemannZetaConjugationCompatibility` | named bridge, not proved |
| Conjugation transports ordinary zeros | `riemannZeta_eq_zero_conjugationPoint` | checked conditionally on the bridge |
| RH is pointwise fixation under the dual symmetry | `statement_iff_nontrivialZerosFixedByDualSymmetry` | checked reformulation |
| Setwise symmetry alone need not imply pointwise fixation | `setwiseDualInvariant_not_pointwiseFixed` | checked generic counterexample |

`RiemannHypothesisLean.Conjugation` proves the first analytic stage:

| Claim | Lean declaration | Status |
|---|---|---|
| Zeta commutes with conjugation on `1 < re(s)` | `riemannZeta_conjugation_of_one_lt_re` | checked from the Dirichlet series |
| Same result through the project transformation | `riemannZeta_conjugationPoint_of_one_lt_re` | checked |

The proof moves conjugation through Mathlib's convergent `tsum` and checks every Dirichlet term
using conjugation of complex powers. The remaining step is an identity-theorem argument on the
analytically continued function away from its pole; it is not silently assumed here.

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
| Localization and conjugation yield the orbit | `riemannZetaZeroOrbit_of_localization_and_conjugation` | checked conditionally |
| Positive real part and conjugation yield the orbit | `riemannZetaZeroOrbit_of_positiveRealPart_and_conjugation` | checked conditionally |

Thus the reflection leg of the ordinary-zeta orbit is no longer an independent bridge. It follows
from the completed functional equation once a zero is known to lie in the critical strip. The
remaining orbit dependencies are exactly the positive-real-part condition from Gate 1 and the
global ordinary-zeta conjugation compatibility named in Gate 2.

## Non-goals of the first milestone

- treating numerical verification as a universal proof;
- adding RH as an axiom;
- disguising an RH-equivalent statement as progress toward its proof;
- importing an informal argument without formalizing its analytic prerequisites.
