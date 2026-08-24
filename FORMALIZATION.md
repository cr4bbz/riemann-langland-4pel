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

## Non-goals of the first milestone

- treating numerical verification as a universal proof;
- adding RH as an axiom;
- disguising an RH-equivalent statement as progress toward its proof;
- importing an informal argument without formalizing its analytic prerequisites.
