import RiemannHypothesisLean

open Complex

namespace RiemannHypothesisLean

example : Statement ↔ RiemannHypothesis := statement_iff_mathlib

example (h : Statement) {s : ℂ} (hs : IsNontrivialZero s) : OnCriticalLine s :=
  h s hs

example {s : ℂ} (hs : IsTrivialZero s) : riemannZeta s = 0 :=
  hs.riemannZeta_eq_zero

example {s : ℂ} (hs : IsNontrivialZero s) : s.re < 1 :=
  hs.re_lt_one

example : CriticalStripLocalization ↔ PositiveRealPartForNontrivialZeros :=
  criticalStripLocalization_iff_positiveRealPart

example (s : ℂ) : IsCompletedZetaZero (criticalReflection s) ↔ IsCompletedZetaZero s :=
  completedZetaZero_criticalReflection_iff s

example : Statement ↔ NontrivialZerosFixedByDualSymmetry :=
  statement_iff_nontrivialZerosFixedByDualSymmetry

end RiemannHypothesisLean
