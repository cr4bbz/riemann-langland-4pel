import RiemannHypothesisLean

open Complex

namespace RiemannHypothesisLean

example : Statement ↔ RiemannHypothesis := statement_iff_mathlib

example (h : Statement) {s : ℂ} (hs : IsNontrivialZero s) : OnCriticalLine s :=
  h s hs

example {s : ℂ} (hs : IsTrivialZero s) : riemannZeta s = 0 :=
  hs.riemannZeta_eq_zero

example {s : ℂ} (hs : IsNontrivialZero s) : 0 < s.re :=
  hs.re_pos

example {s : ℂ} (hs : IsNontrivialZero s) : s.re < 1 :=
  hs.re_lt_one

example {s : ℂ} (hs : IsNontrivialZero s) : InCriticalStrip s :=
  criticalStripLocalization s hs

example : CriticalStripLocalization ↔ PositiveRealPartForNontrivialZeros :=
  criticalStripLocalization_iff_positiveRealPart

example (s : ℂ) : IsCompletedZetaZero (criticalReflection s) ↔ IsCompletedZetaZero s :=
  completedZetaZero_criticalReflection_iff s

example {s : ℂ} (hs : 1 < s.re) :
    riemannZeta (star s) = star (riemannZeta s) :=
  riemannZeta_conjugation_of_one_lt_re hs

example {s : ℂ} (hs : s ≠ 1) :
    riemannZeta (star s) = star (riemannZeta s) :=
  riemannZeta_conjugation_of_ne_one hs

example {s : ℂ} (hs : IsNontrivialZero s) :
    riemannZeta (conjugationPoint s) = 0 :=
  hs.riemannZeta_conjugationPoint_eq_zero

example : Statement ↔ NontrivialZerosFixedByDualSymmetry :=
  statement_iff_nontrivialZerosFixedByDualSymmetry

example {s : ℂ} (hz : riemannZeta s = 0) (hs : InCriticalStrip s) :
    riemannZeta (criticalReflection s) = 0 :=
  riemannZetaZero_criticalReflection hz hs

example {s : ℂ} (hs : IsNontrivialZero s) :
    RiemannZetaZeroOrbit s :=
  riemannZetaZeroOrbit_of_localization criticalStripLocalization hs

end RiemannHypothesisLean
