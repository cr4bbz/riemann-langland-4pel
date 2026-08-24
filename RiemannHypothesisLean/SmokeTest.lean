import RiemannHypothesisLean.Statement

open Complex

namespace RiemannHypothesisLean

example : Statement ↔ RiemannHypothesis := statement_iff_mathlib

example (h : Statement) {s : ℂ} (hs : IsNontrivialZero s) : OnCriticalLine s :=
  h s hs

end RiemannHypothesisLean
