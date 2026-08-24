import Mathlib.NumberTheory.LSeries.ZetaZeros

/-!
# The Riemann hypothesis as a Lean proposition

This module gives explicit names to the mathematical components of the
Riemann hypothesis and proves that the project statement is equivalent to
Mathlib's canonical `RiemannHypothesis` proposition.

No proof of the Riemann hypothesis is claimed here.
-/

open Complex

namespace RiemannHypothesisLean

/-- A trivial zero is one of the negative even integers. -/
def IsTrivialZero (s : ℂ) : Prop :=
  ∃ n : ℕ, s = -2 * (n + 1)

/-- A nontrivial zero is a zero of `riemannZeta` that is not a trivial zero or the pole at `1`.

Mathlib gives `riemannZeta` a totalized value at every complex input, so the explicit `s ≠ 1`
condition keeps the proposition aligned with the analytic statement. -/
def IsNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ ¬IsTrivialZero s ∧ s ≠ 1

/-- The open critical strip `0 < re(s) < 1`. -/
def InCriticalStrip (s : ℂ) : Prop :=
  0 < s.re ∧ s.re < 1

/-- The critical line `re(s) = 1 / 2`. -/
def OnCriticalLine (s : ℂ) : Prop :=
  s.re = 1 / 2

/-- The project-facing formulation of the Riemann hypothesis. -/
def Statement : Prop :=
  ∀ s : ℂ, IsNontrivialZero s → OnCriticalLine s

/-- The project statement is definitionally faithful to Mathlib's canonical formulation. -/
theorem statement_iff_mathlib : Statement ↔ RiemannHypothesis := by
  constructor
  · intro h s hz htrivial hne
    exact h s ⟨hz, htrivial, hne⟩
  · intro h s hs
    exact h s hs.1 hs.2.1 hs.2.2

end RiemannHypothesisLean
