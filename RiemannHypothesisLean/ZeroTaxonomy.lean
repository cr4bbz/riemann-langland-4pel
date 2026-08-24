import Mathlib.NumberTheory.LSeries.Nonvanishing
import RiemannHypothesisLean.Statement

/-!
# Zero taxonomy and the critical-strip boundary

This module connects the project-facing zero predicates to Mathlib's established theorems.
It proves the easy/right-hand part of critical-strip localization and names the remaining
left-hand boundary as an explicit proposition. No proof of that remaining proposition is claimed.
-/

open Complex

namespace RiemannHypothesisLean

/-- Every project-level trivial zero is a zero of the Riemann zeta function.

This is the forward direction supplied by Mathlib's trivial-zero theorem; it does not claim here
that every zeta zero outside the critical strip has already been classified. -/
theorem IsTrivialZero.riemannZeta_eq_zero {s : ℂ} (hs : IsTrivialZero s) :
    riemannZeta s = 0 := by
  obtain ⟨n, rfl⟩ := hs
  exact riemannZeta_neg_two_mul_nat_add_one n

/-- A nontrivial zero is, in particular, a zero of the zeta function. -/
theorem IsNontrivialZero.riemannZeta_eq_zero {s : ℂ} (hs : IsNontrivialZero s) :
    riemannZeta s = 0 :=
  hs.1

/-- A nontrivial zero is not one of the named trivial zeros. -/
theorem IsNontrivialZero.not_trivial {s : ℂ} (hs : IsNontrivialZero s) :
    ¬IsTrivialZero s :=
  hs.2.1

/-- A nontrivial zero is distinct from the totalized pole location `1`. -/
theorem IsNontrivialZero.ne_one {s : ℂ} (hs : IsNontrivialZero s) : s ≠ 1 :=
  hs.2.2

/-- Mathlib's nonvanishing theorem on `re(s) ≥ 1` gives the right boundary of the critical strip. -/
theorem IsNontrivialZero.re_lt_one {s : ℂ} (hs : IsNontrivialZero s) : s.re < 1 := by
  by_contra h
  exact (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h)) hs.riemannZeta_eq_zero

/-- The full classical localization claim for the project-level nontrivial zeros. -/
def CriticalStripLocalization : Prop :=
  ∀ s : ℂ, IsNontrivialZero s → InCriticalStrip s

/-- The presently missing boundary needed for full critical-strip localization.

The name is deliberately a proposition rather than a postulated assumption or theorem. -/
def PositiveRealPartForNontrivialZeros : Prop :=
  ∀ s : ℂ, IsNontrivialZero s → 0 < s.re

/-- Since the right boundary is already checked, full critical-strip localization is equivalent
to proving only that nontrivial zeros have positive real part. -/
theorem criticalStripLocalization_iff_positiveRealPart :
    CriticalStripLocalization ↔ PositiveRealPartForNontrivialZeros := by
  constructor
  · intro h s hs
    exact (h s hs).1
  · intro h s hs
    exact ⟨h s hs, hs.re_lt_one⟩

end RiemannHypothesisLean
