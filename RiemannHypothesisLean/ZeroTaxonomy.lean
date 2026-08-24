import Mathlib.NumberTheory.LSeries.Nonvanishing
import RiemannHypothesisLean.Statement

/-!
# Zero taxonomy and critical-strip localization

This module connects the project-facing zero predicates to Mathlib's established theorems. The
right boundary follows from Mathlib's nonvanishing theorem. For the left boundary, zeros of the
real Gamma factor are identified with the negative even integers; after excluding those and
`s = 0`, the completed functional equation reflects any hypothetical zero with `re(s) ≤ 0`
into Mathlib's zero-free half-plane.
-/

open Complex

namespace RiemannHypothesisLean

/-- Every project-level trivial zero is a zero of the Riemann zeta function. -/
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

/-- The special value `ζ(0) = -1/2` excludes zero itself from the nontrivial zero set. -/
theorem IsNontrivialZero.ne_zero {s : ℂ} (hs : IsNontrivialZero s) : s ≠ 0 := by
  intro h
  subst s
  have hz := hs.riemannZeta_eq_zero
  rw [riemannZeta_zero] at hz
  norm_num at hz

/-- The real Gamma factor does not vanish at a project-level nontrivial zero.

Mathlib classifies its zeros as `s = -2n`. The case `n = 0` is excluded by `ζ(0) ≠ 0`;
all successor cases are exactly the project's trivial zeros. -/
theorem IsNontrivialZero.Gammaℝ_ne_zero {s : ℂ} (hs : IsNontrivialZero s) :
    Gammaℝ s ≠ 0 := by
  intro hGamma
  obtain ⟨n, hn⟩ := Gammaℝ_eq_zero_iff.mp hGamma
  rcases n with _ | n
  · apply hs.ne_zero
    simpa using hn
  · apply hs.not_trivial
    refine ⟨n, ?_⟩
    rw [hn]
    push_cast
    ring

/-- Mathlib's nonvanishing theorem on `re(s) ≥ 1` gives the right boundary of the critical strip. -/
theorem IsNontrivialZero.re_lt_one {s : ℂ} (hs : IsNontrivialZero s) : s.re < 1 := by
  by_contra h
  exact (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt h)) hs.riemannZeta_eq_zero

/-- Every project-level nontrivial zero has positive real part.

A zero outside the positive half-plane is first lifted to a zero of the completed zeta function.
The completed functional equation reflects it to `1 - s`, whose real part is at least `1`,
contradicting Mathlib's nonvanishing theorem there. -/
theorem IsNontrivialZero.re_pos {s : ℂ} (hs : IsNontrivialZero s) : 0 < s.re := by
  by_contra hpos
  have hnonpos : s.re ≤ 0 := le_of_not_gt hpos
  have hcompleted : completedRiemannZeta s = 0 := by
    have hz := hs.riemannZeta_eq_zero
    rw [riemannZeta_def_of_ne_zero hs.ne_zero] at hz
    rcases div_eq_zero_iff.mp hz with h | h
    · exact h
    · exact (hs.Gammaℝ_ne_zero h).elim
  have hreflectedCompleted : completedRiemannZeta (1 - s) = 0 := by
    rw [completedRiemannZeta_one_sub, hcompleted]
  have hreflectNeZero : 1 - s ≠ 0 :=
    sub_ne_zero.mpr hs.ne_one.symm
  have hreflectedZero : riemannZeta (1 - s) = 0 := by
    rw [riemannZeta_def_of_ne_zero hreflectNeZero, hreflectedCompleted]
    simp
  have hreflectRe : 1 ≤ (1 - s).re := by
    simp only [sub_re, one_re]
    linarith
  exact (riemannZeta_ne_zero_of_one_le_re hreflectRe) hreflectedZero

/-- The full classical localization claim for the project-level nontrivial zeros. -/
def CriticalStripLocalization : Prop :=
  ∀ s : ℂ, IsNontrivialZero s → InCriticalStrip s

/-- The left boundary needed for full critical-strip localization. -/
def PositiveRealPartForNontrivialZeros : Prop :=
  ∀ s : ℂ, IsNontrivialZero s → 0 < s.re

/-- Since the right boundary is checked independently, full localization is equivalent to the
positive-real-part condition. -/
theorem criticalStripLocalization_iff_positiveRealPart :
    CriticalStripLocalization ↔ PositiveRealPartForNontrivialZeros := by
  constructor
  · intro h s hs
    exact (h s hs).1
  · intro h s hs
    exact ⟨h s hs, hs.re_lt_one⟩

/-- The positive-real-part boundary is now discharged. -/
theorem positiveRealPartForNontrivialZeros : PositiveRealPartForNontrivialZeros :=
  fun _ hs ↦ hs.re_pos

/-- Every project-level nontrivial zero lies in the open critical strip. -/
theorem criticalStripLocalization : CriticalStripLocalization :=
  criticalStripLocalization_iff_positiveRealPart.mpr positiveRealPartForNontrivialZeros

end RiemannHypothesisLean
