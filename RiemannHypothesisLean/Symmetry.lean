import RiemannHypothesisLean.ZeroTaxonomy

/-!
# Symmetry foundations

This module separates three different statements that are often blurred together informally:

1. algebraic transformations of the complex plane;
2. transport of zeros under those transformations;
3. pointwise fixation of every nontrivial zero.

The completed zeta reflection is proved from Mathlib's functional equation. Conjugation
compatibility is named as an explicit bridge because the pinned Mathlib surface does not expose
it as a directly reusable theorem here. No such bridge is postulated.
-/

open Complex

namespace RiemannHypothesisLean

noncomputable section

/-- Reflection across the vertical line `re(s) = 1 / 2`. -/
def criticalReflection (s : ℂ) : ℂ :=
  1 - s

/-- Reflection across the real axis. -/
def conjugationPoint (s : ℂ) : ℂ :=
  star s

/-- The composition `s ↦ 1 - conj(s)`, whose fixed-point set is the critical line. -/
def dualSymmetry (s : ℂ) : ℂ :=
  1 - star s

@[simp]
theorem criticalReflection_involutive (s : ℂ) :
    criticalReflection (criticalReflection s) = s := by
  simp [criticalReflection]

@[simp]
theorem conjugationPoint_involutive (s : ℂ) :
    conjugationPoint (conjugationPoint s) = s := by
  simp [conjugationPoint]

@[simp]
theorem dualSymmetry_involutive (s : ℂ) :
    dualSymmetry (dualSymmetry s) = s := by
  simp [dualSymmetry]

@[simp]
theorem criticalReflection_re (s : ℂ) :
    (criticalReflection s).re = 1 - s.re := by
  simp [criticalReflection]

@[simp]
theorem conjugationPoint_re (s : ℂ) :
    (conjugationPoint s).re = s.re := by
  simp [conjugationPoint]

@[simp]
theorem dualSymmetry_re (s : ℂ) :
    (dualSymmetry s).re = 1 - s.re := by
  simp [dualSymmetry]

/-- The fixed points of `s ↦ 1 - conj(s)` are exactly the points on the critical line. -/
theorem dualSymmetry_fixed_iff_onCriticalLine (s : ℂ) :
    dualSymmetry s = s ↔ OnCriticalLine s := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp only [dualSymmetry_re] at hre
    unfold OnCriticalLine
    linarith
  · intro h
    apply Complex.ext
    · simp only [dualSymmetry_re]
      unfold OnCriticalLine at h
      linarith
    · simp [dualSymmetry]

/-- A zero of the completed Riemann zeta function. -/
def IsCompletedZetaZero (s : ℂ) : Prop :=
  completedRiemannZeta s = 0

/-- Mathlib's completed functional equation transports completed-zeta zeros under `s ↦ 1 - s`. -/
theorem completedZetaZero_criticalReflection_iff (s : ℂ) :
    IsCompletedZetaZero (criticalReflection s) ↔ IsCompletedZetaZero s := by
  unfold IsCompletedZetaZero criticalReflection
  rw [completedRiemannZeta_one_sub]

/-- The conjugation formula needed to transport ordinary zeta zeros across the real axis.

This is deliberately only a named proposition at the current dependency boundary. -/
def RiemannZetaConjugationCompatibility : Prop :=
  ∀ s : ℂ, riemannZeta (star s) = star (riemannZeta s)

/-- Conditional zero transport across the real axis, displaying the missing bridge explicitly. -/
theorem riemannZeta_eq_zero_conjugationPoint
    (hconj : RiemannZetaConjugationCompatibility) {s : ℂ}
    (hs : riemannZeta s = 0) : riemannZeta (conjugationPoint s) = 0 := by
  change riemannZeta (star s) = 0
  rw [hconj s, hs]
  simp

/-- Setwise closure of the nontrivial zeros under the dual symmetry. -/
def NontrivialZerosClosedUnderDualSymmetry : Prop :=
  ∀ s : ℂ, IsNontrivialZero s → IsNontrivialZero (dualSymmetry s)

/-- Pointwise fixation of all nontrivial zeros under the dual symmetry. -/
def NontrivialZerosFixedByDualSymmetry : Prop :=
  ∀ s : ℂ, IsNontrivialZero s → dualSymmetry s = s

/-- RH is exactly the pointwise-fixation claim, not merely a setwise symmetry claim. -/
theorem statement_iff_nontrivialZerosFixedByDualSymmetry :
    Statement ↔ NontrivialZerosFixedByDualSymmetry := by
  constructor
  · intro h s hs
    exact (dualSymmetry_fixed_iff_onCriticalLine s).2 (h s hs)
  · intro h s hs
    exact (dualSymmetry_fixed_iff_onCriticalLine s).1 (h s hs)

/-- Pointwise fixation implies setwise closure. The converse is intentionally not asserted. -/
theorem nontrivialZerosClosedUnderDualSymmetry_of_fixed
    (h : NontrivialZerosFixedByDualSymmetry) :
    NontrivialZerosClosedUnderDualSymmetry := by
  intro s hs
  simpa [h s hs] using hs

/-- A checked generic counterexample showing that setwise invariance under the dual symmetry does
not, by logic alone, imply that every member is fixed. This says nothing about which complex
numbers are zeta zeros; it isolates the missing inference pattern. -/
theorem setwiseDualInvariant_not_pointwiseFixed :
    ∃ S : Set ℂ,
      (∀ s : ℂ, s ∈ S → dualSymmetry s ∈ S) ∧
      ¬(∀ s : ℂ, s ∈ S → dualSymmetry s = s) := by
  refine ⟨Set.univ, ?_, ?_⟩
  · intro s _
    exact Set.mem_univ _
  · intro h
    have h0 := h 0 (Set.mem_univ 0)
    norm_num [dualSymmetry] at h0

end RiemannHypothesisLean
