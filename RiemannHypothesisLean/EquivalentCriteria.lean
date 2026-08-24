import RiemannHypothesisLean.Finiteness

/-!
# Equivalent zero-free half-strip criteria

Every project-level nontrivial zero already lies in the open critical strip, and its image under
`s ↦ 1 - conj(s)` is again a nontrivial zero. Consequently, excluding nontrivial zeros from
either open half of the critical strip is equivalent to the Riemann hypothesis.

These are genuine two-way reductions. They do not prove either zero-free criterion.
-/

open Complex

namespace RiemannHypothesisLean

noncomputable section

/-- A point with positive real part cannot be one of the named negative-even trivial zeros. -/
theorem not_isTrivialZero_of_re_pos {s : ℂ} (hs : 0 < s.re) :
    ¬IsTrivialZero s := by
  rintro ⟨n, rfl⟩
  norm_num at hs

/-- The dual symmetry preserves project-level nontrivial zeros.

The zeta-zero component comes from the checked four-point orbit. Critical-strip localization
excludes both the named trivial zeros and the pole location at the transformed point. -/
theorem IsNontrivialZero.dualSymmetry {s : ℂ} (hs : IsNontrivialZero s) :
    IsNontrivialZero (dualSymmetry s) := by
  have hpos : 0 < (dualSymmetry s).re := by
    simp only [dualSymmetry_re]
    linarith [hs.re_lt_one]
  have hlt : (dualSymmetry s).re < 1 := by
    simp only [dualSymmetry_re]
    linarith [hs.re_pos]
  refine ⟨hs.riemannZetaZeroOrbit.dual, not_isTrivialZero_of_re_pos hpos, ?_⟩
  intro hone
  have hre := congrArg Complex.re hone
  have : (dualSymmetry s).re = 1 := by
    simpa using hre
  exact (ne_of_lt hlt) this

/-- No project-level nontrivial zero lies strictly left of the critical line.

Together with critical-strip localization, this is the zero-free region
`0 < re(s) < 1 / 2`. -/
def LeftHalfCriticalStripZeroFree : Prop :=
  ∀ s : ℂ, IsNontrivialZero s → (1 / 2 : ℝ) ≤ s.re

/-- No project-level nontrivial zero lies strictly right of the critical line.

Together with critical-strip localization, this is the zero-free region
`1 / 2 < re(s) < 1`. -/
def RightHalfCriticalStripZeroFree : Prop :=
  ∀ s : ℂ, IsNontrivialZero s → s.re ≤ (1 / 2 : ℝ)

/-- RH immediately implies the left-half zero-free criterion. -/
theorem leftHalfCriticalStripZeroFree_of_statement
    (h : Statement) : LeftHalfCriticalStripZeroFree := by
  intro s hs
  exact le_of_eq (h s hs).symm

/-- The left-half zero-free criterion implies RH by applying it also to the dual zero. -/
theorem statement_of_leftHalfCriticalStripZeroFree
    (h : LeftHalfCriticalStripZeroFree) : Statement := by
  intro s hs
  have hlower : (1 / 2 : ℝ) ≤ s.re := h s hs
  have hdual : (1 / 2 : ℝ) ≤ (dualSymmetry s).re :=
    h (dualSymmetry s) hs.dualSymmetry
  have hupper : s.re ≤ (1 / 2 : ℝ) := by
    rw [dualSymmetry_re] at hdual
    linarith
  exact le_antisymm hupper hlower

/-- RH is equivalent to excluding nontrivial zeros from the left half of the critical strip. -/
theorem statement_iff_leftHalfCriticalStripZeroFree :
    Statement ↔ LeftHalfCriticalStripZeroFree :=
  ⟨leftHalfCriticalStripZeroFree_of_statement,
    statement_of_leftHalfCriticalStripZeroFree⟩

/-- RH immediately implies the right-half zero-free criterion. -/
theorem rightHalfCriticalStripZeroFree_of_statement
    (h : Statement) : RightHalfCriticalStripZeroFree := by
  intro s hs
  exact le_of_eq (h s hs)

/-- The right-half zero-free criterion implies RH by applying it also to the dual zero. -/
theorem statement_of_rightHalfCriticalStripZeroFree
    (h : RightHalfCriticalStripZeroFree) : Statement := by
  intro s hs
  have hupper : s.re ≤ (1 / 2 : ℝ) := h s hs
  have hdual : (dualSymmetry s).re ≤ (1 / 2 : ℝ) :=
    h (dualSymmetry s) hs.dualSymmetry
  have hlower : (1 / 2 : ℝ) ≤ s.re := by
    rw [dualSymmetry_re] at hdual
    linarith
  exact le_antisymm hupper hlower

/-- RH is equivalent to excluding nontrivial zeros from the right half of the critical strip. -/
theorem statement_iff_rightHalfCriticalStripZeroFree :
    Statement ↔ RightHalfCriticalStripZeroFree :=
  ⟨rightHalfCriticalStripZeroFree_of_statement,
    statement_of_rightHalfCriticalStripZeroFree⟩

/-- The two one-sided zero-free criteria are equivalent through the checked dual symmetry. -/
theorem leftHalfCriticalStripZeroFree_iff_rightHalfCriticalStripZeroFree :
    LeftHalfCriticalStripZeroFree ↔ RightHalfCriticalStripZeroFree := by
  rw [← statement_iff_leftHalfCriticalStripZeroFree,
    statement_iff_rightHalfCriticalStripZeroFree]

end

end RiemannHypothesisLean
