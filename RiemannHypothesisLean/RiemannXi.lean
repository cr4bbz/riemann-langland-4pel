import RiemannHypothesisLean.ZeroTaxonomy

/-!
# Riemann's xi function

This module constructs the entire symmetric function underlying Li-type positivity criteria.

Mathlib's `completedRiemannZeta` has poles at zero and one, while
`completedRiemannZeta₀` is the entire pole-subtracted function satisfying
`Λ₀(1-s) = Λ₀(s)`. We define

`ξ(s) = (1 / 2) * (1 + s * (s - 1) * Λ₀(s))`.

Away from zero and one this is proved equal to the classical expression
`(1 / 2) * s * (s - 1) * Λ(s)`. No positivity criterion or Riemann-hypothesis
equivalence is asserted in this foundation module.
-/

open Complex

namespace RiemannHypothesisLean

noncomputable section

/-- Riemann's entire xi function, defined using Mathlib's entire pole-subtracted
completed zeta function. -/
def riemannXi (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (1 + s * (s - 1) * completedRiemannZeta₀ s)

/-- Riemann's xi function is entire. -/
theorem differentiable_riemannXi :
    Differentiable ℂ riemannXi := by
  unfold riemannXi
  exact (differentiable_const (𝕜 := ℂ) (1 / 2 : ℂ)).mul
    ((differentiable_const (𝕜 := ℂ) (1 : ℂ)).add
      ((differentiable_id.mul
        (differentiable_id.sub (differentiable_const (𝕜 := ℂ) (1 : ℂ)))).mul
        differentiable_completedZeta₀))

/-- Riemann's xi function is symmetric under `s ↦ 1 - s`. -/
theorem riemannXi_one_sub (s : ℂ) :
    riemannXi (1 - s) = riemannXi s := by
  unfold riemannXi
  rw [completedRiemannZeta₀_one_sub]
  ring

@[simp]
theorem riemannXi_zero :
    riemannXi 0 = (1 / 2 : ℂ) := by
  simp [riemannXi]

@[simp]
theorem riemannXi_one :
    riemannXi 1 = (1 / 2 : ℂ) := by
  simp [riemannXi]

/-- Away from the two removable points, the entire definition agrees with the
classical completed-zeta product. -/
theorem riemannXi_eq_completedRiemannZeta {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s =
      (1 / 2 : ℂ) * s * (s - 1) * completedRiemannZeta s := by
  rw [riemannXi, completedRiemannZeta_eq]
  field_simp [hs0, sub_ne_zero.mpr hs1, sub_ne_zero.mpr hs1.symm]
  ring

/-- Away from zero and one, xi and completed zeta have exactly the same zero
predicate. -/
theorem riemannXi_eq_zero_iff_completedRiemannZeta_eq_zero {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    riemannXi s = 0 ↔ completedRiemannZeta s = 0 := by
  rw [riemannXi_eq_completedRiemannZeta hs0 hs1]
  simp [hs0, sub_ne_zero.mpr hs1]

/-- On the positive-real-part domain away from the pole, xi and ordinary zeta
have exactly the same zero predicate. -/
theorem riemannXi_eq_zero_iff_riemannZeta_eq_zero {s : ℂ}
    (hsre : 0 < s.re) (hs1 : s ≠ 1) :
    riemannXi s = 0 ↔ riemannZeta s = 0 := by
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hsre
  rw [riemannXi_eq_zero_iff_completedRiemannZeta_eq_zero hs0 hs1,
    riemannZeta_def_of_ne_zero hs0]
  simp [Gammaℝ_ne_zero_of_re_pos hsre]

/-- Xi zeros are invariant under the functional-equation reflection. -/
theorem riemannXi_one_sub_eq_zero_iff (s : ℂ) :
    riemannXi (1 - s) = 0 ↔ riemannXi s = 0 := by
  rw [riemannXi_one_sub]

/-- Xi has no zeros in the closed left half-plane. Reflection would otherwise
produce a zeta zero in Mathlib's zero-free half-plane `re(s) ≥ 1`. -/
theorem riemannXi_ne_zero_of_re_nonpos {s : ℂ} (hsre : s.re ≤ 0) :
    riemannXi s ≠ 0 := by
  intro hxi
  have hs0 : s ≠ 0 := by
    intro hs
    subst s
    rw [riemannXi_zero] at hxi
    norm_num at hxi
  have hrefNeOne : 1 - s ≠ 1 := by
    intro href
    apply hs0
    calc
      s = 1 - (1 - s) := by ring
      _ = 1 - 1 := by rw [href]
      _ = 0 := by ring
  have hrefRePos : 0 < (1 - s).re := by
    simp only [sub_re, one_re]
    linarith
  have hrefXi : riemannXi (1 - s) = 0 :=
    (riemannXi_one_sub_eq_zero_iff s).2 hxi
  have hrefZeta : riemannZeta (1 - s) = 0 :=
    (riemannXi_eq_zero_iff_riemannZeta_eq_zero hrefRePos hrefNeOne).1 hrefXi
  have hrefReOne : 1 ≤ (1 - s).re := by
    simp only [sub_re, one_re]
    linarith
  exact (riemannZeta_ne_zero_of_one_le_re hrefReOne) hrefZeta

/-- Every xi zero has positive real part. -/
theorem riemannXi_zero_re_pos {s : ℂ} (hs : riemannXi s = 0) :
    0 < s.re := by
  by_contra h
  exact riemannXi_ne_zero_of_re_nonpos (le_of_not_gt h) hs

/-- Xi zeros are exactly the project-level nontrivial zeta zeros. -/
theorem riemannXi_eq_zero_iff_isNontrivialZero {s : ℂ} :
    riemannXi s = 0 ↔ IsNontrivialZero s := by
  constructor
  · intro hxi
    have hsre : 0 < s.re := riemannXi_zero_re_pos hxi
    have hs1 : s ≠ 1 := by
      intro hs
      subst s
      rw [riemannXi_one] at hxi
      norm_num at hxi
    refine ⟨(riemannXi_eq_zero_iff_riemannZeta_eq_zero hsre hs1).1 hxi, ?_, hs1⟩
    rintro ⟨n, rfl⟩
    norm_num at hsre
  · intro hs
    exact (riemannXi_eq_zero_iff_riemannZeta_eq_zero hs.re_pos hs.ne_one).2
      hs.riemannZeta_eq_zero

/-- The xi-zero formulation of the Riemann hypothesis. -/
def XiCriticalLineCriterion : Prop :=
  ∀ s : ℂ, riemannXi s = 0 → OnCriticalLine s

/-- The xi-zero criterion is exactly equivalent to the project RH statement. -/
theorem statement_iff_xiCriticalLineCriterion :
    Statement ↔ XiCriticalLineCriterion := by
  constructor
  · intro h s hs
    exact h s (riemannXi_eq_zero_iff_isNontrivialZero.mp hs)
  · intro h s hs
    exact h s (riemannXi_eq_zero_iff_isNontrivialZero.mpr hs)

end

end RiemannHypothesisLean
