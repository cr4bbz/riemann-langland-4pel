import Mathlib.NumberTheory.LSeries.RiemannZeta

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
  exact differentiable_const.mul
    (differentiable_const.add
      ((differentiable_id.mul (differentiable_id.sub differentiable_const)).mul
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

end

end RiemannHypothesisLean
