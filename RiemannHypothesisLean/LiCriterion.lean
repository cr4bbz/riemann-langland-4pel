import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import RiemannHypothesisLean.RiemannXi

/-!
# Li coefficients and their positivity criterion

For `n : ℕ`, this module defines the zero-based coefficient `liCoefficient n`
corresponding to the classical Li coefficient `λ_(n+1)`:

`λ_(n+1) = 1 / n! * d^(n+1)/ds^(n+1) [s^n log ξ(s)] at s = 1`.

The principal complex logarithm is legitimate locally at one because `ξ(1)=1/2`
lies in the slit plane. We prove that every derivative kernel is analytic there.

The positivity predicate records both facts required by the classical statement:
a coefficient must be real and its real value must be nonnegative. The equivalence
between this positivity criterion and RH is named as a proof obligation, not assumed
or proved in this foundation step.
-/

open Complex

namespace RiemannHypothesisLean

noncomputable section

/-- The function whose `(n+1)`st derivative at one defines the Li coefficient
`λ_(n+1)`. -/
def liDerivativeKernel (n : ℕ) (s : ℂ) : ℂ :=
  s ^ n * log (riemannXi s)

/-- The principal logarithm of xi is analytic at one. -/
theorem analyticAt_log_riemannXi_one :
    AnalyticAt ℂ (fun s : ℂ => log (riemannXi s)) 1 := by
  apply differentiable_riemannXi.analyticAt.clog
  rw [riemannXi_one]
  norm_num [mem_slitPlane_iff]

/-- Every Li derivative kernel is analytic at one. -/
theorem analyticAt_liDerivativeKernel_one (n : ℕ) :
    AnalyticAt ℂ (liDerivativeKernel n) 1 := by
  have hpow : AnalyticAt ℂ (fun s : ℂ => s ^ n) 1 :=
    (analyticAt_id : AnalyticAt ℂ (fun s : ℂ => s) 1).pow n
  exact hpow.mul analyticAt_log_riemannXi_one

/-- The zero-based Li coefficient: index `n` represents the classical
coefficient `λ_(n+1)`. -/
def liCoefficient (n : ℕ) : ℂ :=
  iteratedDeriv (n + 1) (liDerivativeKernel n) 1 / (n.factorial : ℂ)

/-- The factorial normalization in every Li coefficient is nonzero. -/
theorem liCoefficient_factorial_ne_zero (n : ℕ) :
    (n.factorial : ℂ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero n

/-- A complex number represents a nonnegative real exactly when its imaginary
part vanishes and its real part is nonnegative. -/
def IsNonnegativeReal (z : ℂ) : Prop :=
  z.im = 0 ∧ 0 ≤ z.re

@[simp]
theorem isNonnegativeReal_ofReal_iff (x : ℝ) :
    IsNonnegativeReal (x : ℂ) ↔ 0 ≤ x := by
  simp [IsNonnegativeReal]

/-- The classical Li positivity statement, using the zero-based coefficient
sequence `λ_(n+1)`. -/
def LiPositivityCriterion : Prop :=
  ∀ n : ℕ, IsNonnegativeReal (liCoefficient n)

/-- The exact missing bridge at this checkpoint.

Proving this proposition would establish Li's criterion relative to the already
checked xi/RH equivalence. It is a definition of the obligation, not an axiom or
a theorem. -/
def LiCriterionBridge : Prop :=
  Statement ↔ LiPositivityCriterion

end

end RiemannHypothesisLean
