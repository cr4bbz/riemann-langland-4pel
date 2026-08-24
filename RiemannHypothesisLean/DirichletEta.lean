import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannHypothesisLean.BridgeAudit

/-!
# Concrete Dirichlet eta interoperability

This module defines the analytically continued Dirichlet eta function by its standard zeta-factor
formula away from the pole and by the removable value `log 2` at `s = 1`.

For the RH bridge only the open critical strip matters. There the factor
`1 - 2 ^ (1 - s)` is proved nonzero by comparing norms: since `re(s) < 1`, the norm of
`2 ^ (1 - s)` is strictly greater than one. Eta and zeta therefore have exactly the same zeros
throughout the strip, discharging the explicit interoperability obligation from `BridgeAudit`.
-/

open Complex

namespace RiemannHypothesisLean

noncomputable section

/-- The zeta factor appearing in the analytic continuation of Dirichlet eta. -/
def dirichletEtaFactor (s : ℂ) : ℂ :=
  1 - (2 : ℂ) ^ (1 - s)

/-- The analytically continued Dirichlet eta function.

At the removable point `s = 1` we use the standard value `log 2`; elsewhere we use
`(1 - 2^(1-s)) * ζ(s)`. -/
def dirichletEta (s : ℂ) : ℂ :=
  if s = 1 then (Real.log 2 : ℂ)
  else dirichletEtaFactor s * riemannZeta s

@[simp]
theorem dirichletEta_one :
    dirichletEta 1 = (Real.log 2 : ℂ) := by
  simp [dirichletEta]

theorem dirichletEta_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    dirichletEta s = dirichletEtaFactor s * riemannZeta s := by
  simp [dirichletEta, hs]

/-- A point in the open critical strip is not the pole location. -/
theorem InCriticalStrip.ne_one {s : ℂ} (hs : InCriticalStrip s) : s ≠ 1 := by
  intro hone
  have hre := congrArg Complex.re hone
  norm_num at hre
  linarith [hs.2]

/-- The complex logarithm of the positive real number two is the real logarithm embedded in
`ℂ`. -/
theorem complexLog_two :
    Complex.log (2 : ℂ) = (Real.log 2 : ℂ) := by
  simp

/-- The real part of the exponent defining `2^(1-s)` is positive in the critical strip. -/
theorem log_two_mul_one_sub_re_pos {s : ℂ} (hs : InCriticalStrip s) :
    0 < (Complex.log (2 : ℂ) * (1 - s)).re := by
  rw [complexLog_two]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, sub_re, one_re]
  exact mul_pos (Real.log_pos (by norm_num)) (sub_pos.mpr hs.2)

/-- The eta factor does not vanish anywhere in the open critical strip. -/
theorem dirichletEtaFactor_ne_zero_of_inCriticalStrip {s : ℂ}
    (hs : InCriticalStrip s) :
    dirichletEtaFactor s ≠ 0 := by
  intro hfactor
  have hpow : (2 : ℂ) ^ (1 - s) = 1 := by
    exact (sub_eq_zero.mp hfactor).symm
  rw [Complex.cpow_def_of_ne_zero (by norm_num)] at hpow
  have hnorm := congrArg norm hpow
  rw [Complex.norm_exp] at hnorm
  norm_num at hnorm
  have hre_zero : (Complex.log (2 : ℂ) * (1 - s)).re = 0 := by
    simpa using hnorm
  exact (ne_of_gt (log_two_mul_one_sub_re_pos hs)) hre_zero

/-- Eta has its zeta-factor form throughout the open critical strip. -/
theorem dirichletEta_eq_factor_mul_zeta_of_inCriticalStrip {s : ℂ}
    (hs : InCriticalStrip s) :
    dirichletEta s = dirichletEtaFactor s * riemannZeta s :=
  dirichletEta_of_ne_one hs.ne_one

/-- Eta and zeta have exactly the same zeros in the open critical strip. -/
theorem dirichletEta_eq_zero_iff_riemannZeta_eq_zero_of_inCriticalStrip {s : ℂ}
    (hs : InCriticalStrip s) :
    dirichletEta s = 0 ↔ riemannZeta s = 0 := by
  rw [dirichletEta_eq_factor_mul_zeta_of_inCriticalStrip hs]
  constructor
  · intro hzero
    rcases mul_eq_zero.mp hzero with hfactor | hzeta
    · exact (dirichletEtaFactor_ne_zero_of_inCriticalStrip hs hfactor).elim
    · exact hzeta
  · intro hzeta
    rw [hzeta, mul_zero]

/-- The concrete eta function discharges the Gate 5 zero-set interoperability obligation. -/
theorem dirichletEta_zetaZeroCompatible :
    EtaZetaZeroCompatibleOnCriticalStrip dirichletEta := by
  intro s hs
  exact dirichletEta_eq_zero_iff_riemannZeta_eq_zero_of_inCriticalStrip hs

/-- The canonical zeta RH statement and the concrete eta criterion now have an unconditional exact
bridge. -/
theorem statement_dirichletEta_exactBridge :
    ExactBridge analyticStatementFormulation (analyticEtaFormulation dirichletEta) :=
  statement_eta_exactBridge dirichletEta_zetaZeroCompatible

/-- Project-facing equivalence between zeta RH and the concrete Dirichlet eta criterion. -/
theorem statement_iff_dirichletEtaCriticalStripCriterion :
    Statement ↔ EtaCriticalStripCriterion dirichletEta :=
  statement_dirichletEta_exactBridge.claim_iff

end

end RiemannHypothesisLean
