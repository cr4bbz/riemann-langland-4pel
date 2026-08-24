import Mathlib.NumberTheory.LSeries.ZMod
import RiemannHypothesisLean.DirichletEta

/-!
# Alternating Dirichlet eta series

This module starts an independent construction of Dirichlet eta from its alternating
Dirichlet series. The coefficient sequence is encoded by the two residue classes modulo two:
positive on odd positive integers and negative on even positive integers.

Mathlib's `LSeries` is the naive Dirichlet series and `ZMod.LFunction` is the analytic
continuation attached to a periodic coefficient function. The checked first bridge identifies
these constructions on the half-plane of absolute convergence `1 < re s`.

The stronger classical statement that the alternating series itself converges for every
`0 < re s`, and its eventual identification with `dirichletEta`, are deliberately left as
subsequent Gate 8 obligations.
-/

open Complex

namespace RiemannHypothesisLean

noncomputable section

/-- The eta sign attached to a residue class modulo two: `-1` on the even class and
`1` on the odd class. -/
def etaResidueCoefficient (j : ZMod 2) : ℂ :=
  if j = 0 then -1 else 1

@[simp]
theorem etaResidueCoefficient_zero :
    etaResidueCoefficient 0 = -1 := by
  simp [etaResidueCoefficient]

@[simp]
theorem etaResidueCoefficient_one :
    etaResidueCoefficient 1 = 1 := by
  norm_num [etaResidueCoefficient]

/-- The periodic coefficient sequence used by the eta Dirichlet series.

The value at zero is irrelevant to `LSeries`; positive indices have signs
`+1, -1, +1, -1, ...`. -/
def alternatingEtaCoefficient (n : ℕ) : ℂ :=
  etaResidueCoefficient (n : ZMod 2)

@[simp]
theorem alternatingEtaCoefficient_one :
    alternatingEtaCoefficient 1 = 1 := by
  norm_num [alternatingEtaCoefficient]

/-- The naive alternating Dirichlet eta series represented using Mathlib's `LSeries`.
Its positive-index terms are
`1 / 1^s - 1 / 2^s + 1 / 3^s - 1 / 4^s + ...`. -/
def alternatingDirichletEtaSeries (s : ℂ) : ℂ :=
  LSeries alternatingEtaCoefficient s

/-- The independently constructed analytic continuation associated to the same period-two
coefficient data. This definition does not mention `riemannZeta` or `dirichletEta`. -/
def alternatingDirichletEtaContinuation (s : ℂ) : ℂ :=
  ZMod.LFunction etaResidueCoefficient s

/-- The alternating eta Dirichlet series is summable on its half-plane of absolute convergence. -/
theorem alternatingDirichletEtaSeries_summable_of_one_lt_re {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesSummable alternatingEtaCoefficient s := by
  simpa [alternatingEtaCoefficient] using
    (ZMod.LSeriesSummable_of_one_lt_re etaResidueCoefficient hs)

/-- On `1 < re s`, the independent periodic analytic continuation agrees with the actual
alternating Dirichlet series. -/
theorem alternatingDirichletEtaContinuation_eq_series_of_one_lt_re {s : ℂ}
    (hs : 1 < s.re) :
    alternatingDirichletEtaContinuation s = alternatingDirichletEtaSeries s := by
  simpa [alternatingDirichletEtaContinuation, alternatingDirichletEtaSeries,
    alternatingEtaCoefficient] using
    (ZMod.LFunction_eq_LSeries etaResidueCoefficient hs)

/-- Away from the possible pole location, the periodic continuation is complex differentiable. -/
theorem differentiableAt_alternatingDirichletEtaContinuation {s : ℂ}
    (hs : s ≠ 1) :
    DifferentiableAt ℂ alternatingDirichletEtaContinuation s := by
  exact ZMod.differentiableAt_LFunction etaResidueCoefficient s (Or.inl hs)

end

end RiemannHypothesisLean
