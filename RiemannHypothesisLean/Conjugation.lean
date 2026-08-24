import RiemannHypothesisLean.Symmetry

/-!
# Conjugation on the Dirichlet-series half-plane

This module proves that the Riemann zeta function commutes with complex conjugation on the
half-plane `1 < re(s)`. In that region Mathlib identifies zeta with its absolutely convergent
Dirichlet series, so conjugation can be moved through the infinite sum and checked term by term.

Extending the identity to the analytically continued function is intentionally left as a separate
step.
-/

open Complex

open scoped ComplexConjugate

namespace RiemannHypothesisLean

noncomputable section

/-- On the half-plane of absolute convergence, zeta commutes with complex conjugation. -/
theorem riemannZeta_conjugation_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta (star s) = star (riemannZeta s) := by
  have hseries : conj (riemannZeta (conj s)) = riemannZeta s := by
    rw [zeta_eq_tsum_one_div_nat_cpow (by rwa [conj_re]), conj_tsum,
      zeta_eq_tsum_one_div_nat_cpow hs]
    exact tsum_congr fun n ↦ by
      rw [map_div₀, map_one,
        ← conj_cpow _ _ (by rw [natCast_arg]; positivity), conj_natCast]
  simpa using congrArg (starRingEnd ℂ) hseries

/-- Project-facing version of `riemannZeta_conjugation_of_one_lt_re`. -/
theorem riemannZeta_conjugationPoint_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    riemannZeta (conjugationPoint s) = conjugationPoint (riemannZeta s) := by
  simpa [conjugationPoint] using riemannZeta_conjugation_of_one_lt_re hs

end

end RiemannHypothesisLean
