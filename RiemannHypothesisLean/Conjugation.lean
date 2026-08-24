import RiemannHypothesisLean.Symmetry
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Conjugation of the analytically continued Riemann zeta function

The proof has two stages:

1. on `1 < re(s)`, use the absolutely convergent Dirichlet series and move conjugation through
   the infinite sum term by term;
2. use the identity principle on the connected domain `ℂ \ {1}` to propagate that equality
   through the analytic continuation.

The theorem deliberately excludes `s = 1`, the pole of the mathematical zeta function. Mathlib
assigns a totalized implementation value there, but that value is irrelevant to nontrivial zeros.
-/

open Complex Set Filter

open scoped Topology Real ComplexConjugate

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

/-- The analytically continued zeta function commutes with conjugation away from its pole at
`s = 1`. -/
theorem riemannZeta_conjugation_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    riemannZeta (star s) = star (riemannZeta s) := by
  have hgAnalytic :
      AnalyticOnNhd ℂ (fun z ↦ conj (riemannZeta (conj z))) ({1}ᶜ : Set ℂ) :=
    DifferentiableOn.analyticOnNhd
      (fun z hz ↦
        have hconjNe : conj z ≠ 1 := by
          intro h
          apply hz
          have h' := congrArg (starRingEnd ℂ) h
          simpa using h'
        (differentiableAt_conj_conj_iff.mpr
          (differentiableAt_riemannZeta hconjNe)).differentiableWithinAt)
      isOpen_compl_singleton
  have hseries (z : ℂ) (hz : 1 < z.re) :
      conj (riemannZeta (conj z)) = riemannZeta z := by
    have h := riemannZeta_conjugation_of_one_lt_re (s := z) hz
    simpa using congrArg (starRingEnd ℂ) h
  have heq :
      EqOn (fun z ↦ conj (riemannZeta (conj z))) riemannZeta ({1}ᶜ : Set ℂ) :=
    hgAnalytic.eqOn_of_preconnected_of_eventuallyEq analyticOn_riemannZeta
      (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
      (by norm_num : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ))
      (eventuallyEq_of_mem
        ((isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)) hseries)
  simpa using congrArg (starRingEnd ℂ) (heq hs)

/-- Project-facing form of conjugation compatibility on the natural domain of zeta. -/
theorem riemannZeta_conjugationPoint_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    riemannZeta (conjugationPoint s) = conjugationPoint (riemannZeta s) := by
  simpa [conjugationPoint] using riemannZeta_conjugation_of_ne_one hs

/-- Conjugation transports every project-level nontrivial zeta zero unconditionally. -/
theorem IsNontrivialZero.riemannZeta_conjugationPoint_eq_zero {s : ℂ}
    (hs : IsNontrivialZero s) : riemannZeta (conjugationPoint s) = 0 := by
  rw [riemannZeta_conjugationPoint_of_ne_one hs.ne_one, hs.riemannZeta_eq_zero]
  simp [conjugationPoint]

end

end RiemannHypothesisLean
