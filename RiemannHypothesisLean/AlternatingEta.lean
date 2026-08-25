import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
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

open Complex Filter

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

/-- The two eta residue coefficients have mean zero. This is the cancellation that removes the
only possible pole of the periodic L-function at `s = 1`. -/
theorem etaResidueCoefficient_sum :
    ∑ j : ZMod 2, etaResidueCoefficient j = 0 := by
  change (∑ j : Fin 2, if j = 0 then (-1 : ℂ) else 1) = 0
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  norm_num [Fin.ext_iff]

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

/-- The zero coefficient mean removes the possible pole at one, so the independent periodic
continuation is entire. -/
theorem differentiable_alternatingDirichletEtaContinuation :
    Differentiable ℂ alternatingDirichletEtaContinuation := by
  simpa [alternatingDirichletEtaContinuation] using
    (ZMod.differentiable_LFunction_of_sum_zero etaResidueCoefficient_sum)


/-- The first `N` partial sums of the classical real alternating eta series at exponent `x`.

This explicit sequence models ordinary convergence in the natural order. It is intentionally
separate from Mathlib's stronger, order-independent `Summable` predicate. -/
def realAlternatingEtaPartialSum (x : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * ((n : ℝ) + 1) ^ (-x)

/-- Ordinary sequential convergence of the real alternating eta series at exponent `x`. -/
def RealAlternatingEtaSeriesConvergesAt (x : ℝ) : Prop :=
  ∃ l : ℝ, Filter.Tendsto (realAlternatingEtaPartialSum x) Filter.atTop (nhds l)

/-- The real alternating eta partial sums converge for every positive exponent.

This is the Leibniz alternating-series criterion. In particular, it includes the conditionally
convergent range `0 < x ≤ 1` without asserting Mathlib's stronger `Summable` predicate. -/
theorem realAlternatingEtaSeries_converges_of_pos {x : ℝ} (hx : 0 < x) :
    RealAlternatingEtaSeriesConvergesAt x := by
  unfold RealAlternatingEtaSeriesConvergesAt realAlternatingEtaPartialSum
  apply Antitone.tendsto_alternating_series_of_tendsto_zero
  · intro m n hmn
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · exact_mod_cast Nat.add_le_add_right hmn 1
    · linarith
  · exact (tendsto_rpow_neg_atTop hx).comp (by
      apply tendsto_atTop_add_const_right
      exact tendsto_natCast_atTop_atTop)


/-- The first `N` natural-order partial sums of the classical complex eta series. -/
def complexAlternatingEtaPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, (-1 : ℂ) ^ n * ((n : ℂ) + 1) ^ (-s)

/-- Ordinary sequential convergence of the complex alternating eta series at `s`. -/
def ComplexAlternatingEtaSeriesConvergesAt (s : ℂ) : Prop :=
  ∃ l : ℂ, Filter.Tendsto (complexAlternatingEtaPartialSum s) Filter.atTop (nhds l)

/-- A complex eta term at a real exponent is the complex embedding of the corresponding
real eta term. -/
theorem complexAlternatingEtaTerm_ofReal (x : ℝ) (n : ℕ) :
    (-1 : ℂ) ^ n * ((n : ℂ) + 1) ^ (-(x : ℂ)) =
      (((-1 : ℝ) ^ n * ((n : ℝ) + 1) ^ (-x) : ℝ) : ℂ) := by
  rw [Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_cpow (show 0 ≤ (n : ℝ) + 1 by positivity)]
  norm_num

/-- The complex and real partial-sum constructions agree on the embedded real axis. -/
theorem complexAlternatingEtaPartialSum_ofReal (x : ℝ) (N : ℕ) :
    complexAlternatingEtaPartialSum (x : ℂ) N =
      (realAlternatingEtaPartialSum x N : ℂ) := by
  unfold complexAlternatingEtaPartialSum realAlternatingEtaPartialSum
  calc
    (∑ n ∈ Finset.range N, (-1 : ℂ) ^ n * ((n : ℂ) + 1) ^ (-(x : ℂ))) =
        ∑ n ∈ Finset.range N,
          (((-1 : ℝ) ^ n * ((n : ℝ) + 1) ^ (-x) : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact complexAlternatingEtaTerm_ofReal x n
    _ = ((∑ n ∈ Finset.range N,
          (-1 : ℝ) ^ n * ((n : ℝ) + 1) ^ (-x) : ℝ) : ℂ) := by
      norm_cast

/-- The complex partial sums converge at every positive point of the embedded real axis. -/
theorem complexAlternatingEtaSeries_converges_of_pos_real {x : ℝ} (hx : 0 < x) :
    ComplexAlternatingEtaSeriesConvergesAt (x : ℂ) := by
  obtain ⟨l, hl⟩ := realAlternatingEtaSeries_converges_of_pos hx
  refine ⟨(l : ℂ), ?_⟩
  refine ((Complex.continuous_ofReal.tendsto l).comp hl).congr' ?_
  exact Filter.Eventually.of_forall fun N ↦
    (complexAlternatingEtaPartialSum_ofReal x N).symm


/-- A finite sum with an even number of terms is the sum of its consecutive pairs. -/
theorem sum_range_two_mul_eq_sum_pairs {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (N : ℕ) :
    ∑ n ∈ Finset.range (2 * N), f n =
      ∑ n ∈ Finset.range N, (f (2 * n) + f (2 * n + 1)) := by
  induction N with
  | zero =>
      simp
  | succ N ih =>
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, ih]
      simp [add_assoc]

/-- The `n`th paired complex eta term. -/
def complexAlternatingEtaPair (s : ℂ) (n : ℕ) : ℂ :=
  ((2 * n + 1 : ℕ) : ℂ) ^ (-s) - ((2 * n + 2 : ℕ) : ℂ) ^ (-s)

/-- The first `N` paired complex eta terms. -/
def complexAlternatingEtaPairedPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, complexAlternatingEtaPair s n

/-- Pairing does not change the even natural-order eta partial sums. -/
theorem complexAlternatingEtaPartialSum_two_mul (s : ℂ) (N : ℕ) :
    complexAlternatingEtaPartialSum s (2 * N) =
      complexAlternatingEtaPairedPartialSum s N := by
  unfold complexAlternatingEtaPartialSum complexAlternatingEtaPairedPartialSum
  rw [sum_range_two_mul_eq_sum_pairs]
  apply Finset.sum_congr rfl
  intro n hn
  simp [complexAlternatingEtaPair]
  rw [(show Odd (2 * n + 1) by exact ⟨n, by omega⟩).neg_one_pow]
  ring_nf

/-- The real-variable complex power kernel used to estimate consecutive eta terms. -/
def etaCpowKernel (s : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (-s)

/-- The derivative of the eta power kernel at a nonzero real input.

The later paired-term estimate only uses this result under `0 < re(s)`, which in particular
implies `s ≠ 0`. -/
theorem hasDerivAt_etaCpowKernel {s : ℂ} (hs : s ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (etaCpowKernel s) ((-s) * (t : ℂ) ^ (-s - 1)) t := by
  simpa [etaCpowKernel] using
    (hasDerivAt_ofReal_cpow_const ht (neg_ne_zero.mpr hs))

/-- The eta power kernel is real differentiable at every positive input. -/
theorem differentiableAt_etaCpowKernel_of_pos {s : ℂ} (hs : s ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (etaCpowKernel s) t :=
  (hasDerivAt_etaCpowKernel hs ht.ne').differentiableAt

/-- Exact norm of the derivative expression for the eta power kernel on the positive real axis. -/
theorem norm_etaCpowKernel_derivative (s : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(-s) * (t : ℂ) ^ (-s - 1)‖ = ‖s‖ * t ^ (-s.re - 1) := by
  rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos ht]
  simp

/-- A single paired eta term is bounded by the first point of its unit interval raised to
`-re(s)-1`. This is the pointwise estimate needed before comparison with a convergent
p-series. -/
theorem norm_complexAlternatingEtaPair_le {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖complexAlternatingEtaPair s n‖ ≤
      ‖s‖ * ((2 * n + 1 : ℕ) : ℝ) ^ (-s.re - 1) := by
  let a : ℝ := ((2 * n + 1 : ℕ) : ℝ)
  let b : ℝ := ((2 * n + 2 : ℕ) : ℝ)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hab : a ≤ b := by
    dsimp [a, b]
    exact_mod_cast (by omega : 2 * n + 1 ≤ 2 * n + 2)
  have hs0 : s ≠ 0 := by
    intro h
    subst s
    norm_num at hs
  have hdiff : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ (etaCpowKernel s) t := by
    intro t ht
    exact differentiableAt_etaCpowKernel_of_pos hs0 (ha.trans_le ht.1)
  have hbound : ∀ t ∈ Set.Icc a b,
      ‖deriv (etaCpowKernel s) t‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
    intro t ht
    have htpos : 0 < t := ha.trans_le ht.1
    rw [(hasDerivAt_etaCpowKernel (s := s) hs0 htpos.ne').deriv,
      norm_etaCpowKernel_derivative s htpos]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg s)
    exact Real.rpow_le_rpow_of_nonpos ha ht.1 (by linarith)
  have hmv :
      ‖etaCpowKernel s a - etaCpowKernel s b‖ ≤
        (‖s‖ * a ^ (-s.re - 1)) * ‖a - b‖ :=
    (convex_Icc a b).norm_image_sub_le_of_norm_deriv_le hdiff hbound
      ⟨hab, le_rfl⟩ ⟨le_rfl, hab⟩
  have hstep : ‖a - b‖ = 1 := by
    have : a - b = -1 := by
      dsimp [a, b]
      push_cast
      ring
    rw [this]
    norm_num
  rw [hstep, mul_one] at hmv
  simpa [complexAlternatingEtaPair, etaCpowKernel, a, b] using hmv

/-- The norms of the paired eta terms are summable throughout the half-plane `0 < re(s)`.

The comparison series is the odd-index subsequence of the real p-series with exponent
`-re(s)-1 < -1`. -/
theorem summable_norm_complexAlternatingEtaPair {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ => ‖complexAlternatingEtaPair s n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n =>
    norm_complexAlternatingEtaPair_le hs n) ?_
  have hpow : Summable (fun n : ℕ => (n : ℝ) ^ (-s.re - 1)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  let g : ℕ → ℕ := fun n => 2 * n + 1
  have hg : Function.Injective g := by
    intro m n h
    dsimp [g] at h
    omega
  have hodd : Summable (fun n : ℕ =>
      ((2 * n + 1 : ℕ) : ℝ) ^ (-s.re - 1)) := by
    simpa [g, Function.comp_def] using hpow.comp_injective hg
  exact hodd.mul_left ‖s‖

/-- The paired complex eta series is absolutely summable when `0 < re(s)`. -/
theorem summable_complexAlternatingEtaPair {s : ℂ} (hs : 0 < s.re) :
    Summable (complexAlternatingEtaPair s) := by
  rw [← summable_norm_iff]
  exact summable_norm_complexAlternatingEtaPair hs

/-- The paired eta partial sums converge to the sum of the absolutely summable paired series. -/
theorem complexAlternatingEtaPairedPartialSum_tendsto {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (complexAlternatingEtaPairedPartialSum s) Filter.atTop
      (nhds (∑' n : ℕ, complexAlternatingEtaPair s n)) := by
  simpa [complexAlternatingEtaPairedPartialSum] using
    (summable_complexAlternatingEtaPair hs).hasSum.tendsto_sum_nat

/-- The even natural-order eta partial sums converge throughout `0 < re(s)`.

This theorem uses only the exact finite pairing identity and convergence of the paired series; it
does not yet claim convergence of the odd-indexed partial sums. -/
theorem complexAlternatingEtaPartialSum_even_tendsto {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun N => complexAlternatingEtaPartialSum s (2 * N)) Filter.atTop
      (nhds (∑' n : ℕ, complexAlternatingEtaPair s n)) := by
  refine (complexAlternatingEtaPairedPartialSum_tendsto hs).congr' ?_
  exact Filter.Eventually.of_forall fun N =>
    (complexAlternatingEtaPartialSum_two_mul s N).symm

end

end RiemannHypothesisLean
