import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.SummableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
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

The natural-order alternating series is proved to converge for every `0 < re s`, with its
value named through the absolutely summable paired series. On `1 < re s`, a finite partial-sum
comparison identifies that value with both the naive `LSeries` and the periodic continuation.
The same series calculation gives the classical zeta factorization on `1 < re s`; the identity
theorem identifies the independent periodic continuation with the factorized expression away from
one. A derivative/residue limit then closes the removable point and identifies the independent
continuation globally with `dirichletEta`. Harmonic-number asymptotics independently identify
the natural alternating value at one with `log 2`. Identifying the conditionally convergent
natural value with the continuation on `0 < re s ≤ 1` away from one remains the explicit Gate 8
obligation.
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


/-- The difference `H_(2N) - H_N` tends to `log 2`.

This is the asymptotic identity underlying the value of the natural alternating harmonic
series. It is derived independently from the eta continuation, using Mathlib's checked limit
`H_N - log N → γ`. -/
theorem tendsto_harmonic_two_mul_sub_harmonic :
    Filter.Tendsto
      (fun N : ℕ => (harmonic (2 * N) : ℝ) - (harmonic N : ℝ))
      Filter.atTop (nhds (Real.log 2)) := by
  have hindex :
      Filter.Tendsto (fun N : ℕ => 2 * N) Filter.atTop Filter.atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop b] with N hN
    omega
  have hdiff :=
    (Real.tendsto_harmonic_sub_log.comp hindex).sub
      Real.tendsto_harmonic_sub_log
  have hsum :
      Filter.Tendsto
        (fun N : ℕ =>
          (((harmonic (2 * N) : ℝ) - Real.log (2 * N)) -
            ((harmonic N : ℝ) - Real.log N)) + Real.log 2)
        Filter.atTop (nhds (Real.log 2)) := by
    simpa using hdiff.add
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => Real.log 2) Filter.atTop
          (nhds (Real.log 2)))
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hlog :
      Real.log ((2 * N : ℕ) : ℝ) - Real.log (N : ℝ) = Real.log 2 := by
    rw [← Real.log_div (by positivity) (by positivity)]
    congr 1
    push_cast
    field_simp
  norm_num [Nat.cast_mul] at hlog
  linarith


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

/-- Every even partial sum of the real alternating harmonic series is the harmonic
number difference `H_(2N) - H_N`. -/
theorem realAlternatingEtaPartialSum_one_two_mul (N : ℕ) :
    realAlternatingEtaPartialSum 1 (2 * N) =
      (harmonic (2 * N) : ℝ) - (harmonic N : ℝ) := by
  unfold realAlternatingEtaPartialSum harmonic
  push_cast
  rw [sum_range_two_mul_eq_sum_pairs]
  conv_rhs =>
    lhs
    rw [sum_range_two_mul_eq_sum_pairs]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [(show Even (2 * n) by exact ⟨n, by omega⟩).neg_one_pow]
  rw [(show Odd (2 * n + 1) by exact ⟨n, by omega⟩).neg_one_pow]
  simp [Real.rpow_neg_one]
  field_simp
  ring

/-- The even natural partial sums of the real alternating harmonic series tend to
`log 2`. -/
theorem realAlternatingEtaPartialSum_one_even_tendsto :
    Filter.Tendsto
      (fun N : ℕ => realAlternatingEtaPartialSum 1 (2 * N))
      Filter.atTop (nhds (Real.log 2)) := by
  refine tendsto_harmonic_two_mul_sub_harmonic.congr' ?_
  exact Filter.Eventually.of_forall fun N =>
    (realAlternatingEtaPartialSum_one_two_mul N).symm

/-- The `n`th paired complex eta term. -/
def complexAlternatingEtaPair (s : ℂ) (n : ℕ) : ℂ :=
  ((2 * n + 1 : ℕ) : ℂ) ^ (-s) - ((2 * n + 2 : ℕ) : ℂ) ^ (-s)

/-- The first `N` paired complex eta terms. -/
def complexAlternatingEtaPairedPartialSum (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, complexAlternatingEtaPair s n

/-- The value of the classical eta series in natural order on `0 < re(s)`.

The paired series is absolutely summable there, so its `tsum` gives a canonical name to the
ordinary limit without incorrectly asserting that the unpaired alternating terms are
order-independently summable. -/
def alternatingEtaNaturalValue (s : ℂ) : ℂ :=
  ∑' n : ℕ, complexAlternatingEtaPair s n

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

/-- The odd positive-index terms of Mathlib's `LSeries` are the positive eta terms. -/
theorem alternatingEtaLSeries_term_odd (s : ℂ) (n : ℕ) :
    LSeries.term alternatingEtaCoefficient s (2 * n + 1) =
      ((2 * n + 1 : ℕ) : ℂ) ^ (-s) := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hmod : ((2 * n + 1 : ℕ) : ZMod 2) = 1 := by
    push_cast
    simp [htwo]
  rw [LSeries.term_of_ne_zero (by omega)]
  rw [alternatingEtaCoefficient, hmod, etaResidueCoefficient_one]
  simp [div_eq_mul_inv, ← cpow_neg]

/-- The even positive-index terms of Mathlib's `LSeries` are the negative eta terms. -/
theorem alternatingEtaLSeries_term_even (s : ℂ) (n : ℕ) :
    LSeries.term alternatingEtaCoefficient s (2 * n + 2) =
      -((2 * n + 2 : ℕ) : ℂ) ^ (-s) := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hmod : ((2 * n + 2 : ℕ) : ZMod 2) = 0 := by
    push_cast
    simp [htwo]
  rw [LSeries.term_of_ne_zero (by omega)]
  rw [alternatingEtaCoefficient, hmod, etaResidueCoefficient_zero]
  simp [div_eq_mul_inv, ← cpow_neg]

/-- The first `2N + 1` Mathlib `LSeries` indices (including its zero term) equal the first
`N` paired eta terms. This is a finite identity and uses no convergence theorem. -/
theorem alternatingEtaLSeries_partialSum_two_mul_add_one (s : ℂ) (N : ℕ) :
    (∑ n ∈ Finset.range (2 * N + 1), LSeries.term alternatingEtaCoefficient s n) =
      complexAlternatingEtaPairedPartialSum s N := by
  induction N with
  | zero =>
      simp [complexAlternatingEtaPairedPartialSum]
  | succ N ih =>
      unfold complexAlternatingEtaPairedPartialSum at ih ⊢
      rw [show 2 * (N + 1) + 1 = (2 * N + 1) + 1 + 1 by omega]
      conv_lhs =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ]
      conv_rhs =>
        rw [Finset.sum_range_succ]
      rw [ih, alternatingEtaLSeries_term_odd, alternatingEtaLSeries_term_even]
      simp only [complexAlternatingEtaPair, sub_eq_add_neg]
      ac_rfl

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

/-- The natural eta value is complex differentiable at every point of the right
half-plane.

The paired terms are entire. Around a fixed `s` with positive real part, we work on the open
set where `re(w) > re(s)/2` and `‖w‖ < ‖s‖+1`. The existing paired-term estimate is then
uniformly dominated by a summable p-series. -/
theorem differentiableAt_alternatingEtaNaturalValue {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ alternatingEtaNaturalValue s := by
  let δ : ℝ := s.re / 2
  let M : ℝ := ‖s‖ + 1
  let U : Set ℂ := {w | δ < w.re} ∩ {w | ‖w‖ < M}
  let u : ℕ → ℝ := fun n =>
    M * ((2 * n + 1 : ℕ) : ℝ) ^ (-δ - 1)
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity
  have hUopen : IsOpen U := by
    dsimp [U]
    exact (isOpen_lt continuous_const continuous_re).inter
      (isOpen_lt continuous_norm continuous_const)
  have hsU : s ∈ U := by
    constructor
    · dsimp [δ]
      linarith
    · dsimp [M]
      linarith
  have hu : Summable u := by
    have hpow : Summable (fun n : ℕ => (n : ℝ) ^ (-δ - 1)) :=
      Real.summable_nat_rpow.mpr (by linarith)
    let g : ℕ → ℕ := fun n => 2 * n + 1
    have hg : Function.Injective g := by
      intro m n h
      dsimp [g] at h
      omega
    have hodd : Summable (fun n : ℕ =>
        ((2 * n + 1 : ℕ) : ℝ) ^ (-δ - 1)) := by
      simpa [g, Function.comp_def] using hpow.comp_injective hg
    exact hodd.mul_left M
  have hterm (n : ℕ) :
      DifferentiableOn ℂ (fun w => complexAlternatingEtaPair w n) U := by
    intro w hw
    unfold complexAlternatingEtaPair
    have hodd : (((2 * n + 1 : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast (by omega : (2 * n + 1 : ℕ) ≠ 0)
    have heven : (((2 * n + 2 : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast (by omega : (2 * n + 2 : ℕ) ≠ 0)
    exact
      (((hasDerivAt_neg' w).const_cpow (Or.inl hodd)).sub
        ((hasDerivAt_neg' w).const_cpow (Or.inl heven))).differentiableAt
        |>.differentiableWithinAt
  have hbound (n : ℕ) (w : ℂ) (hw : w ∈ U) :
      ‖complexAlternatingEtaPair w n‖ ≤ u n := by
    have hwre : 0 < w.re := hδ.trans hw.1
    have hbase : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ 2 * n + 1)
    have hpow :
        ((2 * n + 1 : ℕ) : ℝ) ^ (-w.re - 1) ≤
          ((2 * n + 1 : ℕ) : ℝ) ^ (-δ - 1) :=
      Real.rpow_le_rpow_of_exponent_le hbase (by
        have hδw : δ < w.re := hw.1
        linarith)
    calc
      ‖complexAlternatingEtaPair w n‖ ≤
          ‖w‖ * ((2 * n + 1 : ℕ) : ℝ) ^ (-w.re - 1) :=
        norm_complexAlternatingEtaPair_le hwre n
      _ ≤ M * ((2 * n + 1 : ℕ) : ℝ) ^ (-δ - 1) := by
        exact mul_le_mul (le_of_lt hw.2) hpow
          (Real.rpow_nonneg (by positivity) _) hM
      _ = u n := rfl
  have hd :
      DifferentiableOn ℂ
        (fun w : ℂ => ∑' n : ℕ, complexAlternatingEtaPair w n) U :=
    differentiableOn_tsum_of_summable_norm hu hterm hUopen hbound
  simpa [alternatingEtaNaturalValue] using
    hd.differentiableAt (hUopen.mem_nhds hsU)

/-- The natural eta value is holomorphic throughout `0 < re(s)`. -/
theorem differentiableOn_alternatingEtaNaturalValue :
    DifferentiableOn ℂ alternatingEtaNaturalValue {s : ℂ | 0 < s.re} := by
  intro s hs
  exact (differentiableAt_alternatingEtaNaturalValue hs).differentiableWithinAt

/-- The paired eta partial sums converge to the sum of the absolutely summable paired series. -/
theorem complexAlternatingEtaPairedPartialSum_tendsto {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (complexAlternatingEtaPairedPartialSum s) Filter.atTop
      (nhds (alternatingEtaNaturalValue s)) := by
  simpa [complexAlternatingEtaPairedPartialSum] using
    (summable_complexAlternatingEtaPair hs).hasSum.tendsto_sum_nat

/-- The even natural-order eta partial sums converge throughout `0 < re(s)`.

This theorem uses only the exact finite pairing identity and convergence of the paired series; it
does not yet claim convergence of the odd-indexed partial sums. -/
theorem complexAlternatingEtaPartialSum_even_tendsto {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun N => complexAlternatingEtaPartialSum s (2 * N)) Filter.atTop
      (nhds (alternatingEtaNaturalValue s)) := by
  refine (complexAlternatingEtaPairedPartialSum_tendsto hs).congr' ?_
  exact Filter.Eventually.of_forall fun N =>
    (complexAlternatingEtaPartialSum_two_mul s N).symm

/-- The independently defined natural-order eta value at one is `log 2`.

This result comes from the ordinary alternating harmonic partial sums and the harmonic-number
asymptotic, not from the analytic continuation. -/
@[simp]
theorem alternatingEtaNaturalValue_one :
    alternatingEtaNaturalValue 1 = (Real.log 2 : ℂ) := by
  have hcomplex :
      Filter.Tendsto
        (fun N : ℕ => (realAlternatingEtaPartialSum 1 (2 * N) : ℂ))
        Filter.atTop (nhds (Real.log 2 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto (Real.log 2)).comp
      realAlternatingEtaPartialSum_one_even_tendsto
  have heta :
      Filter.Tendsto
        (fun N : ℕ => complexAlternatingEtaPartialSum 1 (2 * N))
        Filter.atTop (nhds (Real.log 2 : ℂ)) := by
    refine hcomplex.congr' ?_
    exact Filter.Eventually.of_forall fun N =>
      (complexAlternatingEtaPartialSum_ofReal 1 (2 * N)).symm
  exact tendsto_nhds_unique
    (complexAlternatingEtaPartialSum_even_tendsto (s := 1) (by norm_num))
    heta

/-- The unpaired positive eta term after the first `2N` terms tends to zero when
`0 < re(s)`. -/
theorem complexAlternatingEtaOddRemainder_tendsto_zero {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun N : ℕ => ((2 * N + 1 : ℕ) : ℂ) ^ (-s)) Filter.atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbase :
      Filter.Tendsto (fun N : ℕ => ((2 * N + 1 : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    have h :
        Filter.Tendsto (fun N : ℕ => (2 : ℝ) * (N : ℝ) + 1)
          Filter.atTop Filter.atTop := by
      apply tendsto_atTop_add_const_right
      exact tendsto_natCast_atTop_atTop.const_mul_atTop zero_lt_two
    simpa using h
  convert (tendsto_rpow_neg_atTop hs).comp hbase using 1
  ext N
  rw [Complex.norm_natCast_cpow_of_pos (by omega)]
  simp

/-- Adding the next term to an even eta partial sum produces the following odd partial sum. -/
theorem complexAlternatingEtaPartialSum_two_mul_add_one (s : ℂ) (N : ℕ) :
    complexAlternatingEtaPartialSum s (2 * N + 1) =
      complexAlternatingEtaPartialSum s (2 * N) +
        ((2 * N + 1 : ℕ) : ℂ) ^ (-s) := by
  unfold complexAlternatingEtaPartialSum
  rw [Finset.sum_range_succ]
  simp

/-- The odd natural-order eta partial sums converge to the same paired-series sum when
`0 < re(s)`. -/
theorem complexAlternatingEtaPartialSum_odd_tendsto {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun N => complexAlternatingEtaPartialSum s (2 * N + 1)) Filter.atTop
      (nhds (alternatingEtaNaturalValue s)) := by
  have h :=
    (complexAlternatingEtaPartialSum_even_tendsto hs).add
      (complexAlternatingEtaOddRemainder_tendsto_zero hs)
  simpa only [add_zero] using h.congr' (Filter.Eventually.of_forall fun N =>
    (complexAlternatingEtaPartialSum_two_mul_add_one s N).symm)

/-- If the even and odd subsequences of a sequence have the same limit, then the full natural
sequence has that limit. -/
theorem tendsto_nat_of_even_odd {α : Type*} [PseudoMetricSpace α] {f : ℕ → α} {a : α}
    (heven : Filter.Tendsto (fun N => f (2 * N)) Filter.atTop (nhds a))
    (hodd : Filter.Tendsto (fun N => f (2 * N + 1)) Filter.atTop (nhds a)) :
    Filter.Tendsto f Filter.atTop (nhds a) := by
  rw [Metric.tendsto_atTop] at heven hodd ⊢
  intro ε hε
  obtain ⟨Ne, hNe⟩ := heven ε hε
  obtain ⟨No, hNo⟩ := hodd ε hε
  refine ⟨2 * max Ne No, ?_⟩
  intro n hn
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · simpa [two_mul] using hNe k (by omega)
  · simpa [two_mul] using hNo k (by omega)

/-- All natural-order complex eta partial sums converge throughout `0 < re(s)`. -/
theorem complexAlternatingEtaPartialSum_tendsto {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (complexAlternatingEtaPartialSum s) Filter.atTop
      (nhds (alternatingEtaNaturalValue s)) :=
  tendsto_nat_of_even_odd
    (complexAlternatingEtaPartialSum_even_tendsto hs)
    (complexAlternatingEtaPartialSum_odd_tendsto hs)

/-- The classical complex alternating eta series converges in its natural order for every
`s` with positive real part. -/
theorem complexAlternatingEtaSeries_converges_of_pos_re {s : ℂ} (hs : 0 < s.re) :
    ComplexAlternatingEtaSeriesConvergesAt s :=
  ⟨alternatingEtaNaturalValue s, complexAlternatingEtaPartialSum_tendsto hs⟩

/-- On the absolute-convergence half-plane, the natural-order eta value agrees with Mathlib's
naive `LSeries`. The proof compares a cofinal sequence of finite partial sums, rather than
misusing `Summable` for the conditionally convergent unpaired series. -/
theorem alternatingEtaNaturalValue_eq_series_of_one_lt_re {s : ℂ}
    (hs : 1 < s.re) :
    alternatingEtaNaturalValue s = alternatingDirichletEtaSeries s := by
  have hindex :
      Filter.Tendsto (fun N : ℕ => 2 * N + 1) Filter.atTop Filter.atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop b] with a ha
    omega
  have hsum :
      LSeriesHasSum alternatingEtaCoefficient s (alternatingDirichletEtaSeries s) := by
    exact (alternatingDirichletEtaSeries_summable_of_one_lt_re hs).LSeriesHasSum
  have hseries :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ n ∈ Finset.range (2 * N + 1),
            LSeries.term alternatingEtaCoefficient s n)
        Filter.atTop (nhds (alternatingDirichletEtaSeries s)) := by
    exact hsum.tendsto_sum_nat.comp hindex
  have hnatural :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ n ∈ Finset.range (2 * N + 1),
            LSeries.term alternatingEtaCoefficient s n)
        Filter.atTop (nhds (alternatingEtaNaturalValue s)) := by
    refine (complexAlternatingEtaPairedPartialSum_tendsto (s := s) (by linarith)).congr' ?_
    exact Filter.Eventually.of_forall fun N =>
      (alternatingEtaLSeries_partialSum_two_mul_add_one s N).symm
  exact tendsto_nhds_unique hnatural hseries

/-- On `1 < re(s)`, the ordinary natural-order eta value also agrees with the independently
constructed periodic analytic continuation. -/
theorem alternatingEtaNaturalValue_eq_continuation_of_one_lt_re {s : ℂ}
    (hs : 1 < s.re) :
    alternatingEtaNaturalValue s = alternatingDirichletEtaContinuation s := by
  calc
    alternatingEtaNaturalValue s = alternatingDirichletEtaSeries s :=
      alternatingEtaNaturalValue_eq_series_of_one_lt_re hs
    _ = alternatingDirichletEtaContinuation s :=
      (alternatingDirichletEtaContinuation_eq_series_of_one_lt_re hs).symm

/-- The natural-order eta value agrees with the independent analytic continuation
throughout the half-plane `0 < re(s)`.

Both sides are holomorphic there. They agree on the nonempty open subdomain `1 < re(s)`, so
the identity theorem propagates the equality across the connected right half-plane. -/
theorem alternatingEtaNaturalValue_eq_continuation_of_pos_re {s : ℂ}
    (hs : 0 < s.re) :
    alternatingEtaNaturalValue s = alternatingDirichletEtaContinuation s := by
  let U : Set ℂ := {z : ℂ | 0 < z.re}
  have hUopen : IsOpen U :=
    isOpen_lt continuous_const continuous_re
  have hfAnalytic :
      AnalyticOnNhd ℂ alternatingEtaNaturalValue U :=
    DifferentiableOn.analyticOnNhd
      differentiableOn_alternatingEtaNaturalValue hUopen
  have hgAnalytic :
      AnalyticOnNhd ℂ alternatingDirichletEtaContinuation U :=
    DifferentiableOn.analyticOnNhd
      differentiable_alternatingDirichletEtaContinuation.differentiableOn hUopen
  have hseries (z : ℂ) (hz : 1 < z.re) :
      alternatingEtaNaturalValue z = alternatingDirichletEtaContinuation z :=
    alternatingEtaNaturalValue_eq_continuation_of_one_lt_re hz
  have heq :
      Set.EqOn alternatingEtaNaturalValue
        alternatingDirichletEtaContinuation U :=
    hfAnalytic.eqOn_of_preconnected_of_eventuallyEq hgAnalytic
      (Convex.isPreconnected (convex_halfSpace_re_gt 0))
      (show (2 : ℂ) ∈ U by
        change 0 < (2 : ℂ).re
        norm_num)
      (eventuallyEq_of_mem
        ((isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num))
        hseries)
  exact heq hs


/-- On the absolute-convergence half-plane, the natural eta value has the classical
factorization `(1 - 2^(1-s)) * ζ(s)`.

The proof splits the absolutely summable shifted zeta series into its odd- and even-denominator
subseries. The even-denominator sum is `2^(-s) * ζ(s)`. -/
theorem alternatingEtaNaturalValue_eq_factor_mul_zeta_of_one_lt_re {s : ℂ}
    (hs : 1 < s.re) :
    alternatingEtaNaturalValue s = dirichletEtaFactor s * riemannZeta s := by
  let a : ℕ → ℂ := fun n => (((n + 1 : ℕ) : ℂ) ^ (-s))
  have ha₀ : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    Complex.summable_one_div_nat_cpow.mpr hs
  have ha : Summable a := by
    have hshift : Summable (fun n : ℕ => 1 / ((n + 1 : ℕ) : ℂ) ^ s) := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        (summable_nat_add_iff 1).2 ha₀
    simpa [a, one_div, ← cpow_neg] using hshift
  have hoddIndex : Function.Injective (fun n : ℕ => 2 * n) := by
    simpa [mul_comm] using (mul_right_injective₀ (two_ne_zero' ℕ))
  have hevenIndex : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    simpa [Function.comp_def, add_comm] using
      ((add_right_injective 1).comp hoddIndex)
  have hodd : Summable (fun n : ℕ => a (2 * n)) :=
    ha.comp_injective hoddIndex
  have heven : Summable (fun n : ℕ => a (2 * n + 1)) :=
    ha.comp_injective hevenIndex
  have hpair (n : ℕ) :
      complexAlternatingEtaPair s n = a (2 * n) - a (2 * n + 1) := by
    simp [a, complexAlternatingEtaPair]
    ring_nf
  have hzeta : (∑' n : ℕ, a n) = riemannZeta s := by
    symm
    simpa [a, one_div, ← cpow_neg] using
      (zeta_eq_tsum_one_div_nat_add_one_cpow hs)
  have hevenTerm (n : ℕ) :
      a (2 * n + 1) = (2 : ℂ) ^ (-s) * a n := by
    dsimp [a]
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega]
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      (natCast_mul_natCast_cpow 2 (n + 1) (-s))
  have hevenSum :
      (∑' n : ℕ, a (2 * n + 1)) = (2 : ℂ) ^ (-s) * riemannZeta s := by
    calc
      (∑' n : ℕ, a (2 * n + 1)) =
          ∑' n : ℕ, (2 : ℂ) ^ (-s) * a n := tsum_congr hevenTerm
      _ = (2 : ℂ) ^ (-s) * ∑' n : ℕ, a n := by rw [tsum_mul_left]
      _ = (2 : ℂ) ^ (-s) * riemannZeta s := by rw [hzeta]
  have hsplit :
      (∑' n : ℕ, a n) =
        (∑' n : ℕ, a (2 * n)) + ∑' n : ℕ, a (2 * n + 1) :=
    (hodd.hasSum.even_add_odd heven.hasSum).tsum_eq
  have htwo :
      (2 : ℂ) * (2 : ℂ) ^ (-s) = (2 : ℂ) ^ (1 - s) := by
    calc
      (2 : ℂ) * (2 : ℂ) ^ (-s) =
          (2 : ℂ) ^ (1 : ℂ) * (2 : ℂ) ^ (-s) := by rw [cpow_one]
      _ = (2 : ℂ) ^ ((1 : ℂ) + (-s)) := by
        rw [← cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
      _ = (2 : ℂ) ^ (1 - s) := by ring_nf
  rw [alternatingEtaNaturalValue]
  calc
    (∑' n : ℕ, complexAlternatingEtaPair s n) =
        ∑' n : ℕ, (a (2 * n) - a (2 * n + 1)) := tsum_congr hpair
    _ = (∑' n : ℕ, a (2 * n)) - ∑' n : ℕ, a (2 * n + 1) :=
      (hodd.hasSum.sub heven.hasSum).tsum_eq
    _ = (∑' n : ℕ, a n) - 2 * ∑' n : ℕ, a (2 * n + 1) := by
      rw [hsplit]
      ring
    _ = riemannZeta s - 2 * ((2 : ℂ) ^ (-s) * riemannZeta s) := by
      rw [hzeta, hevenSum]
    _ = dirichletEtaFactor s * riemannZeta s := by
      rw [← mul_assoc, htwo]
      simp [dirichletEtaFactor]
      ring

/-- On `1 < re(s)`, the independently defined natural eta value agrees with the concrete
factorized Gate 7 eta function. -/
theorem alternatingEtaNaturalValue_eq_dirichletEta_of_one_lt_re {s : ℂ}
    (hs : 1 < s.re) :
    alternatingEtaNaturalValue s = dirichletEta s := by
  have hne : s ≠ 1 := by
    intro h
    subst s
    norm_num at hs
  rw [dirichletEta_of_ne_one hne]
  exact alternatingEtaNaturalValue_eq_factor_mul_zeta_of_one_lt_re hs

/-- The periodic continuation and factorized eta agree on their common series domain. -/
theorem alternatingDirichletEtaContinuation_eq_dirichletEta_of_one_lt_re {s : ℂ}
    (hs : 1 < s.re) :
    alternatingDirichletEtaContinuation s = dirichletEta s := by
  calc
    alternatingDirichletEtaContinuation s = alternatingEtaNaturalValue s :=
      (alternatingEtaNaturalValue_eq_continuation_of_one_lt_re hs).symm
    _ = dirichletEta s :=
      alternatingEtaNaturalValue_eq_dirichletEta_of_one_lt_re hs

/-- Away from the removable point `s = 1`, the independent periodic continuation equals the
classical zeta-factor expression.

The equality is propagated from `1 < re(s)` by the identity theorem on the connected domain
`ℂ \ {1}`. -/
theorem alternatingDirichletEtaContinuation_eq_factor_mul_zeta_of_ne_one {s : ℂ}
    (hs : s ≠ 1) :
    alternatingDirichletEtaContinuation s =
      dirichletEtaFactor s * riemannZeta s := by
  let U : Set ℂ := ({1}ᶜ : Set ℂ)
  have hfactor : Differentiable ℂ dirichletEtaFactor := by
    unfold dirichletEtaFactor
    fun_prop
  have hfAnalytic :
      AnalyticOnNhd ℂ alternatingDirichletEtaContinuation U :=
    DifferentiableOn.analyticOnNhd
      differentiable_alternatingDirichletEtaContinuation.differentiableOn
      isOpen_compl_singleton
  have hgAnalytic :
      AnalyticOnNhd ℂ (fun z =>
        dirichletEtaFactor z * riemannZeta z) U :=
    DifferentiableOn.analyticOnNhd
      (fun z hz =>
        ((hfactor z).mul (differentiableAt_riemannZeta hz)).differentiableWithinAt)
      isOpen_compl_singleton
  have hseries (z : ℂ) (hz : 1 < z.re) :
      alternatingDirichletEtaContinuation z =
        dirichletEtaFactor z * riemannZeta z :=
    alternatingDirichletEtaContinuation_eq_dirichletEta_of_one_lt_re hz
      |>.trans (dirichletEta_of_ne_one (by
        intro h
        subst z
        norm_num at hz))
  have heq :
      Set.EqOn alternatingDirichletEtaContinuation
        (fun z => dirichletEtaFactor z * riemannZeta z) U :=
    hfAnalytic.eqOn_of_preconnected_of_eventuallyEq hgAnalytic
      (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
      (by
        change (2 : ℂ) ≠ 1
        norm_num)
      (eventuallyEq_of_mem
        ((isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num))
        hseries)
  exact heq hs

/-- At the removable point, the eta factor has derivative `log 2`. -/
theorem hasDerivAt_dirichletEtaFactor_one :
    HasDerivAt dirichletEtaFactor (Real.log 2 : ℂ) 1 := by
  have hexponent :
      HasDerivAt (fun s : ℂ => 1 - s) (-1) 1 := by
    simpa only [Pi.sub_apply, id_eq, zero_sub] using
      (hasDerivAt_const (x := (1 : ℂ)) (c := (1 : ℂ))).sub (hasDerivAt_id 1)
  have hpow :
      HasDerivAt (fun s : ℂ => (2 : ℂ) ^ (1 - s))
        (-(Real.log 2 : ℂ)) 1 := by
    have h :=
      hexponent.const_cpow (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
    simpa only [sub_self, cpow_zero, one_mul, mul_neg, mul_one, complexLog_two] using h
  simpa only [dirichletEtaFactor, Pi.sub_apply, zero_sub, sub_neg_eq_add, zero_add] using
    (hasDerivAt_const (x := (1 : ℂ)) (c := (1 : ℂ))).sub hpow

/-- The eta factor divided by `s - 1` tends to `log 2` at the removable point. -/
theorem tendsto_dirichletEtaFactor_div_sub_one :
    Filter.Tendsto
      (fun s : ℂ => dirichletEtaFactor s / (s - 1))
      (nhdsWithin (1 : ℂ) ({1}ᶜ)) (nhds (Real.log 2 : ℂ)) := by
  have h := hasDerivAt_dirichletEtaFactor_one.tendsto_slope
  rw [slope_fun_def_field] at h
  simpa [dirichletEtaFactor] using h

/-- The classical eta product has limit `log 2` at its removable point. -/
theorem tendsto_dirichletEtaFactor_mul_riemannZeta_one :
    Filter.Tendsto
      (fun s : ℂ => dirichletEtaFactor s * riemannZeta s)
      (nhdsWithin (1 : ℂ) ({1}ᶜ)) (nhds (Real.log 2 : ℂ)) := by
  have hproduct :
      Filter.Tendsto
        (fun s : ℂ =>
          (dirichletEtaFactor s / (s - 1)) *
            ((s - 1) * riemannZeta s))
        (nhdsWithin (1 : ℂ) ({1}ᶜ)) (nhds (Real.log 2 : ℂ)) := by
    simpa using
      tendsto_dirichletEtaFactor_div_sub_one.mul riemannZeta_residue_one
  refine hproduct.congr' ?_
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr (by simpa using hs)
  field_simp [hsub]

/-- The independently constructed periodic continuation takes the removable value `log 2`. -/
@[simp]
theorem alternatingDirichletEtaContinuation_one :
    alternatingDirichletEtaContinuation 1 = (Real.log 2 : ℂ) := by
  have hvalue :
      Filter.Tendsto alternatingDirichletEtaContinuation
        (nhdsWithin (1 : ℂ) ({1}ᶜ)) (nhds (alternatingDirichletEtaContinuation 1)) :=
    differentiable_alternatingDirichletEtaContinuation.continuous.continuousWithinAt
  have hlog :
      Filter.Tendsto alternatingDirichletEtaContinuation
        (nhdsWithin (1 : ℂ) ({1}ᶜ)) (nhds (Real.log 2 : ℂ)) := by
    refine tendsto_dirichletEtaFactor_mul_riemannZeta_one.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    exact alternatingDirichletEtaContinuation_eq_factor_mul_zeta_of_ne_one
      (by simpa using hs) |>.symm
  exact tendsto_nhds_unique hvalue hlog

/-- At one, the natural alternating series and the independent periodic continuation agree. -/
theorem alternatingEtaNaturalValue_eq_continuation_one :
    alternatingEtaNaturalValue 1 = alternatingDirichletEtaContinuation 1 := by
  rw [alternatingEtaNaturalValue_one, alternatingDirichletEtaContinuation_one]

/-- The independent periodic continuation agrees globally with the factorized Gate 7 eta
function, including the removable point `s = 1`. -/
theorem alternatingDirichletEtaContinuation_eq_dirichletEta (s : ℂ) :
    alternatingDirichletEtaContinuation s = dirichletEta s := by
  by_cases hs : s = 1
  · subst s
    rw [alternatingDirichletEtaContinuation_one, dirichletEta_one]
  · rw [dirichletEta_of_ne_one hs]
    exact alternatingDirichletEtaContinuation_eq_factor_mul_zeta_of_ne_one hs

/-- Compatibility form of the global continuation theorem under the explicit hypothesis
`s ≠ 1`. -/
theorem alternatingDirichletEtaContinuation_eq_dirichletEta_of_ne_one {s : ℂ}
    (hs : s ≠ 1) :
    alternatingDirichletEtaContinuation s = dirichletEta s := by
  rw [dirichletEta_of_ne_one hs]
  exact alternatingDirichletEtaContinuation_eq_factor_mul_zeta_of_ne_one hs

end

end RiemannHypothesisLean
