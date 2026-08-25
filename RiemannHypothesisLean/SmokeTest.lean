import RiemannHypothesisLean

open Complex Set

namespace RiemannHypothesisLean

example : Statement ↔ RiemannHypothesis := statement_iff_mathlib

example (h : Statement) {s : ℂ} (hs : IsNontrivialZero s) : OnCriticalLine s :=
  h s hs

example {s : ℂ} (hs : IsTrivialZero s) : riemannZeta s = 0 :=
  hs.riemannZeta_eq_zero

example {s : ℂ} (hs : IsNontrivialZero s) : 0 < s.re :=
  hs.re_pos

example {s : ℂ} (hs : IsNontrivialZero s) : s.re < 1 :=
  hs.re_lt_one

example {s : ℂ} (hs : IsNontrivialZero s) : InCriticalStrip s :=
  criticalStripLocalization s hs

example : CriticalStripLocalization ↔ PositiveRealPartForNontrivialZeros :=
  criticalStripLocalization_iff_positiveRealPart

example (s : ℂ) : IsCompletedZetaZero (criticalReflection s) ↔ IsCompletedZetaZero s :=
  completedZetaZero_criticalReflection_iff s

example {s : ℂ} (hs : 1 < s.re) :
    riemannZeta (star s) = star (riemannZeta s) :=
  riemannZeta_conjugation_of_one_lt_re hs

example {s : ℂ} (hs : s ≠ 1) :
    riemannZeta (star s) = star (riemannZeta s) :=
  riemannZeta_conjugation_of_ne_one hs

example {s : ℂ} (hs : IsNontrivialZero s) :
    riemannZeta (conjugationPoint s) = 0 :=
  hs.riemannZeta_conjugationPoint_eq_zero

example : Statement ↔ NontrivialZerosFixedByDualSymmetry :=
  statement_iff_nontrivialZerosFixedByDualSymmetry

example {s : ℂ} (hz : riemannZeta s = 0) (hs : InCriticalStrip s) :
    riemannZeta (criticalReflection s) = 0 :=
  riemannZetaZero_criticalReflection hz hs

example {s : ℂ} (hs : IsNontrivialZero s) :
    RiemannZetaZeroOrbit s :=
  hs.riemannZetaZeroOrbit

example : nontrivialZeroSet ⊆ riemannZetaZeros :=
  nontrivialZeroSet_subset_riemannZetaZeros

example {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ nontrivialZeroSet).Finite :=
  hS.inter_nontrivialZeroSet_finite

example : VerifiedOnRegion (∅ : Set ℂ) :=
  verifiedOnRegion_empty

example {S : Set ℂ} (hcomplete : CompleteForNontrivialZeros S) :
    Statement ↔ VerifiedOnRegion S :=
  statement_iff_verifiedOnRegion_of_complete hcomplete

example {s : ℂ} (hs : IsNontrivialZero s) :
    IsNontrivialZero (dualSymmetry s) :=
  hs.dualSymmetry_isNontrivialZero

example : Statement ↔ LeftHalfCriticalStripZeroFree :=
  statement_iff_leftHalfCriticalStripZeroFree

example : Statement ↔ RightHalfCriticalStripZeroFree :=
  statement_iff_rightHalfCriticalStripZeroFree

example : LeftHalfCriticalStripZeroFree ↔ RightHalfCriticalStripZeroFree :=
  leftHalfCriticalStripZeroFree_iff_rightHalfCriticalStripZeroFree

example :
    ExactBridge analyticStatementFormulation geometricDualFixedFormulation :=
  statement_dualFixed_exactBridge

example :
    ExactBridge geometricDualFixedFormulation analyticLeftHalfZeroFreeFormulation :=
  dualFixed_leftHalfZeroFree_exactBridge

example (eta : ℂ → ℂ) (hcompat : EtaZetaZeroCompatibleOnCriticalStrip eta) :
    ExactBridge analyticStatementFormulation (analyticEtaFormulation eta) :=
  statement_eta_exactBridge hcompat

example :
    ExactSupportTranslation miniSourceTheory miniTargetTheory :=
  miniExactSupportTranslation

example :
    fourSupportValue miniSourceTheory .theorem = .trueOnly :=
  mini_theorem_value

example :
    fourSupportValue miniSourceTheory .refutation = .falseOnly :=
  mini_refutation_value

example :
    fourSupportValue miniSourceTheory .conflict = .glut :=
  mini_conflict_value

example :
    fourSupportValue miniSourceTheory .undecided = .gap :=
  mini_undecided_value

example (sentence : MiniSourceSentence) :
    fourSupportValue miniTargetTheory (miniSentenceMap sentence) =
      fourSupportValue miniSourceTheory sentence :=
  miniTranslation_preserves_fourSupportValue sentence

example {Sentence : Type} (theory : BilateralTheory Sentence) :
    ¬AddsInformationBeyondSupportChannels theory (fourSupportValue theory) :=
  fourSupportValue_not_addsInformation theory

example {s : ℂ} (hs : InCriticalStrip s) :
    dirichletEtaFactor s ≠ 0 :=
  dirichletEtaFactor_ne_zero_of_inCriticalStrip hs

example {s : ℂ} (hs : InCriticalStrip s) :
    dirichletEta s = 0 ↔ riemannZeta s = 0 :=
  dirichletEta_eq_zero_iff_riemannZeta_eq_zero_of_inCriticalStrip hs

example :
    EtaZetaZeroCompatibleOnCriticalStrip dirichletEta :=
  dirichletEta_zetaZeroCompatible

example :
    ExactBridge analyticStatementFormulation (analyticEtaFormulation dirichletEta) :=
  statement_dirichletEta_exactBridge

example :
    Statement ↔ EtaCriticalStripCriterion dirichletEta :=
  statement_iff_dirichletEtaCriticalStripCriterion

example : alternatingEtaCoefficient 1 = 1 :=
  alternatingEtaCoefficient_one

example {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable alternatingEtaCoefficient s :=
  alternatingDirichletEtaSeries_summable_of_one_lt_re hs

example {s : ℂ} (hs : 1 < s.re) :
    alternatingDirichletEtaContinuation s = alternatingDirichletEtaSeries s :=
  alternatingDirichletEtaContinuation_eq_series_of_one_lt_re hs

example {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ alternatingDirichletEtaContinuation s :=
  differentiableAt_alternatingDirichletEtaContinuation hs

example :
    ∑ j : ZMod 2, etaResidueCoefficient j = 0 :=
  etaResidueCoefficient_sum

example :
    Differentiable ℂ alternatingDirichletEtaContinuation :=
  differentiable_alternatingDirichletEtaContinuation


example {x : ℝ} (hx : 0 < x) :
    RealAlternatingEtaSeriesConvergesAt x :=
  realAlternatingEtaSeries_converges_of_pos hx


example (x : ℝ) (N : ℕ) :
    complexAlternatingEtaPartialSum (x : ℂ) N =
      (realAlternatingEtaPartialSum x N : ℂ) :=
  complexAlternatingEtaPartialSum_ofReal x N

example {x : ℝ} (hx : 0 < x) :
    ComplexAlternatingEtaSeriesConvergesAt (x : ℂ) :=
  complexAlternatingEtaSeries_converges_of_pos_real hx


example (s : ℂ) (N : ℕ) :
    complexAlternatingEtaPartialSum s (2 * N) =
      complexAlternatingEtaPairedPartialSum s N :=
  complexAlternatingEtaPartialSum_two_mul s N


example {s : ℂ} (hs : s ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (etaCpowKernel s) ((-s) * (t : ℂ) ^ (-s - 1)) t :=
  hasDerivAt_etaCpowKernel hs ht

example {s : ℂ} (hs : s ≠ 0) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (etaCpowKernel s) t :=
  differentiableAt_etaCpowKernel_of_pos hs ht

example (s : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖(-s) * (t : ℂ) ^ (-s - 1)‖ = ‖s‖ * t ^ (-s.re - 1) :=
  norm_etaCpowKernel_derivative s ht

example {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    ‖complexAlternatingEtaPair s n‖ ≤
      ‖s‖ * ((2 * n + 1 : ℕ) : ℝ) ^ (-s.re - 1) :=
  norm_complexAlternatingEtaPair_le hs n

example {s : ℂ} (hs : 0 < s.re) :
    Summable (fun n : ℕ => ‖complexAlternatingEtaPair s n‖) :=
  summable_norm_complexAlternatingEtaPair hs

example {s : ℂ} (hs : 0 < s.re) :
    Summable (complexAlternatingEtaPair s) :=
  summable_complexAlternatingEtaPair hs

example {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (complexAlternatingEtaPairedPartialSum s) Filter.atTop
      (nhds (∑' n : ℕ, complexAlternatingEtaPair s n)) :=
  complexAlternatingEtaPairedPartialSum_tendsto hs

example {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun N => complexAlternatingEtaPartialSum s (2 * N)) Filter.atTop
      (nhds (∑' n : ℕ, complexAlternatingEtaPair s n)) :=
  complexAlternatingEtaPartialSum_even_tendsto hs

example {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun N : ℕ => ((2 * N + 1 : ℕ) : ℂ) ^ (-s))
      Filter.atTop (nhds 0) :=
  complexAlternatingEtaOddRemainder_tendsto_zero hs

example (s : ℂ) (N : ℕ) :
    complexAlternatingEtaPartialSum s (2 * N + 1) =
      complexAlternatingEtaPartialSum s (2 * N) +
        ((2 * N + 1 : ℕ) : ℂ) ^ (-s) :=
  complexAlternatingEtaPartialSum_two_mul_add_one s N

example {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun N => complexAlternatingEtaPartialSum s (2 * N + 1)) Filter.atTop
      (nhds (∑' n : ℕ, complexAlternatingEtaPair s n)) :=
  complexAlternatingEtaPartialSum_odd_tendsto hs

end RiemannHypothesisLean
