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

end RiemannHypothesisLean
