import RiemannHypothesisLean.BridgeAudit

/-!
# 4PEL feasibility test

This module tests a minimal bilateral reading of four-valued support before attaching it to the RH
bridge graph. A theory context exposes positive and negative derivability separately. Exact
translations must preserve each channel independently.

A finite correspondence realizes all four support profiles: true-only, false-only, both (glut), and
neither (gap). The final theorem then evaluates a falsifiable novelty criterion. The four-value
classifier is completely determined by its two support channels, so this minimal layer does not add
information beyond the bilateral profile. Any later 4PEL layer must introduce and justify further
observable structure if it is to pass the criterion.
-/

namespace RiemannHypothesisLean

universe u v w

/-- An explicit bilateral theory context over a sentence type. This is an interface for derivability,
not yet a syntax or deductive calculus. -/
structure BilateralTheory (Sentence : Type u) where
  derivesPositive : Sentence → Prop
  derivesNegative : Sentence → Prop

/-- Positive derivability relative to an explicit theory context. -/
def PositiveDerivable {Sentence : Type u}
    (theory : BilateralTheory Sentence) (sentence : Sentence) : Prop :=
  theory.derivesPositive sentence

/-- Negative derivability relative to an explicit theory context. -/
def NegativeDerivable {Sentence : Type u}
    (theory : BilateralTheory Sentence) (sentence : Sentence) : Prop :=
  theory.derivesNegative sentence

/-- The four bilateral support profiles. -/
inductive FourSupportValue where
  | gap
  | trueOnly
  | falseOnly
  | glut
  deriving DecidableEq, Repr

/-- Classify a sentence by its positive and negative derivability channels. -/
noncomputable def fourSupportValue {Sentence : Type u}
    (theory : BilateralTheory Sentence) (sentence : Sentence) : FourSupportValue := by
  classical
  exact if PositiveDerivable theory sentence then
    if NegativeDerivable theory sentence then .glut else .trueOnly
  else
    if NegativeDerivable theory sentence then .falseOnly else .gap

theorem fourSupportValue_eq_glut_iff {Sentence : Type u}
    (theory : BilateralTheory Sentence) (sentence : Sentence) :
    fourSupportValue theory sentence = .glut ↔
      PositiveDerivable theory sentence ∧ NegativeDerivable theory sentence := by
  classical
  by_cases hpositive : PositiveDerivable theory sentence <;>
    by_cases hnegative : NegativeDerivable theory sentence <;>
    simp [fourSupportValue, hpositive, hnegative]

theorem fourSupportValue_eq_trueOnly_iff {Sentence : Type u}
    (theory : BilateralTheory Sentence) (sentence : Sentence) :
    fourSupportValue theory sentence = .trueOnly ↔
      PositiveDerivable theory sentence ∧ ¬NegativeDerivable theory sentence := by
  classical
  by_cases hpositive : PositiveDerivable theory sentence <;>
    by_cases hnegative : NegativeDerivable theory sentence <;>
    simp [fourSupportValue, hpositive, hnegative]

theorem fourSupportValue_eq_falseOnly_iff {Sentence : Type u}
    (theory : BilateralTheory Sentence) (sentence : Sentence) :
    fourSupportValue theory sentence = .falseOnly ↔
      ¬PositiveDerivable theory sentence ∧ NegativeDerivable theory sentence := by
  classical
  by_cases hpositive : PositiveDerivable theory sentence <;>
    by_cases hnegative : NegativeDerivable theory sentence <;>
    simp [fourSupportValue, hpositive, hnegative]

theorem fourSupportValue_eq_gap_iff {Sentence : Type u}
    (theory : BilateralTheory Sentence) (sentence : Sentence) :
    fourSupportValue theory sentence = .gap ↔
      ¬PositiveDerivable theory sentence ∧ ¬NegativeDerivable theory sentence := by
  classical
  by_cases hpositive : PositiveDerivable theory sentence <;>
    by_cases hnegative : NegativeDerivable theory sentence <;>
    simp [fourSupportValue, hpositive, hnegative]

/-- A translation between theories that preserves and reflects each support channel separately. -/
structure ExactSupportTranslation {Source : Type u} {Target : Type v}
    (source : BilateralTheory Source) (target : BilateralTheory Target) where
  map : Source → Target
  positive_iff : ∀ sentence,
    PositiveDerivable source sentence ↔ PositiveDerivable target (map sentence)
  negative_iff : ∀ sentence,
    NegativeDerivable source sentence ↔ NegativeDerivable target (map sentence)

namespace ExactSupportTranslation

/-- Identity preserves both support channels. -/
def refl {Sentence : Type u} (theory : BilateralTheory Sentence) :
    ExactSupportTranslation theory theory where
  map := id
  positive_iff := fun _ ↦ Iff.rfl
  negative_iff := fun _ ↦ Iff.rfl

/-- Channel-preserving translations compose. -/
def trans {Source : Type u} {Middle : Type v} {Target : Type w}
    {source : BilateralTheory Source} {middle : BilateralTheory Middle}
    {target : BilateralTheory Target}
    (first : ExactSupportTranslation source middle)
    (second : ExactSupportTranslation middle target) :
    ExactSupportTranslation source target where
  map := second.map ∘ first.map
  positive_iff := fun sentence ↦
    (first.positive_iff sentence).trans (second.positive_iff (first.map sentence))
  negative_iff := fun sentence ↦
    (first.negative_iff sentence).trans (second.negative_iff (first.map sentence))

/-- Preserving both channels preserves the induced four-valued classification. -/
theorem fourSupportValue_map {Source : Type u} {Target : Type v}
    {source : BilateralTheory Source} {target : BilateralTheory Target}
    (translation : ExactSupportTranslation source target) (sentence : Source) :
    fourSupportValue target (translation.map sentence) =
      fourSupportValue source sentence := by
  classical
  unfold fourSupportValue
  rw [← translation.positive_iff sentence, ← translation.negative_iff sentence]

end ExactSupportTranslation

/-- Four source sentences realizing the four possible support profiles. -/
inductive MiniSourceSentence where
  | theorem
  | refutation
  | conflict
  | undecided
  deriving DecidableEq, Repr

/-- A differently named target vocabulary for the same four profiles. -/
inductive MiniTargetSentence where
  | affirmed
  | denied
  | contested
  | openQuestion
  deriving DecidableEq, Repr

/-- The source theory's positive and negative support channels. -/
def miniSourceTheory : BilateralTheory MiniSourceSentence where
  derivesPositive sentence :=
    sentence = .theorem ∨ sentence = .conflict
  derivesNegative sentence :=
    sentence = .refutation ∨ sentence = .conflict

/-- The target theory's corresponding support channels. -/
def miniTargetTheory : BilateralTheory MiniTargetSentence where
  derivesPositive sentence :=
    sentence = .affirmed ∨ sentence = .contested
  derivesNegative sentence :=
    sentence = .denied ∨ sentence = .contested

/-- Vocabulary translation for the finite correspondence. -/
def miniSentenceMap : MiniSourceSentence → MiniTargetSentence
  | .theorem => .affirmed
  | .refutation => .denied
  | .conflict => .contested
  | .undecided => .openQuestion

/-- The finite correspondence preserves positive and negative support independently. -/
def miniExactSupportTranslation :
    ExactSupportTranslation miniSourceTheory miniTargetTheory where
  map := miniSentenceMap
  positive_iff := by
    intro sentence
    cases sentence <;>
      simp [PositiveDerivable, miniSourceTheory, miniTargetTheory, miniSentenceMap]
  negative_iff := by
    intro sentence
    cases sentence <;>
      simp [NegativeDerivable, miniSourceTheory, miniTargetTheory, miniSentenceMap]

theorem mini_theorem_value :
    fourSupportValue miniSourceTheory .theorem = .trueOnly := by
  classical
  simp [fourSupportValue, PositiveDerivable, NegativeDerivable, miniSourceTheory]

theorem mini_refutation_value :
    fourSupportValue miniSourceTheory .refutation = .falseOnly := by
  classical
  simp [fourSupportValue, PositiveDerivable, NegativeDerivable, miniSourceTheory]

theorem mini_conflict_value :
    fourSupportValue miniSourceTheory .conflict = .glut := by
  classical
  simp [fourSupportValue, PositiveDerivable, NegativeDerivable, miniSourceTheory]

theorem mini_undecided_value :
    fourSupportValue miniSourceTheory .undecided = .gap := by
  classical
  simp [fourSupportValue, PositiveDerivable, NegativeDerivable, miniSourceTheory]

/-- The finite translation preserves the classification for every source sentence. -/
theorem miniTranslation_preserves_fourSupportValue (sentence : MiniSourceSentence) :
    fourSupportValue miniTargetTheory (miniSentenceMap sentence) =
      fourSupportValue miniSourceTheory sentence :=
  miniExactSupportTranslation.fourSupportValue_map sentence

/-- A falsifiable novelty criterion for an observation layered over bilateral support.

It passes when two sentences have equivalent positive and negative derivability profiles but the
new observation can still distinguish them. -/
def AddsInformationBeyondSupportChannels {Sentence : Type u} {Observation : Type v}
    (theory : BilateralTheory Sentence) (observe : Sentence → Observation) : Prop :=
  ∃ first second : Sentence,
    (PositiveDerivable theory first ↔ PositiveDerivable theory second) ∧
    (NegativeDerivable theory first ↔ NegativeDerivable theory second) ∧
    observe first ≠ observe second

/-- The four-value classifier is determined entirely by the two support channels. -/
theorem fourSupportValue_eq_of_channels_iff {Sentence : Type u}
    {theory : BilateralTheory Sentence} {first second : Sentence}
    (hpositive :
      PositiveDerivable theory first ↔ PositiveDerivable theory second)
    (hnegative :
      NegativeDerivable theory first ↔ NegativeDerivable theory second) :
    fourSupportValue theory first = fourSupportValue theory second := by
  classical
  unfold fourSupportValue
  rw [hpositive, hnegative]

/-- Negative feasibility result: the minimal four-value classifier adds no information beyond the
positive/negative support pair from which it is computed. -/
theorem fourSupportValue_not_addsInformation {Sentence : Type u}
    (theory : BilateralTheory Sentence) :
    ¬AddsInformationBeyondSupportChannels theory (fourSupportValue theory) := by
  rintro ⟨first, second, hpositive, hnegative, hne⟩
  exact hne (fourSupportValue_eq_of_channels_iff hpositive hnegative)

end RiemannHypothesisLean
