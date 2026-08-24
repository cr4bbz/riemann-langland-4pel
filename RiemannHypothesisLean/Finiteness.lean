import RiemannHypothesisLean.Orbit

/-!
# Finiteness and the computation boundary

Mathlib proves that the full zeta-zero set is discrete and has finite intersection with every
compact set. This module transfers those facts to the project's nontrivial-zero predicate.

It also separates two propositions that numerical discussions often conflate:

* `VerifiedOnRegion S`: every nontrivial zero found inside `S` lies on the critical line;
* `CompleteForNontrivialZeros S`: every nontrivial zero lies inside `S`.

A compact-region certificate provides a finite mathematical verification problem. It implies the
universal Riemann-hypothesis statement only when accompanied by the separate completeness proof.
-/

open Set

namespace RiemannHypothesisLean

/-- The set of project-level nontrivial zeros. -/
def nontrivialZeroSet : Set ℂ :=
  {s | IsNontrivialZero s}

@[simp]
theorem mem_nontrivialZeroSet {s : ℂ} :
    s ∈ nontrivialZeroSet ↔ IsNontrivialZero s :=
  Iff.rfl

/-- Project-level nontrivial zeros are contained in Mathlib's full zeta-zero set. -/
theorem nontrivialZeroSet_subset_riemannZetaZeros :
    nontrivialZeroSet ⊆ riemannZetaZeros := by
  intro s hs
  exact mem_riemannZetaZeros.mpr hs.riemannZeta_eq_zero

/-- The project-level nontrivial-zero set is discrete. -/
theorem isDiscrete_nontrivialZeroSet : IsDiscrete nontrivialZeroSet :=
  isDiscrete_riemannZetaZeros.mono nontrivialZeroSet_subset_riemannZetaZeros

/-- Every compact region contains only finitely many project-level nontrivial zeros. -/
theorem IsCompact.inter_nontrivialZeroSet_finite {S : Set ℂ} (hS : IsCompact S) :
    (S ∩ nontrivialZeroSet).Finite := by
  apply hS.inter_riemannZetaZeros_finite.subset
  intro s hs
  exact ⟨hs.1, nontrivialZeroSet_subset_riemannZetaZeros hs.2⟩

/-- Every nontrivial zero inside `S` has been certified to lie on the critical line. -/
def VerifiedOnRegion (S : Set ℂ) : Prop :=
  ∀ s : ℂ, s ∈ S → IsNontrivialZero s → OnCriticalLine s

/-- The region `S` contains every project-level nontrivial zero. -/
def CompleteForNontrivialZeros (S : Set ℂ) : Prop :=
  nontrivialZeroSet ⊆ S

/-- A proof-level compact-region check.

The compactness field makes the in-region nontrivial-zero set finite. The verification field says
that all such zeros lie on the critical line. Neither field asserts that the region is globally
complete. -/
structure CertifiedCompactCheck (S : Set ℂ) : Prop where
  region_compact : IsCompact S
  verified : VerifiedOnRegion S

/-- A certified compact check concerns only finitely many nontrivial zeros. -/
theorem CertifiedCompactCheck.nontrivialZeros_finite {S : Set ℂ}
    (h : CertifiedCompactCheck S) :
    (S ∩ nontrivialZeroSet).Finite :=
  IsCompact.inter_nontrivialZeroSet_finite h.region_compact

/-- RH verifies every region, compact or otherwise. -/
theorem verifiedOnRegion_of_statement (h : Statement) (S : Set ℂ) :
    VerifiedOnRegion S := by
  intro s _ hs
  exact h s hs

/-- A region verification yields RH only when the region is proved globally complete. -/
theorem statement_of_verifiedOnRegion_of_complete {S : Set ℂ}
    (hverified : VerifiedOnRegion S)
    (hcomplete : CompleteForNontrivialZeros S) : Statement := by
  intro s hs
  exact hverified s (hcomplete hs) hs

/-- Under an explicit completeness proof, checking a region is equivalent to RH. -/
theorem statement_iff_verifiedOnRegion_of_complete {S : Set ℂ}
    (hcomplete : CompleteForNontrivialZeros S) :
    Statement ↔ VerifiedOnRegion S := by
  constructor
  · intro h
    exact verifiedOnRegion_of_statement h S
  · intro h
    exact statement_of_verifiedOnRegion_of_complete h hcomplete

/-- The empty region is vacuously verified, demonstrating that verification without coverage can
carry no information about the universal statement. -/
theorem verifiedOnRegion_empty : VerifiedOnRegion (∅ : Set ℂ) := by
  intro s hs
  simp at hs

/-- A certified compact check proves RH if a separate theorem establishes global coverage. -/
theorem CertifiedCompactCheck.statement_of_complete {S : Set ℂ}
    (h : CertifiedCompactCheck S)
    (hcomplete : CompleteForNontrivialZeros S) : Statement :=
  statement_of_verifiedOnRegion_of_complete h.verified hcomplete

end RiemannHypothesisLean
