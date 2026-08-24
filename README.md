# Riemann–Langland–4PEL

A reproducible Lean 4 research repository with three deliberately separated layers:

1. formalize the Riemann hypothesis and its established mathematical environment;
2. audit genuine correspondence and transfer theorems before calling anything “Langlands-like”;
3. only then test whether 4PEL can represent gaps, gluts, and bridge-stable knowledge across the
   resulting theory network.

## Honest status

This repository **does not prove the Riemann hypothesis**. Mathlib already contains:

- the analytic continuation `riemannZeta : ℂ → ℂ`;
- the functional equation;
- the trivial zeros;
- the discrete zero set `riemannZetaZeros`; and
- the canonical proposition `RiemannHypothesis`.

The foundation exposes these ingredients under explicit names and proves
`RiemannHypothesisLean.Statement ↔ RiemannHypothesis`. Gate 1 now proves the classical
localization `0 < re(s) < 1` for every project-level nontrivial zero. The left boundary follows
by classifying zeros of the real Gamma factor, applying the completed functional equation, and
reflecting a hypothetical left-half-plane zero into Mathlib's zero-free half-plane. This is an
established prerequisite for RH, not the critical-line claim itself.

The Gate 2 foundation checks the completed-zeta reflection, identifies the critical line as the
fixed-point set of `s ↦ 1 - conj(s)`, and separates setwise zero symmetry from the stronger
pointwise-fixation claim equivalent to RH. Ordinary zeta is now proved to commute with conjugation
on its natural analytic domain `s ≠ 1`: first from the Dirichlet series on `1 < re(s)`, then
throughout `ℂ \ {1}` by the identity principle.

Every project-level nontrivial zeta zero now has the checked four-point orbit
`s`, `conj(s)`, `1 - s`, and `1 - conj(s)`. This is setwise symmetry; RH remains the
strictly stronger claim that every such zero is individually fixed by `s ↦ 1 - conj(s)`.

Gate 3 proves that the project-level nontrivial-zero set is discrete and that every compact region
contains only finitely many such zeros. It formally separates certification inside a region from
the independent claim that the region contains every nontrivial zero. A finite verified region
therefore implies RH only together with a proof of global coverage.

Gate 4 proves that RH is equivalent to excluding nontrivial zeros from either open half of the
critical strip. The reverse implications use the checked dual symmetry: applying one one-sided
bound to both `s` and `1 - conj(s)` forces `re(s) = 1 / 2`. This identifies two exact
reduction targets but does not prove either zero-free criterion.

Gate 5 introduces a typed bridge graph. Checked analytic and geometric formulations are connected
only by translations proved in both directions. It isolates a parameterized Dirichlet-eta
zero-compatibility obligation. Spectral and classical positivity rows remain unformalized because
their essential operators, test spaces, and correspondence theorems have not been selected.

Gate 6 tests a minimal 4PEL layer on a finite correspondence before touching the RH graph. Separate
positive and negative derivability, all four support profiles, and channel-preserving translation
are checked. The verdict is deliberately negative on novelty: the induced four-value classifier is
fully determined by the two support channels and therefore adds no further information. A richer
4PEL proposal must pass the documented small-case criterion before integration resumes.

Gate 7 defines a concrete factorized Dirichlet eta function and proves its factor
`1 - 2^(1-s)` nonzero throughout the open critical strip. Eta and Mathlib zeta therefore have
exactly the same zero predicate there, closing the Gate 5 obligation and producing an unconditional
exact bridge between their RH criteria. This is interoperability, not a proof of RH.

Gate 8 begins an independent eta construction from period-two coefficient data. It defines the
naive alternating Dirichlet series through Mathlib's `LSeries` and a separate periodic analytic
continuation through `ZMod.LFunction`. Lean checks summability and equality of these two objects on
`1 < re(s)`, the half-plane of absolute convergence. The two residue coefficients sum to zero,
so the independent continuation is also checked to be entire. Explicit real partial sums are
defined, and Lean's alternating-series test proves their ordinary sequential convergence for every
real `x > 0`, including the non-absolutely convergent range. Extension to complex `s` with
`0 < re(s)` and identification with the factorized Gate 7 eta remain explicit open Gate 8
obligations.

## Reproducible build

The project pins Lean and Mathlib to `v4.30.0`.

```bash
lake exe cache get
lake build
```

The Mathlib cache is an optimization. If the cache helper is unavailable but `lake build`
completes successfully, the project has instead built its dependencies from source.

## Repository map

- `RiemannHypothesisLean/Statement.lean`: zero predicates, critical strip, critical line, and RH.
- `RiemannHypothesisLean/ZeroTaxonomy.lean`: checked zero facts and critical-strip localization.
- `RiemannHypothesisLean/Symmetry.lean`: checked transformations and symmetry dependency audit.
- `RiemannHypothesisLean/Conjugation.lean`: conjugation on `ℂ \ {1}` by analytic continuation.
- `RiemannHypothesisLean/Orbit.lean`: unconditional four-point orbit for nontrivial zeros.
- `RiemannHypothesisLean/Finiteness.lean`: compact finiteness and verification boundary.
- `RiemannHypothesisLean/EquivalentCriteria.lean`: equivalent one-sided zero-free criteria.
- `RiemannHypothesisLean/BridgeAudit.lean`: typed formulation nodes and exact translation edges.
- `RiemannHypothesisLean/DirichletEta.lean`: concrete eta/zeta zero compatibility and RH bridge.
- `RiemannHypothesisLean/AlternatingEta.lean`: independent period-two eta series foundation.
- `RiemannHypothesisLean/FourPELFeasibility.lean`: bilateral support and falsifiable novelty test.
- `RiemannHypothesisLean/SmokeTest.lean`: compilation-level interface checks.
- `FORMALIZATION.md`: the exact formal boundary and dependency audit.
- `BRIDGE_AUDIT.md`: formulation availability, checked graph, and current frontier.
- `FOURPEL_FEASIBILITY.md`: small-case test, negative novelty result, and acceptance criterion.
- `ROADMAP.md`: research gates without pretending that a proof route is known.
- `SCOPE.md`: separation between established mathematics and the later 4PEL research hypothesis.

## Integrity policy

- No `sorry`, `admit`, or project-defined axioms.
- A green build certifies only that Lean accepted the checked declarations.
- Every README status claim must point to a checked declaration or be marked as planned.
- A conditional theorem must display every hypothesis explicitly.

## Windows / PowerShell

Use a short path to avoid Windows path-length problems:

```powershell
New-Item -ItemType Directory -Path C:\Lean -Force | Out-Null
Set-Location C:\Lean
git clone https://github.com/cr4bbz/riemann-langland-4pel.git
Set-Location riemann-langland-4pel
lake exe cache get
lake build
code .
```

Install the **Lean 4** VS Code extension when prompted. If the optional cache helper fails because
no C compiler is available, `lake build` can still build Mathlib from source; this takes longer on
the first run.

## License

MIT
