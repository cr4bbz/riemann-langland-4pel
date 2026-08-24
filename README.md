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
`RiemannHypothesisLean.Statement ↔ RiemannHypothesis`. Gate 1 connects the project's zero taxonomy
to Mathlib, proves `re(s) < 1` for every project-level nontrivial zero, and checks that full
critical-strip localization now reduces exactly to the still-unproved condition `0 < re(s)`.
This is a dependency reduction, not a proof of RH or of critical-strip localization.

The Gate 2 foundation checks the completed-zeta reflection, identifies the critical line as the
fixed-point set of `s ↦ 1 - conj(s)`, and separates setwise zero symmetry from the stronger
pointwise-fixation claim equivalent to RH. Ordinary zeta is now proved to commute with conjugation
on the half-plane `1 < re(s)`, directly from its Dirichlet series. Extending that identity through
analytic continuation remains an explicit bridge.

The four-point orbit of an ordinary nontrivial zeta zero is now derived conditionally rather than
assumed. The completed functional equation proves its reflection leg inside the critical strip;
the remaining inputs are the positive-real-part condition and global ordinary-zeta conjugation.

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
- `RiemannHypothesisLean/ZeroTaxonomy.lean`: checked zero facts and localization dependency.
- `RiemannHypothesisLean/Symmetry.lean`: checked transformations and symmetry dependency audit.
- `RiemannHypothesisLean/Conjugation.lean`: termwise conjugation on `1 < re(s)`.
- `RiemannHypothesisLean/Orbit.lean`: reflection proof and conditional four-point zero orbit.
- `RiemannHypothesisLean/SmokeTest.lean`: compilation-level interface checks.
- `FORMALIZATION.md`: the exact formal boundary and dependency audit.
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
