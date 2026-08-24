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

The first project milestone exposes the ingredients under explicit names and proves
`RiemannHypothesisLean.Statement ↔ RiemannHypothesis`. This fixes the exact formal target before
any research direction is chosen.

## Reproducible build

The project pins Lean and Mathlib to `v4.30.0`.

```bash
lake update
lake exe cache get
lake build
```

## Repository map

- `RiemannHypothesisLean/Statement.lean`: zero taxonomy, critical strip, critical line, and RH.
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

After installing Git, VS Code, and Lean's `elan` toolchain manager:

```powershell
git clone https://github.com/cr4bbz/riemann-langland-4pel.git
Set-Location riemann-langland-4pel
lake update
lake exe cache get
lake build
code .
```

Install the **Lean 4** VS Code extension when prompted.

## License

MIT
