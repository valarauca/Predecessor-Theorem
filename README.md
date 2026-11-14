# Predecessor-Theorem

Lean 4 / mathlib formalizations of two papers on balancing dynamics
`q ↦ q + d (e_k − x)` over the zero-sum hyperplane.

- `FGPT/` proves the Fixed-Generator Predecessor Theorem, an exact one-step
  invariance threshold for the zero-sum cube. Paper: `FGPT/paper.pdf`.
- `Carpooling/` proves Optimal Online Weighted Carpooling via a Permutohedral
  Viability Kernel, which builds on FGPT. Paper: `Carpooling/paper.pdf`.

Each file cites the paper result it proves. Neither library uses `sorry`.

## Build

```
lake exe cache get
lake build
lake env lean AxiomCheck.lean
```

`AxiomCheck.lean` prints the axioms each main theorem depends on.
