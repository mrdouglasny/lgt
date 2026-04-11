# lgt — Lattice Gauge Theory in Lean 4

Formalization of lattice gauge theory, from discrete differential
geometry through the Wilson plaquette action to the 2D Yang-Mills
mass gap proof.

## Goal

Prove the **mass gap for 2D Yang-Mills theory** on the lattice,
following Chatterjee (2026) Ch 15. The proof uses Doeblin's condition
for Markov chains on compact Lie groups — a probabilistic argument
that is well-suited for formalization.

## Architecture

```
LGT/
  Lattice/                    -- Layer 1: Discrete differential geometry
    CellComplex.lean          -- Z^d as a cell complex (sites, links, plaquettes)
    DiscreteForms.lean        -- 0-forms (site fields), 1-forms (link fields), 2-forms
    DiscreteExteriorDerivative.lean  -- Discrete d, d*, Hodge star, Laplacian

  GaugeField/                 -- Layer 2: Gauge fields on the lattice
    Connection.lean           -- G-valued 1-forms (parallel transport on links)
    GaugeTransformation.lean  -- G-valued 0-forms acting on connections
    Holonomy.lean             -- Ordered product around loops (Wilson loops)

  WilsonAction/               -- Layer 3: The Wilson plaquette action
    PlaquetteAction.lean      -- S(U) = -β Σ_p Re Tr U_p
    WilsonLoop.lean           -- Wilson loop observables W(γ) = Tr U_γ
    GaugeInvariance.lean      -- S and W are gauge-invariant

  MassGap/                    -- Layer 4: The 2D mass gap
    TransferMatrix.lean       -- Transfer matrix for 2D lattice gauge theory
    DoeblinCondition.lean     -- Doeblin's condition for Markov chains on G
    MassGap2D.lean            -- Theorem: 2D YM has a mass gap (Chatterjee Thm 15.7.1)

  ContinuumLimit/             -- Layer 5 (future): a → 0 limit
    ...
```

## The 2D mass gap proof (outline)

Following Chatterjee §15.7:

1. **Lattice setup**: gauge field = G-valued 1-form on Z² lattice,
   Wilson action S(U) = -β Σ Re Tr U_p (sum over plaquettes)

2. **Transfer matrix**: decompose the partition function as a product
   of transfer matrices T, one per time slice

3. **Doeblin's condition**: the heat kernel on G satisfies
   p_t(g) ≥ c > 0 for all g ∈ G, t > 0 (G is compact)

4. **Spectral gap**: Doeblin's condition implies the transfer matrix
   has a spectral gap: λ₂/λ₁ < 1 - δ for some δ > 0

5. **Mass gap**: spectral gap of T implies exponential decay of
   correlations, which is the mass gap: ⟨W(γ₁)W(γ₂)⟩ ~ e^{-m·d}

## Dependencies

- [Mathlib](https://github.com/leanprover-community/mathlib4) v4.29.0

## References

- Chatterjee, "Gauge Theory Lecture Notes" (2026), Ch 15-16
- Wilson, "Confinement of quarks," Phys. Rev. D 10 (1974)
- Migdal, "Recursion equations in gauge theories," JETP 42 (1975)
- Chatterjee, "The leading term of the Yang-Mills free energy,"
  J. Funct. Anal. 271 (2016), arXiv:1602.01222

## Author

Michael R. Douglas

## License

Copyright (c) 2026 Michael R. Douglas. Released under the Apache 2.0 license.
