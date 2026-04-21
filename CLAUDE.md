# CLAUDE.md

## Project Overview

Lattice Gauge Theory formalization in Lean 4. Proves the d ≥ 3
Yang-Mills mass gap at strong coupling for compact gauge groups
G ⊆ U(n) via the Dobrushin uniqueness method.

**Main result:** `ym_mass_gap_UN` in `LGT/MassGap/StrongCoupling.lean` —
exponential decay of the connected 2-point function of Wilson plaquette
observables on (ℤ/Nℤ)^d for U(n) gauge theory at β < 1/(32n(d-1)).
Zero sorries, zero custom axioms.

## Build

```bash
lake build
```

Dependencies: Mathlib v4.29.0, MarkovSemigroups, GaussianField.

## Architecture

Seven layers:

1. **Lattice/** — Cell complex: sites, links, plaquettes on (ℤ/Nℤ)^d
2. **GaugeField/** — G-valued connections, gauge transformations,
   holonomy, U(n) instantiation
3. **WilsonAction/** — Plaquette action S = β Σ(n - Re Tr U_p),
   gauge invariance
4. **MassGap/YMMeasure** — Product Haar, Boltzmann weight, YM measure,
   partition function, connected 2-point function
5. **Gibbs/** — YM as a GibbsSpec, DLR identity (YMIsGibbs),
   Dobrushin condition verification (YMDobrushin)
6. **MassGap/MassGap3D** — d ≥ 3 mass gap via Dobrushin correlation
   decay from markov-semigroups
7. **MassGap/StrongCoupling** — Final assembly: discharge all
   measure-theoretic hypotheses, influence bounds, U(n) specialization

Also: 2D mass gap path via Doeblin (MassGap2D, partially complete).

## Key References

- Chatterjee, "Gauge Theory Lecture Notes" (2026), Ch 15-16
- Dobrushin (1968), conditional probabilities and regularity
- Georgii, "Gibbs Measures and Phase Transitions" (1988), §8
- Wilson, Phys. Rev. D 10 (1974), 2445

## Lean 4 Working Methods

### Build-First Workflow
Always build before and after changes. Use `lake build`.

### Key Conventions
- `G` is always a compact Lie group (with Haar measure)
- `d` is the spatial dimension, `N` is the lattice size
- Lattice is (ℤ/Nℤ)ᵈ (periodic boundary conditions)
- Links carry group elements (parallel transport)
- Plaquettes carry holonomies (curvature)
