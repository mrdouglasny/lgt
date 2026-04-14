# AGENTS.md

## Project Overview

Lattice Gauge Theory formalization in Lean 4. Goal: prove the 2D
Yang-Mills mass gap on the lattice via Doeblin's condition.

## Build

```bash
lake build
```

Dependencies: Mathlib v4.29.0.

## Architecture

Four layers, each building on the previous:

1. **Lattice/** — Discrete DG: cell complex (sites, links, plaquettes),
   discrete forms, exterior derivative d/d*
2. **GaugeField/** — G-valued connections on links, gauge transformations,
   holonomy (Wilson loops)
3. **WilsonAction/** — Wilson plaquette action, gauge invariance
4. **MassGap/** — Transfer matrix, Doeblin's condition, 2D mass gap proof

## Critical Path

1. `CellComplex.lean` — lattice as cell complex
2. `Connection.lean` — G-valued 1-forms on links
3. `PlaquetteAction.lean` — Wilson action S = -β Σ Re Tr U_p
4. `TransferMatrix.lean` — decompose partition function
5. `DoeblinCondition.lean` — heat kernel bound on compact G
6. `MassGap2D.lean` — spectral gap ⟹ mass gap

## Key References

- Chatterjee, "Gauge Theory Lecture Notes" (2026), Ch 15
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
