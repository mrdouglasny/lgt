# lgt — Lattice Gauge Theory in Lean 4

Formal proof of the **d ≥ 3 Yang-Mills mass gap at strong coupling**
for compact gauge groups G ⊆ U(n), with **zero sorry's** and
**zero custom axioms**.

## Main result

**Theorem** (`ym_mass_gap_UN`). For U(n) Wilson lattice gauge theory
on (ℤ/Nℤ)^d with d ≥ 2, n ≥ 1, and coupling β < 1/(32n(d−1)),
the connected 2-point function of plaquette observables decays
exponentially:

    |⟨Re Tr(U_p) · Re Tr(U_q)⟩ − ⟨Re Tr(U_p)⟩⟨Re Tr(U_q)⟩|
        ≤ C(n) · α^dist(p,q) / (1 − α)

where α = dobrushinColumnSum(n, d, β) < 1.

This holds for all compact gauge groups: U(1), SU(N), SO(N), etc.

## Status

**Zero sorry's. Zero custom axioms.** Only standard Lean axioms
(propext, Classical.choice, Quot.sound).

Remaining hypotheses (all provable, not axioms):
- 2 lattice combinatorics facts (shared plaquettes, plaquettes per link)
- 3 Mathlib typeclass instances for U(n) (CompactSpace, SecondCountableTopology, HasHaarProbability)
- 1 condKernel a.e. bound (derivable from the Dobrushin coupling)

See [docs/mass-gap-proof-outline.md](docs/mass-gap-proof-outline.md)
for the full proof outline.

## Proof architecture

Seven layers:

1. **Lattice geometry** (`Lattice/CellComplex.lean`) — sites, links,
   plaquettes on (ℤ/Nℤ)^d with boundary links and shift operations.

2. **Gauge fields** (`GaugeField/`) — G-valued connections on links,
   plaquette holonomy, gauge covariance, U(n) instantiation with
   trace bounds |Re Tr(U)| ≤ n.

3. **Wilson action** (`WilsonAction/`) — plaquette cost, Wilson action
   S(U) = β Σ(n − Re Tr U_p), Boltzmann weight, gauge invariance.

4. **YM measure** (`MassGap/YMMeasure.lean`) — product Haar measure,
   YM probability measure via withDensity, partition function Z > 0,
   ymExpect bridge to integrals.

5. **Gibbs specification** (`Gibbs/`) — YM as a GibbsSpec on link
   lattice, DLR identity (`ymMeasure_isGibbs`), Dobrushin condition
   at strong coupling (`ymDobrushinCondition`).

6. **Dobrushin correlation decay** (in `markov-semigroups`) — canonical
   maximal coupling with Giry measurability, Dobrushin coupling via
   minimum-disagreement + Prokhorov compactness, single-site
   disintegration, multi-site covariance bounds via condKernel
   disintegration, Neumann series exponential decay.

7. **Mass gap assembly** (`MassGap/StrongCoupling.lean`) — discharge
   integrability/measurability from continuity, influence bounds via
   action splitting, link distance, U(n) specialization.

Also: 2D mass gap via Doeblin (`MassGap2D.lean`, partially complete).

8. **EKR-Dobrushin bridge** (`Bridge/`) — connects tensor
   renormalization group (TRG) convergence to Dobrushin mass gap.
   For any nearest-neighbor spin model with an EKR-style certificate
   (hat-tensor contraction λ < 1), derives exponential correlation
   decay on the original lattice. Zero sorries, zero axioms.
   Applicable to Ising, XY, O(3) NLSM, Potts, or any model with a
   tensor RG certificate. See `docs/mass-gap-blueprint.md` for details.

## File structure

```
LGT/
  Lattice/CellComplex.lean           -- cell complex on (ℤ/Nℤ)^d
  GaugeField/
    Connection.lean                   -- connections, holonomy, gauge covariance
    GaugeGroup.lean                   -- HasGaugeTrace typeclass
    UnitaryGroup.lean                 -- U(n) instantiation + trace bounds
  WilsonAction/
    PlaquetteAction.lean              -- Wilson action, Boltzmann weight
    GaugeInvariance.lean              -- S(g·U) = S(U)
  Gibbs/
    YMSpec.lean                       -- YM as GibbsSpec
    YMDobrushin.lean                  -- Dobrushin condition verification
    YMIsGibbs.lean                    -- DLR identity (ymMeasure is Gibbs)
  MassGap/
    YMMeasure.lean                    -- YM probability measure
    DobrushinVerification.lean        -- influence bound algebra
    GaugeFixing.lean                  -- correlation bound wiring
    MassGap3D.lean                    -- d≥3 mass gap theorem
    StrongCoupling.lean               -- final assembly + U(n)
    MassGap2D.lean                    -- 2D mass gap (Doeblin path)
  Bridge/
    TensorGibbsSpec.lean              -- Gibbs spec from tensor network
    TensorDobrushin.lean              -- influence bounds + Dobrushin condition
    ScaleTransfer.lean                -- RG scale transfer (coarse → fine)
    O3MassGap.lean                    -- assembly for O(3) / general models
docs/
  mass-gap-proof-outline.md           -- detailed proof outline
  mass-gap-proof-outline.tex          -- LaTeX version
```

## Dependencies

- [markov-semigroups](https://github.com/mrdouglasny/markov-semigroups) —
  Dobrushin uniqueness theory, canonical maximal coupling, covariance
  bounds, Neumann series, single-site disintegration, condKernel wiring
- [gaussian-field](https://github.com/mrdouglasny/gaussian-field) —
  lattice site types
- [Mathlib](https://github.com/leanprover-community/mathlib4) v4.29.0

## Building

```bash
lake update
lake build
```

## References

- S. Chatterjee, *Gauge Theory Lecture Notes* (2026), Ch 15–16
- R. L. Dobrushin, "Description of a random field by means of
  conditional probabilities" (1968)
- H.-O. Georgii, *Gibbs Measures and Phase Transitions* (1988), §8
- K. G. Wilson, "Confinement of quarks," Phys. Rev. D 10 (1974) 2445

## Author

Michael R. Douglas

## License

Copyright (c) 2026 Michael R. Douglas. Released under the Apache 2.0 license.
