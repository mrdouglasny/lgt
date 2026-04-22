# lgt — Lattice Gauge Theory in Lean 4

Formal proof of **Dobrushin contraction for the d ≥ 2 lattice
Yang-Mills theory at strong coupling**. Establishes a connected
2-point function bound with contraction factor α < 1. The
reduction to exponential decay in geometric plaquette distance
is stated (`ym_mass_gap_exponential_decay`) but not yet proved.

## Main result

**Theorem** (`ym_mass_gap_UN`). For U(n) Wilson lattice gauge theory
on (ℤ/Nℤ)^d with d ≥ 2, N ≥ 3, n ≥ 1, and coupling β < 1/(32n(d−1)),
the connected 2-point function of plaquette observables is bounded:

    |⟨Re Tr(U_p) · Re Tr(U_q)⟩ − ⟨Re Tr(U_p)⟩⟨Re Tr(U_q)⟩|
        ≤ 2n² · ∑_{x ∈ ∂p} ∑_{y ∈ ∂q} α^{d(x,y)} / (1 − α)

where α = dobrushinColumnSum(n, d, β) < 1, and d(x,y) is a coarse
link distance (currently 0, 1, or 2 based on plaquette-sharing).

**What this proves**: Dobrushin contraction — the connected 2-point
function is bounded by α < 1 raised to a graph distance power.

**What remains**: replacing the coarse `ymLinkDist` (which caps at 2)
with true lattice graph distance and proving the 16-term boundary sum
≤ C · α^{dist(p,q)}. This is the step from "Dobrushin contraction"
to "exponential decay in geometric distance" (mass gap).

The theorem is stated for U(n); other compact gauge groups G ⊆ U(n)
require supplying the `HasGaugeTrace` instance.

**Mass gap target** (`ym_mass_gap_exponential_decay`, **not yet proved**).
The Dobrushin bound above would imply exponential decay in plaquette
distance if the 16-term boundary sum can be bounded by C · α^{dist(p,q)}:

    |⟨Re Tr(U_p) · Re Tr(U_q)⟩_c| ≤ C(n) · e^{−m · dist(p,q)}

with m = −log α > 0 (the mass gap) and dist = periodic L₁ distance
between plaquette sites. This is stated as a sorry in `StrongCoupling.lean`.
The reduction requires showing that link graph distance ≥ L₁ site
distance minus a constant — a combinatorial lattice geometry fact that
has not yet been formalized.

See [docs/mass-gap-proof-outline.md](docs/mass-gap-proof-outline.md)
for the full proof outline, and [docs/codex-review.txt](docs/codex-review.txt)
for an independent review.

## Status

**`ym_mass_gap_UN`: zero sorry's, zero custom axioms.**

```
#print axioms ym_mass_gap_UN
-- propext, Classical.choice, Quot.sound
```

Only the three standard Lean axioms. This theorem proves the Dobrushin
contraction bound (16-term sum with coarse link distance).

**`ym_mass_gap_exponential_decay`: 1 sorry** (the combinatorial
reduction from coarse distance to geometric L₁ plaquette distance).

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
