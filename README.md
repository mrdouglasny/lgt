# lgt — Lattice Gauge Theory in Lean 4

> **Starting here?** See [`docs/mass-gap-roadmap.md`](docs/mass-gap-roadmap.md)
> for a short human-facing summary of the project's goal, current status,
> and the plan to close the remaining sorry.

**Status**: in-progress formalization of the **d ≥ 2 lattice
Yang-Mills mass gap at strong coupling**, via the Dobrushin
uniqueness method (Chatterjee 2026, Ch. 16). The target theorem
`ym_mass_gap_exponential_decay` is stated but not yet proved
— see [docs/mass-gap-completion-plan.md](docs/mass-gap-completion-plan.md)
for the worked-out route.

## Target theorem

`ym_mass_gap_exponential_decay` in `LGT/MassGap/StrongCoupling.lean`.
For U(n) Wilson lattice gauge theory on (ℤ/Nℤ)^d with d ≥ 2,
N ≥ 3, n ≥ 1, coupling β < 1/(32n(d−1)):

    |⟨Re Tr(U_p) · Re Tr(U_q)⟩_c|
        ≤ 32 n² / (1 − α) · α^((latticePlaquetteDist p q − 1) / 2)

where α = dobrushinAlpha(n, d, β) < 1 and `latticePlaquetteDist`
is the periodic L¹ distance between plaquette anchor sites. The
exponent uses `Nat` subtraction and division (saturating at 0 for
close-range plaquettes). The factor of `1/2` is forced by the
geometry: one shared-plaquette influence-graph step displaces a
link anchor by up to 2 L¹ site-units, so `α^k` decay in graph-step
count yields `(log α) / 2` rate in L¹ plaqDist. See the completion
plan for the full derivation.

The theorem is stated for U(n); other compact gauge groups G ⊆ U(n)
require supplying the `HasGaugeTrace` instance.

## What's in the repository

**Infrastructure (proved, axiom-free):** all the upstream plumbing
for the proof — Wilson action, gauge invariance, the YM measure, the
Gibbs specification framework, DLR identity, Dobrushin condition
verification, U(n) instances, and the distance-parameterized
hypothesis-discharging wrapper `ym_mass_gap_strong_coupling`.

**Remaining work (the open sorry):** the geometric reduction that
turns the Dobrushin output (a 16-term boundary-link sum) into
exponential decay in plaquette distance. Phase-by-phase plan:
[docs/mass-gap-completion-plan.md](docs/mass-gap-completion-plan.md).

See [docs/mass-gap-roadmap.md](docs/mass-gap-roadmap.md) for a
two-page human-facing summary,
[docs/mass-gap-proof-outline.md](docs/mass-gap-proof-outline.md)
for the full proof outline, and
[docs/codex-review.txt](docs/codex-review.txt) for independent
review records.

## Status

**`ym_mass_gap_strong_coupling`: zero sorries, zero custom axioms**
(distance-parameterized wrapper).

```
#print axioms ym_mass_gap_strong_coupling
-- propext, Classical.choice, Quot.sound
```

**`ym_mass_gap_exponential_decay`: 1 sorry**, the only one in the
repository. The route to close it is specified in
[docs/mass-gap-completion-plan.md](docs/mass-gap-completion-plan.md):
define a plaq-independent ambient shared-plaquette graph distance
on links, prove the boundary-layer incidence geometry, and
compose with the (already distance-parameterized)
`ym_mass_gap_strong_coupling` wrapper. No upstream changes in
`markov-semigroups` required.

See [docs/mass-gap-proof-outline.md](docs/mass-gap-proof-outline.md)
for the full proof outline.

## Proof architecture

Eight layers (1–7 are the main Dobrushin path; 8 is an independent
bridge to tensor-network models):

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

8. **EKR-Dobrushin bridge** (`Bridge/`) — connects tensor
   renormalization group (TRG) convergence to Dobrushin mass gap.
   For any nearest-neighbor spin model with an EKR-style certificate
   (hat-tensor contraction λ < 1), derives exponential correlation
   decay on the original lattice. Zero sorries, zero axioms.
   Applicable to Ising, XY, O(3) NLSM, Potts, or any model with a
   tensor RG certificate. See `docs/mass-gap-blueprint.md` for details.

Also: 2D mass gap via Doeblin (`MassGap2D.lean`, partially complete).

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
  mass-gap-roadmap.md                 -- short human-facing summary (START HERE)
  mass-gap-completion-plan.md         -- detailed Lean roadmap for the open sorry
  mass-gap-proof-outline.md           -- proof outline
  mass-gap-blueprint.md               -- full math blueprint
  mass-gap-blueprint.tex              -- LaTeX version
  mass-gap-proof.md                   -- 2D Doeblin path notes
  codex-review*.txt                   -- historical review record
```

## Dependencies

- **Lean 4**: `leanprover/lean4:v4.29.0` (pinned in `lean-toolchain`;
  installed automatically by `elan` when you enter the directory).
- **[Mathlib](https://github.com/leanprover-community/mathlib4)** v4.29.0
- **[markov-semigroups](https://github.com/mrdouglasny/markov-semigroups)** —
  Dobrushin uniqueness theory, canonical maximal coupling, covariance
  bounds, Neumann series, single-site disintegration, condKernel wiring.
- **[gaussian-field](https://github.com/mrdouglasny/gaussian-field)** —
  lattice site types.

All resolved via `lakefile.toml`; `lake-manifest.json` pins the
exact commits.

## Building

```bash
git clone https://github.com/mrdouglasny/lgt.git
cd lgt
lake build          # fetches deps on first run via the pinned manifest
```

Full build takes ~15–30 min on first run (Mathlib cache download +
local compilation). Incremental rebuilds are seconds.

To verify the main result builds and the axiom footprint is clean:

```bash
lake build LGT.MassGap.StrongCoupling
```

## Contributing

**New collaborator?** Read in this order:

1. **[`docs/mass-gap-roadmap.md`](docs/mass-gap-roadmap.md)** —
   two-page human summary: goal, status, approach, timeline.
2. **[`docs/mass-gap-completion-plan.md`](docs/mass-gap-completion-plan.md)** —
   detailed Lean roadmap, phase-by-phase, with concrete lemma
   signatures and line-count estimates for each phase.
3. **[`docs/mass-gap-proof-outline.md`](docs/mass-gap-proof-outline.md)** —
   deeper math context for the existing proofs.

**Open work** lives in the completion plan as Phases 1–9. Phases 1
(ZMod periodic distance), 7 (renaming proxy theorems), and 8 (docs
cleanup) are the most independent entry points. Phase 4 (ambient link
graph + connectedness) is the largest and benefits from being taken
on in one piece. The dependency graph in the plan file shows which
phases block which.

**Conventions**: this project follows Mathlib-style naming and layout
(see `CLAUDE.md` in the root for the working-methods summary; detailed
rules in `~/Documents/GitHub/mathlib-ready/docs/` for those with
access). Before writing a new lemma, check whether it exists upstream
or in sibling projects — the `markov-semigroups` and `gaussian-field`
libraries cover most of the Dobrushin / lattice-geometry machinery
already. Axioms are budgeted: see `research-dev/library/lean/AXIOM_MANAGEMENT.md`
for the vetting protocol if a new one is truly needed.

**How to propose a change**: fork, branch, PR to `main`. For anything
non-trivial, open an issue first to coordinate — several of the
phases touch the same files. Commit messages: concise, describe the
*why*, point at the phase number where relevant.

## References

- S. Chatterjee, *Gauge Theory Lecture Notes* (2026), Ch 15–16
- R. L. Dobrushin, "Description of a random field by means of
  conditional probabilities" (1968)
- H.-O. Georgii, *Gibbs Measures and Phase Transitions* (1988), §8
- K. G. Wilson, "Confinement of quarks," Phys. Rev. D 10 (1974) 2445

## Authors

Michael R. Douglas (CMSA, Harvard), with collaborators.

## License

Copyright (c) 2026 Michael R. Douglas. Released under the Apache 2.0 license.
