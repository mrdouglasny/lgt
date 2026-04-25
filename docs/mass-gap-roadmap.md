# Yang–Mills mass gap in lgt: roadmap

A short human-facing summary of where the project stands and how it
finishes. For the detailed per-step Lean plan, see
[mass-gap-completion-plan.md](mass-gap-completion-plan.md).

## The goal

A Lean 4 proof that, for U(n) Wilson lattice gauge theory on the
periodic torus `(ℤ/Nℤ)^d` with `d ≥ 2` at strong coupling, the
connected 2-point function of plaquette observables decays
exponentially in the geometric plaquette separation — a rigorous
lattice Yang–Mills mass gap.

This is the lattice version of the mass gap, established by the
Dobrushin uniqueness method (Chatterjee 2026, §16.3). It is not the
continuum Clay Millennium problem — the continuum limit is a
separate, harder story.

## Where we are

Roughly 95% of the proof is in place. The Gibbs-specification
framework, the Dobrushin coupling, the covariance bound for
multisite observables, the DLR identity for the YM measure, the
Wilson action, the U(n) instantiation, and the hypothesis
discharges are all formalized with zero sorries.

The genuine exponential-decay statement is stated in
`LGT/MassGap/StrongCoupling.lean` as
`ym_mass_gap_exponential_decay` but the proof is a single `sorry`
— the only one left in the repository. (An earlier intermediate
theorem dressed in a coarse three-valued "link distance" was
removed: the 0/1/2 metric capped at 2, which made the bound
non-decreasing in geometric separation and therefore not a mass
gap. The wrapper that powered it, `ym_mass_gap_strong_coupling`,
is kept and is now distance-parameterized — ready to be
specialized to the genuine ambient shared-plaquette graph
distance once the reduction in the completion plan lands.)

The remaining work replaces the coarse distance with a real graph
distance and proves the combinatorial inequality that converts the
Dobrushin machinery's output into geometric exponential decay.

## The idea

The Dobrushin machinery already delivers a bound of the form

    |connected 2-point function| ≤ 2n² · sum over boundary link pairs
                                      of α^{d(x,y)} / (1 − α)

for any "distance" `d` on links that has (i) the usual metric
properties and (ii) the nearest-neighbor support property "if
`d > 1` then the Dobrushin influence is 0". The coarse distance
we currently plug in satisfies both, but it's too crude to show
exponential decay.

**The fix**: use the shortest-path distance in the graph where
links are adjacent iff they share a lattice plaquette. This
distance automatically has the nearest-neighbor support property,
so the Dobrushin machinery applies unchanged. A short geometric
argument then shows that this graph distance grows linearly with
the L¹ lattice distance between plaquettes (one graph step moves
a link anchor by at most 2 lattice sites), so the `α^{d(x,y)}`
decay in graph steps translates to exponential decay in lattice
distance at rate `(−log α) / 2`.

## What the finished theorem will say

Two companion statements, both in `LGT/MassGap/StrongCoupling.lean`:

**`ym_mass_gap_exponential_decay`** — the algebraic bound:

    |⟨Re Tr U_p · Re Tr U_q⟩_c|
        ≤ 32 n² / (1 − α) · α^((plaqDist(p,q) − 1) / 2)

**`ym_mass_gap_rate_exists`** — the existential rate form
(requires β > 0):

    ∃ m > 0, |⟨Re Tr U_p · Re Tr U_q⟩_c| ≤ C · exp(−m · plaqDist(p,q))

with `m = (−log α) / 2`.

The first is the "concrete" form produced by the proof; the second
is the shape familiar from the physics literature.

## Work breakdown

Nine phases, one of which (Phase 7) can run in parallel with the
rest:

| Phase | What | Size |
|---|---|---|
| 1 | Periodic distance on `ℤ/Nℤ` — a metric | ~50–100 lines |
| 2 | Lift to L¹ metric on sites and plaquettes | ~40 lines |
| 3 | Boundary-layer incidence geometry | ~30 lines |
| 4 | Ambient shared-plaquette graph + connectedness + graph distance | ~150–200 lines |
| 5 | Reverse triangle + boundary-sum aggregation | ~50 lines |
| 5.5 | Small refactor: make an existing wrapper distance-generic | ~30–50 lines |
| 6 | Compose into `ym_mass_gap_exponential_decay` | ~30 lines |
| 6b | Rate corollary `ym_mass_gap_rate_exists` | ~20–30 lines |
| 7 | Rename misleading proxy theorems | parallel |
| 8 | Update user-facing docs | after 6, 6b |
| 9 | Build + axiom check | last |

Phase 4 is the dominant one: it builds a graph metric on the
lattice link set using Mathlib's `SimpleGraph.dist`, and the
connectedness proof on the periodic lattice is verbose (single
graph steps can translate links transverse to their own direction
but not parallel — parallel translation requires a three-step walk).

## Timeline

Calibrated against comparable sister-project work (the upstream
Dobrushin infrastructure, the periodic-distance fragments in
related projects, the existing lattice incidence lemmas):
**5–8 active days, 1–2 weeks wall-clock**. Dominant uncertainties
are the ZMod triangle inequality (Phase 1) and the SimpleGraph
walk constructions over periodic coordinates (Phase 4).

## Dependencies on other libraries

None beyond what's already in `lakefile.toml`: Mathlib, the
sibling `markov-semigroups` library, and `gaussian-field` for
lattice site types. No upstream PRs are required to close the
sorry — all the machinery is already exposed.

## Pointers

- **Detailed Lean plan**: [mass-gap-completion-plan.md](mass-gap-completion-plan.md)
- **Full proof outline**: [mass-gap-proof-outline.md](mass-gap-proof-outline.md)
- **Blueprint with math context**: [mass-gap-blueprint.md](mass-gap-blueprint.md)
- **Current sorry location**: `LGT/MassGap/StrongCoupling.lean:2065`
- **Independent review record**: [codex-review.txt](codex-review.txt),
  [codex-review2.txt](codex-review2.txt),
  [codex-review3.txt](codex-review3.txt)
