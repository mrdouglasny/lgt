# Yang–Mills mass gap in lgt: roadmap

A short human-facing summary of where the project stands. The proof is
**complete**; this page records what the result says, how it was
closed, and where the pieces live. For the math see
[mass-gap-blueprint.md](mass-gap-blueprint.md); for the step-by-step
record of the geometric closure see
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

## Status: complete

The proof is finished as of PR #2 (commit `a2b76c9`): **zero sorries,
zero project axioms** across the whole repository. Both headline
statements are proven in `LGT/MassGap/StrongCoupling.lean`, and
`#print axioms` on a fresh build shows only the Lean foundationals
(`propext`, `Classical.choice`, `Quot.sound`) — no project axioms and
no extra Mathlib analytic axioms.

An earlier draft stated the central theorem as a single `sorry`
guarded by a coarse three-valued "link distance" (a 0/1/2 metric
capped at 2, which was non-decreasing in geometric separation and
therefore *not* a mass gap). That coarse distance has been replaced by
a genuine graph distance and the combinatorial reduction described
below, which closed the last `sorry`.

## What the theorems say

Both live in `LGT/MassGap/StrongCoupling.lean`, for U(n) at
`β < 1/(32 n (d−1))` (equivalently `β < 1/(4 n · maxNeighbors d)`),
with `α = dobrushinAlpha n d β < 1` and
`d(p,q) = latticePlaquetteDist d N p q` the periodic L¹ distance
between plaquette anchor sites.

**`ym_mass_gap_exponential_decay`** — the algebraic bound:

    |⟨Re Tr U_p · Re Tr U_q⟩_c|
        ≤ 32 n² / (1 − α) · α^((d(p,q) − 1) / 2)

**`ym_mass_gap_rate_exists`** — the existential rate form (requires
`β > 0`):

    ∃ m > 0, |⟨Re Tr U_p · Re Tr U_q⟩_c|
                ≤ 32 n² / (α (1 − α)) · exp(−m · d(p,q))

with `m = (−log α) / 2`.

The first is the "concrete" form produced by the proof; the second is
the shape familiar from the physics literature.

## How it was closed

The Dobrushin machinery delivers a bound of the form

    |connected 2-point function| ≤ 2n² · sum over boundary link pairs
                                      of α^{d(x,y)} / (1 − α)

for any "distance" `d` on links with (i) the usual metric properties
and (ii) the nearest-neighbor support property "if `d > 1` then the
Dobrushin influence is 0". The coarse capped distance satisfied both
but was too crude to show exponential decay.

**The fix that was implemented**: the shortest-path distance in the
graph where links are adjacent iff they share a lattice plaquette
(`ambientLinkGraph` / `linkGraphDist` in
`LGT/Lattice/LatticeDistance.lean`). This distance has the
nearest-neighbor support property automatically (`linkGraphDist_support`),
so the Dobrushin machinery applies unchanged. A geometric argument then
shows the graph distance grows linearly with the L¹ lattice distance
between plaquettes (one graph step moves a link anchor by at most 2
lattice sites; parallel translation costs a three-step walk), so the
`α^{d(x,y)}` decay in graph steps becomes exponential decay in lattice
distance at rate `(−log α) / 2`.

Pieces added for the closure:

- periodic-distance machinery — `ZMod.periodicDist`, `latticeSiteDist`,
  `latticePlaquetteDist` (`LatticeDistance.lean`);
- the ambient shared-plaquette link graph, its connectedness, and
  `linkGraphDist` with `linkGraphDist_support`;
- `boundary_sum_bound` — the 16-term boundary-link sum bounded by
  `16 · α^((d−1)/2) / (1 − α)`;
- composition into the two headline theorems above.

## Dependencies on other libraries

None beyond what's already in `lakefile.toml`: Mathlib v4.29.0, the
sibling `markov-semigroups` library (Dobrushin uniqueness, maximal
coupling, covariance bounds), and `gaussian-field` (lattice site
types). No upstream PRs were required.

## Pointers

- **Main theorems**: `LGT/MassGap/StrongCoupling.lean` —
  `ym_mass_gap_exponential_decay`, `ym_mass_gap_rate_exists`
- **Lattice geometry**: `LGT/Lattice/LatticeDistance.lean`
- **Detailed closure record**: [mass-gap-completion-plan.md](mass-gap-completion-plan.md)
- **Full proof outline**: [mass-gap-proof-outline.md](mass-gap-proof-outline.md)
- **Blueprint with math context**: [mass-gap-blueprint.md](mass-gap-blueprint.md)
- **Independent review record**: [codex-review.txt](codex-review.txt),
  [codex-review2.txt](codex-review2.txt),
  [codex-review3.txt](codex-review3.txt)
