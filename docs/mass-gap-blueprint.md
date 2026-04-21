# Blueprint: Lattice Yang-Mills Mass Gap at Strong Coupling

## What we prove

For any compact gauge group G ⊆ U(n) on the periodic lattice
(ℤ/Nℤ)^d with d ≥ 2 and small enough coupling β, the correlation
between Wilson plaquette observables at distant plaquettes p, q
decays exponentially:

$$|\langle \mathrm{Re\,Tr}(U_p) \cdot \mathrm{Re\,Tr}(U_q)\rangle
- \langle \mathrm{Re\,Tr}(U_p)\rangle \langle \mathrm{Re\,Tr}(U_q)\rangle|
\leq C \cdot \alpha^{\mathrm{dist}(p,q)}$$

This is the "mass gap" — the connected correlation function decays
exponentially, with a decay rate (the mass) that is uniform in the
lattice size N.

## Part 1: The lattice

We work on the d-dimensional periodic lattice (ℤ/Nℤ)^d. The basic
geometric objects are:

- **Sites**: points x ∈ (ℤ/Nℤ)^d.
- **Links**: oriented edges ℓ = (site, direction). Each link
  connects a site to its neighbor in one of d coordinate directions.
- **Plaquettes**: oriented unit squares p = (site, dir₁ < dir₂).
  Each plaquette has 4 boundary links forming a square.

## Part 2: Gauge fields and the Wilson action

A **gauge configuration** assigns a group element U(ℓ) ∈ G to each
link. Physically, U(ℓ) represents the parallel transport along ℓ.

The **holonomy** around a plaquette p is the ordered product of
group elements around its boundary:

$$U_p = U(\ell_1) \cdot U(\ell_2) \cdot U(\ell_3)^{-1} \cdot U(\ell_4)^{-1}$$

The **Wilson action** penalizes configurations where holonomies
deviate from the identity:

$$S(U) = \beta \sum_p \bigl(n - \mathrm{Re\,Tr}(U_p)\bigr)$$

Since |Re Tr(U)| ≤ n for unitary U (we prove this from the
column-norm-one property), the plaquette cost n − Re Tr(U_p) is
nonneg, so S ≥ 0. The Boltzmann weight w(U) = exp(−S(U)) is in
(0, 1].

A key property: the Wilson action is **gauge invariant**. Under a
gauge transformation g: sites → G that conjugates each link
U(ℓ) ↦ g(source) · U(ℓ) · g(target)⁻¹, the holonomy transforms
as U_p ↦ g(x) · U_p · g(x)⁻¹, and Re Tr is unchanged by
cyclicity of trace.

## Part 3: The Yang-Mills measure

The **Yang-Mills measure** is the probability measure on gauge
configurations defined by:

$$\mu_{\mathrm{YM}}(dU) = \frac{1}{Z} \, e^{-S(U)} \prod_\ell d\mathrm{Haar}(U(\ell))$$

where Z = ∫ exp(−S) dHaar is the partition function (proved > 0
from w > 0 on a compact group). We define this formally as
productHaar.withDensity(w/Z) and prove it is a probability measure.

The **connected 2-point function** measures correlations:

$$\langle f \cdot g \rangle - \langle f \rangle \langle g \rangle$$

where ⟨·⟩ denotes expectation under μ_YM. The mass gap is the
statement that this decays exponentially for plaquette observables
f = Re Tr(U_p), g = Re Tr(U_q).

## Part 4: The Gibbs specification

The key idea of the proof is to view the Yang-Mills measure as a
**Gibbs measure** — a probability distribution on the lattice that
satisfies local consistency conditions.

A Gibbs specification γ assigns to each subset Λ of sites (here:
links) and each boundary condition σ on Λᶜ a conditional
probability measure γ(Λ, σ) on Λ-configurations. The Wilson
action naturally defines such a specification:

$$\gamma(\Lambda, \sigma)(A) = \frac{1}{Z_\Lambda(\sigma)}
\int_{U|_\Lambda} \mathbf{1}_A(U) \, e^{-S(U)} \, d\mathrm{Haar}^\Lambda$$

where U agrees with σ outside Λ.

A probability measure μ is a **Gibbs measure** for γ if it
satisfies the DLR equation: for every Λ and measurable A,

$$\mu(A) = \int \gamma(\Lambda, \sigma)(A) \, d\mu(\sigma)$$

We prove that μ_YM satisfies DLR — this is `ymMeasure_isGibbs`,
the hardest single theorem in the lgt codebase. The proof
requires:

1. A **Fubini identity** (`glue_measurePreserving`): the
   pushforward of productHaar × productHaar through the "gluing"
   map equals productHaar. Proved via Measure.pi_eq on measurable
   boxes.
2. The **cancellation identity**: the w(σ)/Z_Λ(σ) normalization
   factors telescope when integrated against the full measure.
3. Assembly of the DLR equation from these pieces.

## Part 5: The Dobrushin condition

**Dobrushin's condition** (1968) gives a criterion for when a
Gibbs specification has unique Gibbs measures and exponential
correlation decay. The condition is:

$$\alpha := \max_x \sum_y C(x, y) < 1$$

where C(x, y) is the **influence coefficient** — the maximum
(over boundary conditions differing only at y) of the total
variation distance between the x-marginals of γ({x}, σ) and
γ({x}, τ).

For the YM specification: links x and y have nonzero influence
only if they share a plaquette. The influence bound comes from
the Boltzmann ratio: when one boundary link changes, the
conditional density ratio at x is exp(±2nβ) (one shared plaquette
contributes at most β · 2n to the energy change). The normalized
measure ratio is exp(±4nβ), giving C(x,y) ≤ 1 − exp(−4nβ).

The column sum is at most maxNeighbors(d) · (1 − exp(−4nβ)).
For β < 1/(4n · maxNeighbors(d)), this is < 1 and Dobrushin's
condition holds.

## Part 6: The Dobrushin coupling

The core of the Dobrushin uniqueness theorem is the construction
of a **joint coupling** P of two probability measures μ₁, μ₂
(both Gibbs for γ on a set T of sites) such that the per-site
disagreement probability satisfies the contraction:

$$P\{\sigma_z \neq \eta_z\} \leq \sum_w C(z,w) \cdot P\{\sigma_w \neq \eta_w\}$$

for all z ∈ T simultaneously.

The coupling P is constructed as the **minimum total disagreement
coupling**: among all couplings of μ₁ and μ₂, choose P* minimizing
∑_z P{σ_z ≠ η_z}. This exists by compactness of the space of
probability measures (Prokhorov's theorem for compact spaces).

At the minimizer P*, the contraction holds because:
updateCoupling at any site z (replacing the z-coupling with the
maximal coupling of the conditionals) cannot decrease total
disagreement (by minimality), hence cannot decrease z-disagreement
(since it preserves all other sites' disagreement), hence
z-disagreement ≤ the local contraction bound.

The **canonical maximal coupling** of two probability measures
μ, ν on a countable space S is constructed explicitly as:

$$P = (\mu \wedge \nu) \cdot \mathrm{diag} + c^{-1} \cdot (\mu - \mu \wedge \nu) \times (\nu - \mu \wedge \nu)$$

where μ ∧ ν is the pointwise minimum on singletons, and
c = 1 − (μ ∧ ν)(S) is the residual mass. This achieves
P{a ≠ b} = TV(μ, ν) (optimal). We prove it is a coupling, is
optimal, and varies measurably in (μ, ν) — the last property
is crucial for the Measure.bind kernel in the coupling construction.

## Part 7: Correlation decay via the Neumann series

Given the coupling with per-site contraction, the disagreement
vector δ(z) = P{σ_z ≠ η_z} satisfies:

$$\delta(z) \leq \sum_w C(z,w) \cdot \delta(w)$$

This is a matrix inequality δ ≤ Cδ. Iterating N times:
δ ≤ C^N δ₀ + (partial sums of C^k). Since α < 1, C^N → 0
and the series converges to the Neumann series (I−C)⁻¹:

$$\delta(y) \leq \sum_{x \in N_f} ((I-C)^{-1})_{yx}$$

For nearest-neighbor influence (C(z,w) = 0 when dist > 1), the
resolvent entry is bounded by α^{dist}/(1−α), giving exponential
decay.

## Part 8: The covariance bound

The covariance |⟨fg⟩ − ⟨f⟩⟨g⟩| is bounded using the
**multi-site** covariance decomposition:

1. **Disintegrate** μ at the N_f-fiber (the links of plaquette p)
   using Mathlib's Measure.condKernel.
2. **Factor out** f (which is N_f-local, hence constant on fibers):
   Cov(f,g) = E[f · (E[g|fiber] − E[g])].
3. **Bound** the conditional expectation difference
   |E[g|fiber=b] − E[g]| using the Dobrushin coupling: the fiber
   measure satisfies DLR at sites outside N_f (proved via
   condKernel DLR inheritance), so the coupling bounds apply.
4. **Assemble**: |Cov| ≤ Bf · 2Bg · ∑∑ neumannSeriesCoeff.

The covariance tower property (Step 2) is proved using Mathlib's
condKernel disintegration theorem, which works for compact
metrizable S (via StandardBorelSpace) without requiring
countability.

## Part 9: Assembly

`ym_mass_gap_strong_coupling` wires everything:

1. Build γ = ymGibbsSpec (the YM Gibbs specification).
2. Verify the Dobrushin condition: α < 1 at strong coupling.
3. Prove ymMeasure is Gibbs for γ (the DLR identity).
4. Prove plaquette observables are 4-link-local.
5. Bound the influence coefficients (off-plaquette = 0 via action
   factorization; on-plaquette ≤ 1−exp(−4nβ) via density ratio).
6. Apply the multi-site covariance bound with the condKernel
   a.e. bound derived from the coupling.
7. Convert connected2pt ↔ covariance via ymExpect bridge.

`ym_mass_gap_UN` specializes to G = U(n), supplying the proved
trace bounds (|Re Tr(U)| ≤ n from column-norm-one), continuity
of the fundamental representation, CompactSpace, SecondCountable-
Topology, and HasHaarProbability (all proved from Mathlib).

## What remains

- **2 lattice combinatorics facts**: each pair of links shares at
  most 1 plaquette, and each link borders at most 2(d−1) plaquettes.
  True by finite enumeration on the hypercubic lattice; tedious but
  unenlightening in Lean (256-case split + lattice geometry).

- **1 upstream axiom** (`dobrushin_coupling_axiom_compact`): the
  minimum-disagreement coupling exists for compact (not just
  countable) S. The countable case IS proved (via Prokhorov on
  finite spaces). The compact case is the same argument but needs
  Portmanteau lower semicontinuity for the coupling functional on
  compact measure spaces (~300 lines of Mathlib infrastructure).

## Statistics

| Metric | Count |
|---|---|
| New Lean 4 code (both repos) | ~12,000 lines |
| Files created | 8 (lgt) + 6 (markov-semigroups) |
| Sorry count (lgt) | 0 |
| Sorry count (markov-semigroups) | 0 |
| Custom axioms (lgt) | 0 |
| Custom axioms (markov-semigroups) | 1 (compact coupling) |
| Hypotheses in final theorem | 6 physics + 2 lattice |

## References

- S. Chatterjee, *Gauge Theory Lecture Notes* (2026), Ch 15–16
- R. L. Dobrushin, "Description of a random field by means of
  conditional probabilities" (1968)
- H.-O. Georgii, *Gibbs Measures and Phase Transitions* (1988), §8
- K. G. Wilson, "Confinement of quarks," Phys. Rev. D 10 (1974) 2445
