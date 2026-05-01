# Blueprint: Lattice Yang-Mills Mass Gap at Strong Coupling

## Overview

We formally prove exponential decay of correlations (mass gap) for
Wilson's lattice gauge theory at strong coupling, following the
Dobrushin uniqueness approach outlined in Chatterjee's *Gauge Theory
Lecture Notes* (2026), Chapter 16. The proof applies to any compact
gauge group G ⊆ U(n), in any dimension d ≥ 2, on the finite periodic
lattice (ℤ/Nℤ)^d.

The argument proceeds in three stages:

**Stage A** (Parts 1–4): Encode lattice gauge theory as a Gibbs
specification on the link lattice, and prove the Yang-Mills measure
satisfies the DLR equations.

**Stage B** (Parts 5–7): Verify Dobrushin's condition at strong
coupling and construct the Dobrushin coupling, yielding exponential
decay of the disagreement vector via the Neumann series.

**Stage C** (Parts 8–9): Transfer the coupling-level decay to a
covariance bound on plaquette observables via multi-site
disintegration.

---

## Part 1: The lattice as a cell complex

*(Lean: `LGT/Lattice/CellComplex.lean`)*

We work on the d-dimensional periodic lattice (ℤ/Nℤ)^d, which we
equip with an explicit CW-structure:

- **Sites** (0-cells): points x = (x₁, …, x_d) ∈ (ℤ/Nℤ)^d.
- **Links** (1-cells): oriented edges ℓ = (x, μ) where x is a site
  and μ ∈ {0, …, d−1} is a lattice direction. The link connects x
  to x + eμ (mod N).
- **Plaquettes** (2-cells): oriented unit squares p = (x, μ, ν) with
  μ < ν. The boundary ∂p consists of four links traversed
  counterclockwise:

  $$\partial p = \{(x, \mu),\; (x{+}e_\mu, \nu),\; (x{+}e_\nu, \mu),\; (x, \nu)\}$$

  The third and fourth links are traversed with reversed orientation.

Two links share a plaquette iff they are edges of a common unit
square. On the standard lattice, each link lies on at most 2(d−1)
plaquettes, and two distinct links share at most one plaquette.

## Part 2: Gauge fields and the Wilson action

*(Lean: `LGT/GaugeField/`, `LGT/WilsonAction/`)*

Fix a compact matrix Lie group G ⊆ U(n) with the fundamental
representation ρ: G → M_n(ℂ).

A **gauge configuration** (or connection) is a function
U: Links → G assigning a group element to each link. The
configuration space is G^{|Links|}, a compact product of copies
of G.

The **holonomy** around a plaquette p is the ordered product of
group elements around its boundary (cf. Chatterjee §15.2):

$$U_p = U(\ell_1) \cdot U(\ell_2) \cdot U(\ell_3)^{-1} \cdot U(\ell_4)^{-1}$$

For a flat connection (U_p = 1), the holonomy is trivial. The
holonomy measures the discrete curvature.

The **Wilson plaquette action** (Wilson 1974) is:

$$S(U) = \beta \sum_{p \in \text{plaq}} \bigl(n - \mathrm{Re\,Tr}(U_p)\bigr)$$

where β ≥ 0 is the inverse coupling constant. Since U_p ∈ G ⊆ U(n),
the eigenvalues of ρ(U_p) lie on the unit circle, so
Re Tr(ρ(U_p)) ∈ [−n, n]. We prove this from the column-norm-one
property of unitary matrices:

> **Lemma** (`unitaryGroup_gaugeReTr_le`). For U ∈ U(n),
> |Re Tr(U)| ≤ n.
>
> *Proof.* Each diagonal entry satisfies |U_{ii}|² ≤ Σ_k |U_{ki}|² = 1
> (column norm one), hence |Re U_{ii}| ≤ |U_{ii}| ≤ 1, and
> |Re Tr(U)| = |Σ_i Re U_{ii}| ≤ n. □

The plaquette cost n − Re Tr(U_p) ∈ [0, 2n], so S ≥ 0 and the
**Boltzmann weight** w(U) = exp(−S(U)) ∈ (0, 1].

The action is **gauge invariant**: under a gauge transformation
g: Sites → G acting by U(ℓ) ↦ g(source(ℓ)) · U(ℓ) · g(target(ℓ))⁻¹,
the holonomy transforms as U_p ↦ g(x) · U_p · g(x)⁻¹, and
Re Tr is invariant by cyclicity of trace (cf. Chatterjee §15.3).

## Part 3: The Yang-Mills measure

*(Lean: `LGT/MassGap/YMMeasure.lean`)*

The **prior measure** on configurations is the product Haar
probability measure:

$$\mu_{\text{Haar}} = \bigotimes_{\ell \in \text{Links}} \text{Haar}_G$$

This is a probability measure on G^{|Links|} (finite product of
compact groups with Haar probability).

The **Yang-Mills measure** is the Boltzmann-weighted measure:

$$\mu_{\text{YM}} = \frac{1}{Z} \, e^{-S(U)} \, d\mu_{\text{Haar}}(U)$$

where Z = ∫ exp(−S) dμ_Haar is the **partition function**. We prove
Z > 0 from the strict positivity of the Boltzmann weight on the
compact support (cf. Chatterjee §15.4):

> **Lemma** (`partitionFn_pos`). Z > 0.
>
> *Proof.* w(U) = exp(−S(U)) > 0 for all U, and w is bounded below
> by exp(−β · |plaq| · 2n) > 0. Since μ_Haar is a probability
> measure, Z ≥ exp(−β · |plaq| · 2n) > 0. □

Formally, μ_YM is defined as `productHaar.withDensity(ofReal(w/Z))`.
We prove it is a probability measure and establish the bridge
`ymExpect f = ∫ f dμ_YM` connecting the expectation-value notation
with the measure-theoretic integral.

The **connected 2-point function** (covariance) of observables
f, g is:

$$\langle f g \rangle - \langle f \rangle \langle g \rangle$$

The mass gap is the statement that this decays exponentially when
f = Re Tr(U_p) and g = Re Tr(U_q) are plaquette observables at
distant plaquettes p, q.

## Part 4: The DLR identity — Yang-Mills as a Gibbs measure

*(Lean: `LGT/Gibbs/YMSpec.lean`, `LGT/Gibbs/YMIsGibbs.lean`)*

The strategy for proving correlation decay is to apply the Dobrushin
uniqueness theorem from the theory of Gibbs measures (Chatterjee
§16.3, Georgii §8). This requires expressing the Yang-Mills measure
as a **Gibbs measure** on the link lattice — a probability distribution
satisfying local consistency conditions known as the DLR equations.

### Gibbs specifications

In statistical mechanics, a **Gibbs specification** (cf. Georgii §1.2,
Chatterjee §16.1) is a rule that, given any finite region Λ and any
configuration σ on the complement Λᶜ, produces a conditional
probability distribution on Λ-configurations. Formally, it is a
family of probability kernels γ(Λ, σ) indexed by (Λ, σ) satisfying
consistency, properness, and measurability axioms.

For lattice gauge theory, the "sites" are links and the "spin space"
is the gauge group G. A configuration is a function
U: Links → G. Given a finite subset Λ ⊆ Links and a boundary
condition σ: Links → G (specifying group elements on all links
outside Λ), the Gibbs conditional is:

$$\gamma(\Lambda, \sigma)(A) = \frac{1}{Z_\Lambda(\sigma)}
\int_{G^\Lambda} \mathbf{1}_A\bigl(\mathrm{glue}(\Lambda, u_\Lambda, \sigma)\bigr)
\, e^{-S(\mathrm{glue}(\Lambda, u_\Lambda, \sigma))} \, d\mathrm{Haar}^\Lambda(u_\Lambda)$$

Here the **gluing operation** glue(Λ, u_Λ, σ) produces a full
configuration by combining fresh integration variables u_Λ on the
links in Λ with the fixed boundary values σ on the links outside Λ:

$$\mathrm{glue}(\Lambda, u_\Lambda, \sigma)(\ell) =
\begin{cases} u_\Lambda(\ell) & \text{if } \ell \in \Lambda \\
\sigma(\ell) & \text{if } \ell \notin \Lambda \end{cases}$$

The integral is over the product Haar measure on G^Λ (independent
Haar on each link in Λ), and Z_Λ(σ) = ∫ w(glue(Λ, u_Λ, σ)) dHaar^Λ
is the **conditional partition function**, which normalizes the
density to a probability measure. We prove Z_Λ(σ) > 0 by the same
argument as for the full partition function (the Boltzmann weight
is strictly positive everywhere).

The Gibbs specification satisfies three structural axioms:

- **Consistency**: γ(Λ, σ) depends on σ only through σ|_{Λᶜ}
  (changing σ inside Λ has no effect, since those values are
  replaced by the integration variables u_Λ).
- **Properness**: γ(Λ, σ) is concentrated on configurations that
  agree with σ outside Λ (the gluing operation forces this by
  construction).
- **Measurability**: σ ↦ γ(Λ, σ)(A) is measurable for each A
  (proved from the continuity of the Boltzmann weight and the
  parametric integral).

### The DLR equation

A probability measure μ on configurations is a **Gibbs measure**
for the specification γ if it satisfies the **DLR equation**
(Dobrushin–Lanford–Ruelle, cf. Georgii §1.5): for every finite Λ
and every measurable set A of configurations,

$$\mu(A) = \int \gamma(\Lambda, \sigma)(A) \, d\mu(\sigma)$$

In words: the probability μ assigns to any event A equals the
average, over boundary conditions σ drawn from μ itself, of the
conditional probability γ(Λ, σ)(A). This is a self-consistency
condition — μ is compatible with its own conditional distributions.

On a finite lattice, the DLR equation has a unique solution when
Dobrushin's condition holds (Part 5). On an infinite lattice, the
DLR equation may have multiple solutions (phase coexistence); the
Dobrushin condition guarantees uniqueness.

### Proving the DLR identity

We prove that the Yang-Mills measure μ_YM satisfies DLR —
this is `ymMeasure_isGibbs`, the most technically demanding
theorem in the lgt formalization. The proof assembles five
intermediate results:

1. **Pushforward identity** (`glue_measurePreserving`): the map
   (u, σ) ↦ glue(Λ, u, σ) pushes productHaar × productHaar forward
   to productHaar. Proved via `Measure.pi_eq` by computing the
   preimage of each measurable box.

2. **Fubini helper** (`integral_glue_split_eq`): for integrable F,
   ∫∫ F(glue(u, σ)) dHaar(u) dHaar(σ) = ∫ F(U) dHaar(U).
   Follows from (1) via `integral_map` + `integral_prod_symm`.

3. **Identity A** (`integral_smul_condZ_eq_integral_smul_w`): for h
   constant on Λᶜ-fibers, ∫ h · Z_Λ dHaar = ∫ h · w dHaar.
   Follows from (2) with F = h · w.

4. **Cancellation identity** (`cancellation_identity`): for h
   constant on Λᶜ-fibers, ∫ h · w/Z_Λ dHaar = ∫ h dHaar.
   Follows from (3) by substituting h/Z_Λ.

5. **DLR assembly** (`ymMeasure_dlr`): combines (4) with the
   indicator-weighted Fubini identity and the withDensity unfolding
   of μ_YM and γ(Λ, σ).

## Part 5: The Dobrushin condition at strong coupling

*(Lean: `LGT/Gibbs/YMDobrushin.lean`, `LGT/MassGap/DobrushinVerification.lean`)*

**Dobrushin's condition** (Dobrushin 1968, Chatterjee §16.2) provides
a criterion for exponential correlation decay. Define the **influence
coefficient** C(x, y) as the maximum, over boundary conditions σ, τ
differing only at link y, of the total variation distance between the
x-marginals of γ({x}, σ) and γ({x}, τ):

$$C(x, y) = \sup_{\sigma \sim_y \tau}
d_{\text{TV}}\bigl(\gamma(\{x\}, \sigma)|_x,\; \gamma(\{x\}, \tau)|_x\bigr)$$

Dobrushin's condition requires: the maximum row (or column) sum
α := max_x Σ_y C(x, y) is strictly less than 1.

For the YM specification, we prove two influence bounds:

**Off-plaquette: C(x, y) = 0 when x and y don't share a plaquette.**
The conditional at {x} has density w(glue(u, σ))/Z_x(σ). When σ
changes only at y, and y shares no plaquette with x, the action
decomposes as S = S_x + S_rest where S_x (plaquettes through x)
doesn't involve y. So the density ratio w(glue(u, σ))/w(glue(u, τ))
is exactly 1, and the conditional measures are identical.

**On-plaquette: C(x, y) ≤ 1 − exp(−4nβ) when x, y share a plaquette.**
The conditional density at x, viewed as a function of u_x, changes by
a factor exp(±2nβ) when σ(y) changes (the shared plaquette contributes
at most β · 2n to the energy oscillation). After normalization, the
measure ratio is exp(±4nβ), giving TV ≤ 1 − exp(−4nβ).

The column sum is at most maxNeighbors(d) · (1 − exp(−4nβ)), where
maxNeighbors(d) = 8(d−1) is the maximum number of links sharing a
plaquette with a given link. For

$$\beta < \frac{1}{4n \cdot 8(d-1)} = \frac{1}{32n(d-1)},$$

Dobrushin's condition holds with α < 1 (cf. Chatterjee Theorem 16.3.1
for the analogous result).

## Part 6: The Dobrushin coupling

*(Lean: `markov-semigroups/Coupling/DobrushinCoupling.lean`,
`markov-semigroups/Coupling/CanonicalCoupling.lean`)*

The heart of the Dobrushin uniqueness theorem is the construction of a
**joint coupling** P of two measures μ₁, μ₂ (both satisfying DLR on a
set T of sites) such that the per-site disagreement satisfies the
**contraction inequality** simultaneously at all sites z ∈ T:

$$P\{\sigma_z \neq \eta_z\} \leq \sum_w C(z, w) \cdot P\{\sigma_w \neq \eta_w\}$$

We construct P as the **minimum total disagreement coupling**
(cf. Dobrushin 1968, Lemma 2; Georgii §8.1, Proposition 8.7):

> **Theorem** (`dobrushin_iterated_coupling_fintype`).
> Among all couplings of μ₁ and μ₂, let P* minimize the total
> disagreement D(P) = Σ_z P{σ_z ≠ η_z}. Then P* satisfies the
> per-site contraction at every z ∈ T.

*Proof.* The minimum exists by **Prokhorov compactness**: the space
of probability measures on a compact space is compact in the weak
topology, and the coupling set (measures with prescribed marginals) is
closed. The total disagreement D is lower semicontinuous (each
{σ_z ≠ η_z} is open for T₂ spaces), so D attains its minimum on the
compact coupling set.

At the minimizer P*, suppose `P*{σ_z ≠ η_z} > Σ_w C(z,w) P*{σ_w ≠ η_w}`
for some z ∈ T. Then replacing the z-coupling with the **maximal
coupling** of the z-conditionals would produce a coupling P' with:
- D(P') = D(P*) − P*{z-ne} + P'{z-ne} < D(P*) (since P'{z-ne} ≤
  Σ C(z,w) P*{w-ne} < P*{z-ne}, and all other sites' disagreement
  is unchanged by `updateCoupling_disagree_preserve`).
This contradicts minimality of P*. □

The **maximal coupling** of two probability measures μ, ν on a
countable space S is constructed canonically as (cf. Lindvall 2002):

$$P_{\max} = (\mu \wedge \nu) \cdot \Delta + c^{-1} \cdot (\mu - \mu \wedge \nu) \otimes (\nu - \mu \wedge \nu)$$

where Δ is the diagonal embedding, (μ ∧ ν)({a}) = min(μ{a}, ν{a}),
and c = TV(μ, ν) = 1 − (μ ∧ ν)(S). This achieves P{a ≠ b} = TV(μ, ν),
the minimum possible. We prove it is a coupling, achieves the TV
distance, and (crucially for the `Measure.bind` kernel) **varies
measurably** in (μ, ν) — using the explicit pointwise-min formula
rather than the non-constructive `.choose` from `exists_maximal_coupling`.

## Part 7: Exponential decay via the Neumann series

*(Lean: `markov-semigroups/Dobrushin/NeumannSeries.lean`,
`markov-semigroups/Dobrushin/CondTVBridge.lean`)*

Given the coupling P with the contraction δ(z) ≤ Σ_w C(z,w) δ(w),
where δ(w) = P{σ_w ≠ η_w}, we iterate the inequality:

$$\delta \leq C\delta \leq C^2\delta \leq \cdots \leq C^N \delta_0 + \sum_{k=0}^{N-1} C^k \cdot \text{source}$$

The "source" arises from sites x ∉ T where DLR does not hold (in our
application, T = Links \ N_f, and N_f is the 4-link support of the
plaquette observable). At these source sites, δ(x) ≤ 1.

Since α < 1, the Neumann series Σ_k C^k converges to (I − C)⁻¹, and:

$$\delta(y) \leq \sum_{x \in N_f} ((I - C)^{-1})_{yx} \cdot 1$$

For nearest-neighbor influence (C(z, w) = 0 when they share no
plaquette), the resolvent entry is bounded by (cf. Chatterjee §16.2):

$$((I - C)^{-1})_{yx} \leq \frac{\alpha^{\text{dist}(y, x)}}{1 - \alpha}$$

where dist is the graph distance in the link-adjacency graph. This
gives exponential decay of the coupling disagreement.

## Part 8: From coupling to covariance — the multi-site bound

*(Lean: `markov-semigroups/Dobrushin/CovarianceBoundMultisite.lean`,
`markov-semigroups/Dobrushin/CondKernelDLR.lean`)*

The plaquette observable Re Tr(U_p) depends on the 4 links of
plaquette p, not a single link. This requires a **multi-site**
covariance bound.

For f depending on N_f ⊆ Links (the boundary links of plaquette p,
|N_f| = 4) and g depending on N_g (the boundary links of plaquette q):

> **Theorem** (`covariance_bound_gibbs_multisite_general_nocount`).
>
> $$|\text{Cov}_\mu(f, g)| \leq 2 B_f B_g \sum_{x \in N_f} \sum_{y \in N_g} \frac{\alpha^{\text{dist}(y,x)}}{1 - \alpha}$$

The proof has three ingredients:

**Ingredient 1: Covariance decomposition via disintegration.**
Disintegrate μ at the N_f-fiber using Mathlib's `Measure.condKernel`
(regular conditional probability for Standard Borel spaces). Since f
is N_f-local (constant on fibers):

$$\text{Cov}(f, g) = \int f(b) \cdot \bigl(E[g \mid \text{fiber} = b] - E[g]\bigr) \, d\mu_{\text{fst}}(b)$$

Bounding |f| ≤ B_f gives |Cov| ≤ B_f · sup_b |E[g|b] − E[g]|.

This is the **tower property** for conditional expectations. For
uncountable compact S (like U(n)), the discrete fiber decomposition
fails (fibers have measure zero for diffuse marginals), so we use
Mathlib's condKernel disintegration which works for arbitrary Standard
Borel spaces via Prokhorov's theorem.

**Ingredient 2: Conditional expectation bound via coupling.**
For each fiber value b, the conditional measure μ_b (the condKernel
fiber lifted back to SpinConfig) satisfies the DLR equations at sites
z ∉ N_f:

> **Theorem** (`fiberMeasure_dlr_ae`). For a.e. b, μ_b satisfies DLR
> at every {z} with z ∉ N_f.

*Proof.* Transport the DLR equation for μ through the disintegration
ρ = ρ.fst ⊗ κ. For each measurable A, the integral identity
∫ F_A(b) dρ.fst = ∫ G_A(b) dρ.fst follows from DLR on restricted
sets. The a.e. equality F_A = G_A for each A follows from
`Integrable.ae_eq_of_forall_setIntegral_eq` (Radon-Nikodym uniqueness).
The upgrade from "for each A, a.e. b" to "a.e. b, for all A" uses the
countable generating π-system of the Standard Borel space
(via `MeasurableSpace.ae_induction_on_inter`). The finite intersection
over z ∉ N_f is trivial. □

With DLR for μ_b, the Dobrushin coupling applies to μ_b and μ, giving:

$$|E[g \mid b] - E[g]| \leq 2 B_g \sum_{y \in N_g} \sum_{x \in N_f} ((I-C)^{-1})_{yx}$$

(The factor 2B_g comes from a union bound over the N_g sites of g,
using `local_integral_sub_le_coupling_Ng`.)

**Ingredient 3: Nearest-neighbor exponential decay.**
Substituting the resolvent bound:

$$|\text{Cov}| \leq 2 B_f B_g \sum_{x \in N_f} \sum_{y \in N_g}
\frac{\alpha^{\text{dist}(y, x)}}{1 - \alpha}$$

Since |N_f| = |N_g| = 4 and dist(y, x) ≥ dist(p, q) − 2 (the links
of each plaquette are within distance 1 of the plaquette center), this
gives exponential decay in plaquette distance.

## Part 9: Assembly — the mass gap for U(n)

*(Lean: `LGT/MassGap/StrongCoupling.lean`, `LGT/GaugeField/UnitaryGroup.lean`)*

The final theorem `ym_mass_gap_strong_coupling` wires Parts 1–8:

1. **Build** γ = ymGibbsSpec (Part 4).
2. **Verify** the Dobrushin condition α < 1 at β < 1/(32n(d−1)) (Part 5).
3. **Prove** μ_YM is Gibbs for γ via ymMeasure_isGibbs (Part 4).
4. **Prove** plaquette observables are 4-link-local.
5. **Derive** the influence bounds from the action splitting (Part 5).
6. **Derive** the condKernel a.e. bound from fiberMeasure_dlr_ae (Part 8).
7. **Apply** the multi-site covariance bound (Part 8).
8. **Convert** the covariance form back to connected2pt.

The U(n) specialization in `ym_mass_gap_exponential_decay` instantiates
G = U(n), discharging:
- Trace bounds |Re Tr(U)| ≤ n (from column-norm-one, Part 2).
- Continuity of the fundamental representation (subtype inclusion).
- CompactSpace (closed + bounded in finite-dim space, Heine-Borel).
- SecondCountableTopology (subspace of M_n(ℂ)).
- HasHaarProbability (Mathlib's haarMeasure with K₀ = U(n), normalized
  via haarMeasure_self = 1 for compact groups).

## Relation to Chatterjee's exposition

Our formalization follows Chatterjee (2026) Chapter 16 closely:

| Chatterjee | This formalization |
|---|---|
| §16.1 Gibbs specifications | `ymGibbsSpec` (YMSpec.lean) |
| §16.2 Dobrushin uniqueness | `dobrushin_iterated_coupling_fintype` (DobrushinCoupling.lean) |
| §16.2 Influence coefficients | `influenceCoeff`, influence bounds (YMDobrushin.lean) |
| §16.2 Neumann series | `neumannSeriesCoeff`, resolvent bound (NeumannSeries.lean) |
| §16.3 Application to YM (framework) | `ym_mass_gap_strong_coupling` (StrongCoupling.lean) |
| Theorem 16.3.1 (exponential decay) | `ym_mass_gap_exponential_decay` (StrongCoupling.lean, **target; 1 sorry**) |

The main differences from Chatterjee's treatment:
- We use the **multi-site** covariance bound (plaquette observables
  depend on 4 links, not 1), which Chatterjee handles implicitly.
- We construct the Dobrushin coupling via **minimum total disagreement**
  (Prokhorov compactness), whereas Chatterjee uses the iterative
  sweep construction.
- We prove the DLR identity for μ_YM explicitly, whereas Chatterjee
  takes it as given.
- We handle uncountable gauge groups via Mathlib's `condKernel`
  disintegration (Standard Borel spaces), whereas Chatterjee works
  with finite or countable state spaces.

## What remains

Two **lattice combinatorics hypotheses** (provable by finite
enumeration, ~160 lines):
- `hSharedPlaqBound`: two distinct links share at most 1 plaquette.
- `hPlaqPerLink`: each link borders at most 2(d−1) plaquettes.

One **upstream axiom** in markov-semigroups
(`dobrushin_coupling_axiom_compact`): the minimum-disagreement
coupling exists for compact (not just countable) S. The countable
case IS proved; the compact case requires Portmanteau lower
semicontinuity (~300 lines of Mathlib infrastructure).

## Statistics

| Metric | Count |
|---|---|
| New Lean 4 code (both repos) | ~12,000 lines |
| Files created | 8 (lgt) + 6 (markov-semigroups) |
| Sorry count (lgt, `ym_mass_gap_strong_coupling`) | 0 |
| Sorry count (lgt, `ym_mass_gap_exponential_decay`) | 1 (see `docs/mass-gap-completion-plan.md` for the route to close) |
| Sorry count (markov-semigroups) | 0 |
| Custom axioms (lgt) | 0 |
| Custom axioms (markov-semigroups) | 1 (compact coupling) |
| Hypotheses in final theorem | 6 physics + 2 lattice |
| Upstream bugs found + fixed | 2 (false marginal-TV axiom, h_dep_F) |

## References

- S. Chatterjee, *Gauge Theory Lecture Notes* (2026), Chapters 15–16.
- R. L. Dobrushin, "Description of a random field by means of
  conditional probabilities and conditions of its regularity,"
  *Teor. Veroyatnost. i Primenen.* **13** (1968), 201–229.
- H.-O. Georgii, *Gibbs Measures and Phase Transitions*, de Gruyter,
  1988, §8.
- T. Lindvall, *Lectures on the Coupling Method*, Dover, 2002.
- K. G. Wilson, "Confinement of quarks,"
  *Phys. Rev. D* **10** (1974), 2445–2459.
