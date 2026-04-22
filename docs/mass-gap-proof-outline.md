# Formal Proof of Dobrushin Contraction for Lattice Yang-Mills at Strong Coupling

## Proved theorem

**Theorem** (`ym_mass_gap_UN` in `LGT/MassGap/StrongCoupling.lean`).
For the U(n) Wilson lattice gauge theory on the d-dimensional periodic
lattice (ℤ/Nℤ)^d with d ≥ 2, N ≥ 3, n ≥ 1, and coupling
β < 1/(32n(d−1)), the connected 2-point function of plaquette
observables p, q is bounded:

    |⟨Re Tr(U_p) · Re Tr(U_q)⟩ − ⟨Re Tr(U_p)⟩ · ⟨Re Tr(U_q)⟩|
        ≤ 2n² · ∑_{x ∈ ∂p, y ∈ ∂q} α^{d(x,y)} / (1 − α)

where α = dobrushinColumnSum(n, d, β) < 1 and d(x,y) = ymLinkDist
is a coarse link distance taking values in {0, 1, 2}. Zero sorry's,
zero custom axioms.

## Mass gap target (not yet proved)

**Theorem** (`ym_mass_gap_exponential_decay`, sorry).
Under the same hypotheses, the connected 2-point function decays
exponentially in the periodic L₁ plaquette distance:

    |⟨Re Tr(U_p) · Re Tr(U_q)⟩_c| ≤ C(n,d,β) · α^{dist(p,q)}

This reduces to `ym_mass_gap_UN` plus the combinatorial bound that
link graph distance ≥ L₁ site distance minus a constant.

## Axiom status

```
#print axioms ym_mass_gap_UN
-- propext, Classical.choice, Quot.sound
```

**Zero sorry's. Zero custom axioms.** Only the three standard Lean
axioms used by every Lean program.

## Architecture

The proof spans two Lean 4 libraries:

- **lgt** (`mrdouglasny/lgt`): lattice gauge theory definitions,
  Wilson action, Gibbs specification, mass gap assembly.
- **markov-semigroups** (`mrdouglasny/markov-semigroups`): abstract
  Dobrushin uniqueness theory, coupling machinery, covariance bounds.

### Layer 1 — Lattice Structure (`LGT/Lattice/`)

`CellComplex.lean` defines the discrete geometry:
- **Sites**: (ℤ/Nℤ)^d (the periodic lattice).
- **Links**: (site, direction) pairs — oriented 1-cells.
- **Plaquettes**: (site, dir₁ < dir₂) triples — oriented 2-cells.
  Each plaquette has 4 boundary links via `boundaryLinks : Fin 4 → LatticeLink`.
- **Incidence lemmas** (fully proved):
  - `plaquettes_per_link_le'`: each link borders ≤ 2(d−1) plaquettes
    (via injection into `{ν : Fin d // ν ≠ ℓ.dir} × Bool`).
  - `shared_plaquettes_le_one`: two distinct links share ≤ 1 plaquette
    (requires N ≥ 3; false for N = 2 due to ZMod 2 wraparound).
  - Helper lemmas: `siteShift_injective`, `siteShift_ne_self`,
    `siteShift_cross_absurd`, `plaquette_unique_of_two_links`.

### Layer 2 — Gauge Fields (`LGT/GaugeField/`)

- **Connections**: `GaugeConnection G d N := LatticeLink d N → G`
  (G-valued parallel transport on each link).
- **Holonomy**: `plaquetteHolonomy U p = U(l₁)·U(l₂)·U(l₃)⁻¹·U(l₄)⁻¹`
  (ordered product around the plaquette boundary).
- **Gauge transformations**: `g : Sites → G` acts by conjugation on
  each link. Holonomy transforms covariantly; trace is invariant.
- **U(n) instantiation** (`UnitaryGroup.lean`): `HasGaugeTrace` instance
  for the unitary group via the fundamental representation, with proved
  trace bounds |Re Tr(U)| ≤ n, continuity, CompactSpace,
  SecondCountableTopology, and HasHaarProbability.

### Layer 3 — Wilson Action (`LGT/WilsonAction/`)

- **Plaquette cost**: `n − Re Tr(U_p)` ∈ [0, 2n].
- **Wilson action**: `S(U) = ∑_p β · cost(U_p)`.
- **Boltzmann weight**: `w(U) = exp(−S(U))` ∈ (0, 1] for β ≥ 0.
- **Gauge invariance**: `S(g·U) = S(U)` via trace cyclicity (`gaugeTrace_conj_invariant`).

### Layer 4 — Yang-Mills Measure (`LGT/MassGap/`)

`YMMeasure.lean`:
- **Product Haar measure**: `productHaar = ⊗_ℓ Haar_G` on G^{links}.
- **Yang-Mills measure**: `ymMeasure = productHaar.withDensity(w/Z)`.
- **Partition function**: `Z = ∫ w dHaar > 0` (from `w > 0` on compact support).
- **Expectation**: `ymExpect f = (∫ f·w dHaar) / Z`.
- **Connected 2-point function**: `⟨fg⟩ − ⟨f⟩⟨g⟩`.

SFinite, IsProbabilityMeasure, and related instances registered for
`productHaar` and `ymMeasure`.

### Layer 5 — Gibbs Specification (`LGT/Gibbs/`)

`YMSpec.lean`: Encodes the Yang-Mills theory as a `GibbsSpec` on
the link lattice (sites = links, spin space = G):
- `gibbsCondMeasure Λ σ` = conditional Boltzmann measure on Λ-links
  given boundary σ on Λᶜ.
- Proved: consistency, properness, normalization.

`YMIsGibbs.lean` (**the DLR identity**):
- `ymMeasure_isGibbs`: the Yang-Mills measure IS a Gibbs measure
  for `ymGibbsSpec`. Proof via:
  1. `glue_measurePreserving`: the pushforward identity on product Haar
     (proved via `Measure.pi_eq` on measurable boxes).
  2. `integral_glue_split_eq`: core Fubini helper.
  3. `integral_smul_condZ_eq_integral_smul_w` (Identity A):
     h-weighted integral identity.
  4. `cancellation_identity` (S2): the w(σ)/Z(σ) cancellation.
  5. `ymMeasure_dlr`: the full DLR equation.

`YMDobrushin.lean`: Dobrushin condition verification.
- `ymDobrushinCondition`: the column sum of the influence matrix
  α = maxNeighbors(d) · influenceBound(n, β) < 1 at strong coupling.

### Layer 6 — Dobrushin Theory (markov-semigroups)

`Dobrushin/Specification.lean`: Abstract GibbsSpec + IsGibbsMeasure.

`Dobrushin/Uniqueness.lean`:
- `influenceCoeff γ x y` = sup TV distance of x-marginals over
  boundary pairs differing at y.
- `DobrushinCondition`: row + column sums < α < 1.
- `marginalTvDist_contraction`: single-step contraction.
- `influenceCoeff_le_of_cylinder_ratio_bound`: general density-ratio
  → influence coefficient bound (the Layer 1 abstraction).

`Coupling/CanonicalCoupling.lean`:
- Constructive pointwise-min maximal coupling.
- Giry measurability for countable spin spaces.

`Coupling/DobrushinCoupling.lean`:
- `updateCoupling`: single-site coupling improvement.
- `dobrushin_iterated_coupling_fintype`: min-disagreement coupling
  for finite spin spaces via Prokhorov compactness.

`Coupling/ProkhorovCoupling.lean`:
- `canonicalMaximalCoupling_compact`: maximal coupling for Borel
  spaces (no Countable S requirement). Marginal proofs generalized.
- `measurable_inf_apply`: Giry measurability of measure infimum
  via kernel Radon-Nikodym derivatives (the key technical innovation).
- `prokhorov_coupling_theorem`: min-disagreement coupling for compact
  spin spaces via Prokhorov compactness + Portmanteau lsc.
- Eliminates `dobrushin_coupling_axiom_compact` (formerly the last
  custom axiom).

`Tools/SingleSiteDisintegration.lean`:
- `condSingleSiteMeasure μ x a` = μ(· | σ(x) = a).
- Disintegration identity (integral form).

`Dobrushin/CovarianceBound.lean`:
- `covariance_bound_via_bridge`: |Cov(f,g)| ≤ Bf · K given a
  conditional-expectation-difference bound K.

`Dobrushin/CondTVBridge.lean`:
- `condSingleSiteMeasure_dlr_at_site`: the conditional measure
  satisfies DLR at every site z ≠ x.
- `abstract_neumann_iteration`: Neumann-series contraction from a
  self-consistency inequality to a resolvent bound.
- `covariance_bound_gibbs`: |Cov| ≤ 2·Bf·Bg · neumannSeriesCoeff.

`Dobrushin/CondKernelDLR.lean`:
- `fiberMeasure_dlr_ae`: condKernel fiber inherits DLR.
- `condKernel_ae_bound`: the condKernel-based a.e. covariance bound
  (bridges uncountable spin spaces via Mathlib's condKernel).

`Dobrushin/NeumannSeries.lean`:
- `neumannSeriesCoeff γ x y = ∑_n (C^n)_{xy}` (resolvent entry).
- `neumannSeriesCoeff_nn_dist_bound`: ≤ α^{dist}/(1−α) for
  nearest-neighbor specifications.
- `dobrushin_correlation_decay_nn_dist`: general-I textbook form.

`Dobrushin/CovarianceBoundMultisite.lean`:
- Generalizes the entire chain from single-site-local observables
  to **multi-site-local** observables (needed for plaquette
  observables, which depend on 4 links).
- `condFiniteSupportMeasure`, multi-site DLR, multi-source
  Neumann iteration, `covariance_bound_gibbs_multisite_general`.

### Layer 7 — Mass Gap Assembly (`LGT/MassGap/StrongCoupling.lean`)

`ym_mass_gap_strong_coupling` assembles the full chain:

1. **Build γ**: `ymGibbsSpec G n d N plaq β`.
2. **Dobrushin condition**: `ymDobrushinCondition` with
   α = dobrushinColumnSum < 1 at strong coupling.
3. **ymMeasure is Gibbs**: `ymMeasure_isGibbs`.
4. **Plaquette locality**: `plaqObs p` depends on 4 boundary links
   (N_f = {p.boundaryLinks i | i : Fin 4}).
5. **Influence bound**: off-plaquette = 0 (`influenceCoeff_zero_off_plaquette`,
   via `boltzmannWeight_factor_eq`); on-plaquette ≤ 1−exp(−4nβ)
   (`gibbsCondMeasure_cylinder_ratio` via action splitting S = S_x + S_rest).
6. **Lattice incidence**: `shared_plaquettes_le_one` (needs N ≥ 3) and
   `plaquettes_per_link_le'` discharged from CellComplex.
7. **Apply** `covariance_bound_gibbs_multisite_general_nn_dist_nocount`
   from markov-semigroups.
8. **Convert** connected2pt ↔ covariance via `ymExpect_eq_integral_ymMeasure`.

`ym_mass_gap_UN` specializes to G = U(n), supplying trace bounds
and representation continuity from `UnitaryGroup.lean`.

## Statistics

| Metric | Count |
|---|---|
| New Lean 4 code (both repos) | ~12,000 lines |
| `ym_mass_gap_UN` sorry count | 0 |
| `ym_mass_gap_UN` custom axioms | 0 |
| `ym_mass_gap_exponential_decay` sorry count | 1 (combinatorial reduction) |
| Standard Lean axioms | 3 (propext, Classical.choice, Quot.sound) |

## References

- K. R. Chatterjee, *Gauge Theory Lecture Notes* (2026), Ch 15–16.
- R. L. Dobrushin, "Description of a random field by means of
  conditional probabilities" (1968).
- H.-O. Georgii, *Gibbs Measures and Phase Transitions* (1988), §8.
- Yu. V. Prokhorov, "Convergence of random processes" (1956).
- K. G. Wilson, Phys. Rev. D 10 (1974) 2445.
