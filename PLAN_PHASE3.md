# Plan: Phase 3 — Discharge the mass-gap bridge hypotheses

*2026-04-15*

Phases 1 (`ymGibbsSpec`) and 2 (`ymDobrushinCondition`) are complete.
Phase 3 is to remove the `hBridge` / `hFP` hypotheses in
`LGT/MassGap/GaugeFixing.lean`, `LGT/MassGap/MassGap2D.lean`, and
`LGT/MassGap/MassGap3D.lean`, so that the mass-gap theorems become
unconditional (modulo external bridges in markov-semigroups).

## Current state of the target theorems

| Theorem | File | Status |
|---|---|---|
| `faddeevPopov` | `GaugeFixing.lean:81` | stub: `hFP → hFP` |
| `doeblin_correlation_bound_2d` | `GaugeFixing.lean:124` | stub: `hBridge → hBridge` |
| `dobrushin_correlation_bound` | `GaugeFixing.lean:156` | stub: `hBridge → hBridge` |
| `mass_gap_2d` | `MassGap2D.lean:50` | real proof, but depends on `hBridge` |
| `ym_mass_gap_2pt` | `MassGap3D.lean:131` | real proof, but depends on `hBridge` |

`ym_satisfies_dobrushin` and `mass_gap_2d_rate_pos` are genuinely
proven and do not change.

## External dependency (in flight, another agent)

In `MarkovSemigroups/Dobrushin/Uniqueness.lean:826`,
`dobrushin_correlation_decay` still takes a `hDecay` bridge
hypothesis (Neumann-series covariance bound). The agent working on
markov-semigroups is expected to discharge this.

**We do not block on it.** We target the current signature and
note in a comment which hypothesis will disappear when the external
work lands.

In `MarkovSemigroups/Convergence/Doeblin.lean:310`,
`doeblin_correlation_decay` is already fully proved (no bridge).
So the 2D path is in principle closable today.

## Revision (2026-04-15, after audit)

Initial plan assumed Faddeev-Popov was on the critical path for the
d≥3 bound. After reading `LGT/Gibbs/YMSpec.lean` and
`LGT/MassGap/YMMeasure.lean` more carefully:

- `ymGibbsSpec` is defined on `LatticeLink d N` with **no gauge
  fixing** — it's the unfixed Wilson theory expressed as a Gibbs
  specification. Dobrushin's condition applies directly.
- The YM expectation `ymExpect f` is `(∫ f·w dHaar) / Z`, which we
  can repackage as `∫ f dymMeasure` for `ymMeasure :=
  productHaar.withDensity (w/Z)`.
- If we prove `IsGibbsMeasure (ymGibbsSpec β) ymMeasure`, then
  `dobrushin_correlation_decay` applies **directly** to our
  `connected2pt`, bypassing FP.

So FP only matters for the 2D path (which needs *spatial
factorisation*, a physically different statement).

**Revised work items:**

### W1'. Define `ymMeasure` and relate it to `ymExpect`

File: `LGT/MassGap/YMMeasure.lean`.

Currently the file only has `ymDensity` (a real-valued function)
and `ymExpect` (a quotient of integrals). No actual measure.

**Task:** define

```lean
def ymMeasure (β : ℝ) (plaq : Finset (LatticePlaquette d N)) :
    Measure (GaugeConnection G d N) :=
  (productHaar G d N).withDensity
    (fun U => ENNReal.ofReal (ymDensity G n d N β plaq U))
```

Prove:
- `ymMeasure_isProb` (given `Z > 0` and integrability) — total mass 1.
- `ymExpect_eq_integral_ymMeasure`: `ymExpect f = ∫ f ∂ymMeasure`.
- `connected2pt_eq_covariance`: rewrite `connected2pt` as
  `∫ (f-⟨f⟩)(g-⟨g⟩) dymMeasure` or directly as
  `(∫fg dμ)(∫1 dμ) - (∫f dμ)(∫g dμ)` (matches the
  `dobrushin_correlation_decay` output shape).

**Difficulty.** EASY-MEDIUM. Mostly bookkeeping around
`withDensity`, `integral_withDensity_eq_integral_smul`.

### W2'. Prove `IsGibbsMeasure (ymGibbsSpec β …) ymMeasure`

File: new `LGT/Gibbs/YMIsGibbs.lean`.

**Mathematical content.** The DLR equation:
for every `Λ` and every bounded measurable `f`,
`∫ f dymMeasure = ∫ (∫ f(U) dgibbsCondMeasure(Λ,σ)(U)) dymMeasure(σ)`.

On a finite lattice, this follows by unfolding
`gibbsCondMeasure Λ σ = (productHaar.map (glue σ)).withDensity (w/Z(σ))`
and using Fubini + the factorisation of `productHaar` into
`productHaar|_Λ ⊗ productHaar|_Λᶜ`. The partition-function
ratio `Z(σ)/Z` comes out as a reweighting; the overall identity
is the standard Wilson-DLR equation and is mechanical given
Fubini on finite product Haar.

**Difficulty.** MEDIUM. Much of the scaffolding
(`gluedConfig`, `gibbsConditionalWeight`, `gibbsCondMeasure`,
`gibbsCondMeasure_total`) already exists; we're assembling those
pieces into the DLR identity.

### W3'. Wire d≥3 correlation bound via `dobrushin_correlation_decay_nn_direct`

File: `LGT/MassGap/GaugeFixing.lean:156-172`.

**Revised target (2026-04-15, per external-agent update).** The
markov-semigroups agent is adding two new variants to replace the
single-Neumann-series `dobrushin_correlation_decay`:

```
dobrushin_correlation_decay_direct (general I):
  hCov : |Cov(f,g)| ≤ C · iterateInfluence γ n x y
  ⊢ |Cov(f,g)| ≤ C · α^n

dobrushin_correlation_decay_nn_direct (lattice, n = latticeDist x y):
  hCov : |Cov(f,g)| ≤ C · iterateInfluence γ (latticeDist x y) x y
  ⊢ |Cov(f,g)| ≤ C · α^{latticeDist x y}
```

Key differences from the prior `dobrushin_correlation_decay`:
- Bridge hypothesis is `|Cov| ≤ C · iterateInfluence γ d x y`, not
  `|Cov| ≤ C · α^d` — i.e. the `α^d` reduction is now supplied by
  the theorem, and the caller only needs the iterated-influence
  intermediate from an iterated single-site coupling argument.
- The `4B²` factor folds into `C`.
- No `1/(1-α)` factor; rate is `−log α`.

Replace the identity-function `hBridge → hBridge` with:

1. Translate `connected2pt` to the covariance form (W1':
   `ymExpect_eq_integral_ymMeasure`).
2. Apply `dobrushin_correlation_decay_nn_direct` with
   `γ = ymGibbsSpec β …`, `hD = ymDobrushinCondition …` (existing),
   `C = 4 n²`.
3. **New bridge hypothesis: `hIterInf`**, supplying
   `|Cov| ≤ 4 n² · iterateInfluence γ (latticeDist x y) x y`
   from the FP + iterated-coupling argument. This is the right
   shape — an iterated single-site coupling along a `d`-step path
   from `y` to `x` via `marginalTvDist_contraction` — and is much
   smaller/more canonical than the full `α^d` bound.
4. Locality: `plaqObs p` depends only on the four links of
   plaquette `p`. Choose representative link per plaquette; bound
   `plaquetteDist p q ≤ C · latticeDist (rep p) (rep q)`.

**Status of dep.** The vendored `.lake/packages/MarkovSemigroups`
is at `b1664bf` (influenceCoeff marginal-TV fix), predating the
`_direct` variants. W3' is blocked until the dep is bumped.

**Difficulty.** MEDIUM. Once the dep lands, W3' is a direct call
with the `hIterInf` bridge as its only remaining input.

### W4' (= old W1 + W3). Faddeev-Popov + spatial factorisation for 2D

File: `LGT/MassGap/GaugeFixing.lean:124` — the 2D bound.

Unchanged from the prior plan: W1 (real FP) and W3 (spatial
factorisation via FP) collapse into a single multi-step workstream
for the 2D theorem, feeding `doeblin_correlation_decay` (which
is already fully proved in markov-semigroups).

**Difficulty.** HARD. Deferred until W1'–W3' land.

---

## Prior work items (preserved for context)

The original decomposition assumed FP was needed first; preserved
here so prior decisions remain auditable.

### W1. `faddeevPopov` — discharge the measure-decomposition `sorry`

File: `LGT/MassGap/GaugeFixing.lean:81-88`
(Currently accepts `hFP : ymExpect … = gfExpect` and returns it.)

**Mathematical content.** On a finite lattice with product Haar
$\mu = \bigotimes_\ell \text{Haar}_G$:

1. Pick an axial gauge tree $T$ (e.g. all temporal links at fixed
   spatial slice). Links decompose as $T \sqcup T^c$.
2. For each configuration $U$, the gauge transform $g(U)$ that
   sends $U|_T$ to identity is measurable, pointwise well-defined.
3. By Fubini on $G^T \times G^{T^c}$ and Haar left-invariance on
   each factor, $\mu$-integrals of gauge-invariant $f$ equal the
   same integrals restricted to $\{U : U|_T = 1\}$ times $|T|$
   copies of $\int d\mu_{\text{Haar}} = 1$.

**Lean decomposition.** Break into:

- `W1a`: Product-measure Fubini on `productHaar G d N` with an
  explicit link partition. Mathlib: `MeasureTheory.Measure.pi` and
  `Measure.integral_prod` / `Measure.pi_unique`.
- `W1b`: Pointwise gauge transform $g(U)$ that zeroes axial links.
  Uses existing `GaugeTransform` + the axial tree construction.
- `W1c`: Haar left-invariance per link: `MeasureTheory.Measure.haar.
  map_mul_left_eq_self` applied factor-wise.
- `W1d`: Assemble `faddeevPopov` without `hFP`.

**Estimated difficulty.** MEDIUM-HARD. The measurability of the
pointwise gauge transform and the Fubini bookkeeping over a
`Fintype`-indexed product are where time will go. Axial tree
existence on periodic $(\mathbb Z/N\mathbb Z)^d$ needs care (the
torus has no spanning tree of axial links — have to drop one link
per cycle). The current file's docstring already says "the axial
links form a tree connecting all lattice sites" which is not quite
true on the torus; need to revisit.

### W2. Wire `ymGibbsSpec` into `dobrushin_correlation_bound`

File: `LGT/MassGap/GaugeFixing.lean:156-172`.

After W1 the YM expectation equals the gauge-fixed expectation, so
`connected2pt` under `ymExpect` equals `connected2pt` under the
Gibbs measure determined by `ymGibbsSpec`. Then apply
`dobrushin_correlation_decay`.

**Mathematical content.**

1. **Index translation.** `dobrushin_correlation_decay` indexes on
   `LatticeSite d` with spin space `S`. Our state space is
   `LatticeLink d N → G`, indexed on `LatticeLink d N`. Need an
   instance or wrapper identifying `I = LatticeLink d N`, `S = G`.
   The `GibbsSpec` definition is parameterised on the index type,
   so this should just be a direct application — `ymGibbsSpec`
   already lives over `LatticeLink d N`.
2. **Gibbs measure witness.** Need `μ : Measure (SpinConfig …)` with
   `IsGibbsMeasure (ymGibbsSpec β) μ`. On the finite lattice this
   is the explicit Boltzmann-weighted product Haar normalised by
   $Z$. Likely already constructible from existing definitions in
   `YMSpec.lean` (the consistency + properness lemmas at
   lines 222–304 suggest the measure exists).
3. **Locality translation.** `plaqObs G n d N p` depends only on the
   four links of plaquette $p$, so it is $\{p\}$-local in the
   plaquette indexing and at worst $4$-link-local in the link
   indexing. `dobrushin_correlation_decay` wants the observable to
   depend only on one site. Either:
   - (a) replace `latticeDist x y` with `plaquetteDist d N p q`
     and treat plaquettes as sites (reformulate spec at plaquette
     level — large refactor); OR
   - (b) apply the theorem at the level of links, choosing a
     representative link for each plaquette, then bound
     `plaquetteDist p q` by link distance up to a constant.
   Option (b) is lower-effort.
4. **Bridge hypothesis flow-through.** While the external
   `hDecay` hypothesis persists in markov-semigroups, we pass it
   through as our own top-level hypothesis, narrowed to the
   concrete column sum. Once the external agent lands the proof,
   we delete our pass-through.

**Estimated difficulty.** MEDIUM. Most of the difficulty is the
index/site-vs-plaquette translation; mathematically straightforward.

### W3. Wire `doeblin_correlation_decay` into the 2D bound

File: `LGT/MassGap/GaugeFixing.lean:124-144`.

2D is a harder physical reduction (spatial factorisation into
independent temporal chains) but the abstract theorem it feeds —
`doeblin_correlation_decay` — is already fully proved. So this
work item needs:

1. **Spatial factorisation lemma.** After axial gauge fixing in 2D,
   the gauge-fixed measure is a product over spatial sites of
   independent chains (temporal-link sequences). Needs a real Lean
   lemma: `gfMeasure_eq_spatial_product`.
2. **Single-site Markov kernel.** Identify each temporal chain
   with a `MarkovKernel G`. `SingleSiteKernel.lean` likely already
   has this.
3. **Apply `doeblin_correlation_decay`.** Instantiate with
   `ε = ymDoeblinLowerBound n β`, the single-site observables at
   temporal distance $d$.
4. **Independence when spatial sites differ.** If $s_p \ne s_q$
   the observables are independent, so `connected2pt = 0`. Pure
   Fubini on the spatial-product structure.

**Estimated difficulty.** HARD. The spatial factorisation on the
torus (periodic BC) is genuinely subtle and is what Chatterjee
§15.5–15.7 does by hand. This is the content of the 2D mass gap.

## Dependency graph (revised)

```
W1' ymMeasure + ymExpect bridge       (EASY-MEDIUM, ~150 lines)
  │
  └─→ W2' IsGibbsMeasure (ymGibbsSpec) ymMeasure   (MEDIUM, ~250 lines)
        │
        └─→ W3' Wire d≥3 correlation bound         (MEDIUM, ~150 lines)
              ├── plaquette↔link locality translation
              └── apply dobrushin_correlation_decay  [passes through
                                                      external hDecay]

W4' Faddeev-Popov + spatial factorisation for 2D  (HARD, ~500 lines)
  (independent branch; deferred)
```

## Order of attack (revised)

1. **W1' first** — define `ymMeasure`, prove expectations.
   Mechanical. Unlocks everything else.
2. **W2' next** — the DLR identity. The bulk of the remaining
   real mathematical content.
3. **W3' after W2'.** Short. Delivers the d≥3 mass gap modulo
   the external `hDecay` hypothesis.
4. **W4' last.** The 2D story. Independent of W1'–W3'.

## Estimated effort (revised)

| Item | Lines | Difficulty |
|---|---|---|
| W1' `ymMeasure` definition + `ymExpect` bridge | ~150 | EASY-MEDIUM |
| W2' `IsGibbsMeasure ymGibbsSpec ymMeasure` | ~250 | MEDIUM |
| W3' Wire d≥3 to `dobrushin_correlation_decay` | ~150 | MEDIUM |
| W4' 2D Faddeev-Popov + spatial factorisation | ~500 | HARD |
| **Total (d≥3 path only: W1'+W2'+W3')** | **~550** | |
| **Total (full Phase 3)** | **~1050** | |

## What stays as hypothesis after Phase 3

- The external `hDecay` inside
  `dobrushin_correlation_decay` — until the markov-semigroups
  agent finishes, W2 propagates it as a single top-level
  hypothesis named something like `hGeomDecay`. Once the external
  work lands, that one line disappears and `ym_mass_gap_2pt`
  becomes fully unconditional.

- Nothing else, assuming W1–W3 land cleanly.

## References

- `PLAN_YM_GIBBS.md` — the original Phase 1/2 plan (done).
- `.lake/packages/MarkovSemigroups/MarkovSemigroups/Dobrushin/Uniqueness.lean:826`
- `.lake/packages/MarkovSemigroups/MarkovSemigroups/Convergence/Doeblin.lean:310`
- `LGT/Gibbs/YMSpec.lean`, `LGT/Gibbs/YMDobrushin.lean`
- Chatterjee (2026), §15.5–15.7 (2D), §16.3 (d≥3 strong coupling)
