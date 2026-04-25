# Plan: Encoding Yang-Mills as a Gibbs Specification

*2026-04-15*

The remaining work to complete the d ≥ 3 YM mass gap proof is to fill the
two `hBridge` hypotheses in `LGT/MassGap/GaugeFixing.lean`:

1. `dobrushin_correlation_bound`: bridge from YM connected 2-point to
   `dobrushin_correlation_decay` in markov-semigroups
2. `doeblin_correlation_bound_2d`: bridge from 2D YM to product Markov
   chain via spatial factorization

This document focuses on (1) since (2) follows similar patterns but with
a simpler product structure.

## Goal

Prove `dobrushin_correlation_bound` in `LGT/MassGap/GaugeFixing.lean`:

```
|connected2pt(f, g)| ≤ 4B²·(dobrushinAlpha n d β)^dist
```

for gauge-fixed YM with β small enough.

## Architecture

```
LGT.GaugeYMSpec  (NEW)
  Encode gauge-fixed YM as a markov-semigroups GibbsSpec
  ├── condDist Λ σ  : conditional Boltzmann measure on Λ-links
  ├── isProb        : probability measure
  ├── consistent    : depends only on σ outside Λ
  ├── proper        : concentrates on agreeing configs
  └── measurable    : σ ↦ condDist Λ σ A measurable

LGT.GaugeYMNearestNeighbor  (NEW)
  Verify the Dobrushin hypotheses for the YM specification
  ├── IsNearestNeighbor     : plaquette interactions are local
  ├── InteractionBound β    : C(x,y) ≤ 2nβ for shared plaquettes
  └── DobrushinCondition    : 4(d-1)·2nβ < 1 for β < 1/(8n(d-1))

LGT.MassGap.GaugeFixing (UPDATE)
  Wire YM Gibbs spec into Dobrushin correlation decay
  └── dobrushin_correlation_bound
        ├── faddevPopov (proved): YM expectation = gauge-fixed expectation
        ├── encode YM as GibbsSpec (above)
        ├── verify Dobrushin column sum < 1 (already: dobrushin_sufficient)
        └── apply dobrushin_correlation_decay (markov-semigroups)
```

## Step-by-step plan

### Phase 1: Define the YM Gibbs specification (~300 lines)

Create `LGT/Gibbs/YMSpec.lean`:

```lean
import LGT.WilsonAction.PlaquetteAction
import MarkovSemigroups.Dobrushin.Specification

open MeasureTheory

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [MeasurableSpace G] [BorelSpace G] [HasHaarProbability G]
variable (n d N : ℕ) [HasGaugeTrace G n] [Fintype (LatticeLink d N)]

/-- Conditional Boltzmann weight for a region Λ given boundary σ.
  W_Λ(U, σ) = exp(-β · Σ_{p touches Λ} (n - Re Tr(U_p)))
where U agrees with σ outside Λ. -/
def gibbsConditionalWeight (β : ℝ) (Λ : Finset (LatticeLink d N))
    (σ : LatticeLink d N → G) (U : LatticeLink d N → G) : ℝ :=
  Real.exp (-β * Σ_{p : LatticePlaquette d N} ...)

/-- Conditional partition function: integrates the weight over Λ-configs
with boundary fixed to σ on Λᶜ. -/
def gibbsConditionalZ (β : ℝ) (Λ : Finset (LatticeLink d N))
    (σ : LatticeLink d N → G) : ℝ := ...

/-- The YM Gibbs specification on the link lattice. -/
def gaugeFixedYMSpec (β : ℝ) :
    GibbsSpec (LatticeLink d N) G := {
  condDist := fun Λ σ => ...  -- conditional Boltzmann measure
  isProb := ...                -- probability via Z
  consistent := ...            -- by construction (depends on σ|Λᶜ only)
  proper := ...                -- by construction (Dirac outside Λ)
  measurable_condDist := ...   -- continuous in σ via continuous action
}
```

**Hard parts:**
- Z(σ) > 0: needs continuous positive integrand on compact group
- Measurability of σ ↦ Z(σ): product measurability + continuous functions
- Properness: requires the Haar^Λ ⊗ Dirac_σ construction

**Mathlib tools:**
- `MeasureTheory.Measure.pi` for product Haar
- `Measure.dirac` for boundary
- `Continuous.comp` for measurable conditional weights

### Phase 2: Verify nearest-neighbor structure (~200 lines)

Create `LGT/Gibbs/YMNearestNeighbor.lean`:

```lean
/-- Two links are neighbors iff they share a plaquette. -/
def isLinkNeighbor (e e' : LatticeLink d N) : Prop :=
  ∃ p : LatticePlaquette d N, e ∈ plaquetteLinks p ∧ e' ∈ plaquetteLinks p

/-- The YM specification only depends on neighbors. -/
theorem ym_isNearestNeighbor (β : ℝ) :
    IsNearestNeighbor (gaugeFixedYMSpec G n d N β) := by
  -- Single-link conditional depends only on neighbors via plaquettes
  ...

/-- TV bound on single-link conditional when one neighbor changes. -/
theorem ym_interactionBound (β : ℝ) (hβ : 0 ≤ β) :
    InteractionBound (gaugeFixedYMSpec G n d N β) (2 * n * β) := by
  -- Action change ≤ 2n when one link changes ⟹ TV bound ≤ 1 - exp(-2nβ) ≤ 2nβ
  ...
```

**Mathematical content:**
- Plaquette structure: each link borders ≤ 2(d-1) plaquettes in d dims
- Energy oscillation: changing one link changes |Re Tr| by at most 2n per shared plaquette
- TV bound from Boltzmann ratio: TV ≤ 1 - exp(-osc·β) ≤ osc·β

### Phase 3: Wire into the correlation bound (~100 lines)

Update `LGT/MassGap/GaugeFixing.lean`:

```lean
theorem dobrushin_correlation_bound
    (β : ℝ) (hβ : 0 ≤ β)
    (hd : 2 ≤ d) (hn : 1 ≤ n)
    (hβ_small : β < 1 / (2 * n * maxNeighbors d))
    ... :
    |connected2pt G n d N β plaq f g| ≤ 4 * B^2 * (dobrushinAlpha n d β)^dist := by
  -- Step 1: Faddeev-Popov: connected2pt under YM = under gauge-fixed
  rw [faddeevPopov ...]
  -- Step 2: Get the Dobrushin condition via strong_coupling
  have hD := strong_coupling_dobrushin (gaugeFixedYMSpec G n d N β)
    (ym_isNearestNeighbor G n d N β) (2*n*β) (ym_interactionBound G n d N β hβ) ...
  -- Step 3: Apply dobrushin_correlation_decay (with bridge hypothesis)
  exact dobrushin_correlation_decay ... hD ...
```

## Estimated effort

| Phase | Content | Lines | Difficulty |
|-------|---------|-------|------------|
| 1 | YM Gibbs spec definition + verification | ~300 | HARD (measurability) |
| 2 | Nearest-neighbor + interaction bound | ~200 | MEDIUM (algebra) |
| 3 | Wire correlation bound | ~100 | EASY |
| **Total** | | **~600** | |

## What's still missing (deeper)

Even after this work, two pieces remain abstract:

1. **`dobrushin_correlation_decay` in markov-semigroups** still has the
   Neumann series `hDecay` bridge hypothesis. To remove it: prove
   conditional measure factorization + iterated coupling along paths.
   Estimated: ~400 lines of measure theory.

2. **`dobrushin_existence`** has the existence bridge hypothesis. The
   YM measure exists by direct construction (compact lattice, finite Z),
   so for the lgt application we don't need the abstract existence —
   we can just construct the YM measure directly and verify it's Gibbs.

## Order of attack

1. **Direct YM measure construction** — define the YM Gibbs measure
   explicitly on the FINITE lattice, prove it's a Gibbs measure for
   `gaugeFixedYMSpec`. This is straightforward (finite product Haar).
   ~100 lines. Avoids needing `dobrushin_existence`.

2. **YM Gibbs spec (Phase 1)** — the conditional distributions.
   Hardest part of the whole project.

3. **Nearest-neighbor verification (Phase 2)** — algebraic, follows
   from existing oscillation bounds in DobrushinVerification.lean.

4. **Wire correlation bound (Phase 3)** — short, mechanical.

5. **Optional: prove `dobrushin_correlation_decay`** — removes the
   remaining bridge hypothesis. Significant Mathlib infrastructure.

## References

- Chatterjee §16.3 (Dobrushin condition for lattice gauge)
- Existing `DobrushinVerification.lean` — already has `dobrushin_sufficient`
- `markov-semigroups/Dobrushin/Specification.lean` — the GibbsSpec target
- `markov-semigroups/Dobrushin/StrongCoupling.lean` — already has the
  IsNearestNeighbor + InteractionBound → DobrushinCondition machinery
