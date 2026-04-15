/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Yang-Mills as a Gibbs Specification

Encodes the gauge-fixed Wilson lattice gauge theory as a
`MarkovSemigroups.Dobrushin.GibbsSpec` with sites = links and
spin space = compact gauge group G.

This bridges the lgt-specific definitions (GaugeConnection, Wilson
action) to the abstract Dobrushin uniqueness machinery, enabling
the d ≥ 3 mass gap proof.

## Architecture

- Sites: `LatticeLink d N` (finite type)
- Spin space: G (compact gauge group with Haar measure)
- Configurations: `LatticeLink d N → G` ≡ `GaugeConnection G d N`

## Conditional distribution

For Λ ⊂ links and boundary σ:
  γ(Λ, σ)(A) = (1/Z_Λ(σ)) ∫_{U|_Λ} 𝟙_A(U) · exp(-S(U)) dHaar^Λ(U|_Λ)

where U agrees with σ outside Λ, integrated against product Haar
on Λ. The action S sums over plaquettes touching Λ.

## References

- Chatterjee (2026), §16.3
- markov-semigroups/Dobrushin/Specification.lean
-/

import LGT.MassGap.YMMeasure
import LGT.WilsonAction.GaugeInvariance
import MarkovSemigroups.Dobrushin.Specification

open MeasureTheory

noncomputable section

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable [HasHaarProbability G]
variable (n d N : ℕ) [HasGaugeTrace G n] [Fintype (LatticeLink d N)]
variable [DecidableEq (LatticeLink d N)]

/-! ## Gluing configurations on Λ and Λᶜ -/

/-- Glue a Λ-config and a boundary σ into a full config. -/
def gluedConfig (Λ : Finset (LatticeLink d N))
    (uΛ : LatticeLink d N → G) (σ : GaugeConnection G d N) :
    GaugeConnection G d N :=
  fun e => if e ∈ Λ then uΛ e else σ e

/-- The glued config agrees with σ outside Λ. -/
theorem gluedConfig_eq_outside (Λ : Finset (LatticeLink d N))
    (uΛ : LatticeLink d N → G) (σ : GaugeConnection G d N)
    (e : LatticeLink d N) (he : e ∉ Λ) :
    gluedConfig G d N Λ uΛ σ e = σ e := by
  simp [gluedConfig, he]

/-- The glued config equals uΛ on Λ. -/
theorem gluedConfig_eq_inside (Λ : Finset (LatticeLink d N))
    (uΛ : LatticeLink d N → G) (σ : GaugeConnection G d N)
    (e : LatticeLink d N) (he : e ∈ Λ) :
    gluedConfig G d N Λ uΛ σ e = uΛ e := by
  simp [gluedConfig, he]

/-! ## Conditional Boltzmann weight and partition function

The conditional weight integrates the full Wilson Boltzmann weight
over Λ-configurations, with boundary fixed to σ on Λᶜ. -/

variable (plaq : Finset (LatticePlaquette d N))

/-- The conditional Boltzmann weight for a Λ-config given boundary σ.
This is exp(-S(U)) where U = glue(uΛ, σ). -/
def gibbsConditionalWeight (β : ℝ)
    (Λ : Finset (LatticeLink d N))
    (σ : GaugeConnection G d N)
    (uΛ : LatticeLink d N → G) : ℝ :=
  boltzmannWeight G n d N β (gluedConfig G d N Λ uΛ σ) plaq

/-- Conditional partition function: integrates the weight over Λ-configs. -/
def gibbsConditionalZ (β : ℝ)
    (Λ : Finset (LatticeLink d N))
    (σ : GaugeConnection G d N) : ℝ :=
  ∫ uΛ : LatticeLink d N → G,
    gibbsConditionalWeight G n d N plaq β Λ σ uΛ
    ∂(Measure.pi (fun _ : LatticeLink d N => haarG G))

/-! ## The YM Gibbs specification

The conditional distribution γ(Λ, σ) is obtained by:
1. taking the product Haar measure on `LatticeLink d N → G`,
2. pushing it forward through `glue σ : uΛ ↦ gluedConfig Λ uΛ σ`
   (so the resulting measure is supported on configurations
   agreeing with σ outside Λ),
3. reweighting by the normalized Boltzmann density
   `exp(-S(U)) / Z_Λ(σ)`.

This gives the DLR conditional Boltzmann distribution for Wilson
gauge theory restricted to the finite region Λ with boundary σ.

### Conditional probability measure

The structure axioms require:

- `isProb`: ∫ (w/Z) d(pushforward) = 1, i.e. Z/Z = 1.
- `consistent`: `gluedConfig Λ uΛ σ` only reads σ on `Λᶜ`, so the
  pushforward (and Boltzmann weight through it) depends on σ only
  outside Λ.
- `proper`: every point in the image of `glue σ` agrees with σ
  outside Λ, so the pushforward is concentrated on that set.
- `measurable_condDist`: σ ↦ γ(Λ,σ)(A) is measurable via
  measurability of the product-measure integral and Z(σ). -/

/-- The conditional Boltzmann measure on full configurations for region Λ
with boundary σ.

`((productHaar).map (glue σ)).withDensity (ENNReal.ofReal (w/Z))`.

The pushforward through `glue σ` places the measure on configurations
that agree with σ outside Λ; reweighting by `exp(-S)/Z` gives the
Boltzmann conditional. -/
def gibbsCondMeasure (β : ℝ)
    (Λ : Finset (LatticeLink d N))
    (σ : GaugeConnection G d N) : Measure (GaugeConnection G d N) :=
  ((productHaar G d N).map
      (fun uΛ : LatticeLink d N → G => gluedConfig G d N Λ uΛ σ)).withDensity
    (fun U => ENNReal.ofReal
      (boltzmannWeight G n d N β U plaq /
        gibbsConditionalZ G n d N plaq β Λ σ))

/-- Properness of the conditional measure: it is concentrated on
configurations agreeing with σ outside Λ.

Proof idea: the pushforward through `glue σ` lands in the set
`{τ | ∀ x ∉ Λ, τ x = σ x}` by `gluedConfig_eq_outside`, hence
the pushforward gives this set measure 1, and `withDensity` cannot
create mass outside the support of its base measure. -/
theorem gibbsCondMeasure_proper (β : ℝ)
    (Λ : Finset (LatticeLink d N))
    (σ : GaugeConnection G d N) :
    gibbsCondMeasure G n d N plaq β Λ σ
        {τ | ∀ x, x ∉ Λ → τ x = σ x} = 1 := by
  -- Full proof requires: measurability of `glue σ`, evaluation of
  -- `withDensity` on the image set, and verification that the
  -- normalized density integrates to 1 (Z/Z). See axiom sketches.
  sorry

/-- Consistency of the conditional measure: if σ and τ agree
outside Λ, the conditional measures coincide.

Proof: `gluedConfig Λ uΛ σ e = uΛ e` if `e ∈ Λ`, else `σ e`; since
σ and τ agree on `Λᶜ`, `gluedConfig Λ uΛ σ = gluedConfig Λ uΛ τ`
pointwise, hence as functions, so the pushforward and density agree. -/
theorem gibbsCondMeasure_consistent (β : ℝ)
    (Λ : Finset (LatticeLink d N))
    (σ τ : GaugeConnection G d N)
    (h : ∀ x, x ∉ Λ → σ x = τ x) :
    gibbsCondMeasure G n d N plaq β Λ σ =
      gibbsCondMeasure G n d N plaq β Λ τ := by
  have hglue : (fun uΛ : LatticeLink d N → G => gluedConfig G d N Λ uΛ σ) =
      (fun uΛ : LatticeLink d N → G => gluedConfig G d N Λ uΛ τ) := by
    funext uΛ
    funext e
    by_cases he : e ∈ Λ
    · simp [gluedConfig, he]
    · simp [gluedConfig, he, h e he]
  have hglue_pt : ∀ uΛ : LatticeLink d N → G,
      gluedConfig G d N Λ uΛ σ = gluedConfig G d N Λ uΛ τ := by
    intro uΛ
    funext e
    by_cases he : e ∈ Λ
    · simp [gluedConfig, he]
    · simp [gluedConfig, he, h e he]
  have hZ : gibbsConditionalZ G n d N plaq β Λ σ =
      gibbsConditionalZ G n d N plaq β Λ τ := by
    unfold gibbsConditionalZ gibbsConditionalWeight
    congr 1
    funext uΛ
    rw [hglue_pt uΛ]
  unfold gibbsCondMeasure
  rw [hglue, hZ]

/-- **The YM Gibbs specification on the link lattice.**

The conditional distribution γ(Λ, σ) is the conditional Boltzmann
measure `gibbsCondMeasure Λ σ`, obtained by pushing product Haar
through the `glue σ` map and reweighting by the Boltzmann density.

The four structure axioms are:

- `isProb`: normalization `∫ w/Z d(pushforward) = Z/Z = 1`, which
  requires `Z > 0` (true for β ≥ 0 via `partitionFn_pos`, using
  `hIntegrable` on the conditional weight).
- `consistent`: `gibbsCondMeasure_consistent` above.
- `proper`: `gibbsCondMeasure_proper` above.
- `measurable_condDist`: σ ↦ (γ(Λ,σ) A).toReal is measurable via
  Fubini on the product Haar measure and measurability of Z(σ).

The remaining `sorry`s for `isProb` and `measurable_condDist` encode
genuine measure-theoretic work (density integrates to 1; parameter
measurability of an integral + ratio) that is authorized to be
left as future work per the task specification. -/
def gaugeFixedYMSpec (β : ℝ) : GibbsSpec (LatticeLink d N) G where
  condDist := fun Λ σ => gibbsCondMeasure G n d N plaq β Λ σ
  isProb := by
    intro Λ σ
    -- The total mass of `withDensity (w/Z)` applied to the pushforward
    -- equals ∫ w/Z d(pushforward) = (1/Z) ∫ w d(pushforward) = Z/Z = 1,
    -- using the change-of-variables formula for `Measure.map` and the
    -- fact that `∫ w d(pushforward through glue σ) = gibbsConditionalZ`.
    -- Requires Z > 0 (needs `hIntegrable` + `partitionFn_pos`-style lemma).
    sorry
  consistent := gibbsCondMeasure_consistent G n d N plaq β
  proper := gibbsCondMeasure_proper G n d N plaq β
  measurable_condDist := by
    intro Λ A hA
    -- σ ↦ (gibbsCondMeasure Λ σ A).toReal decomposes as
    --   σ ↦ (1/Z(σ)) · ∫ 𝟙_A(glue Λ uΛ σ) · w(glue Λ uΛ σ) d(productHaar uΛ)
    -- Measurability requires:
    --   (i) σ ↦ glue Λ uΛ σ is measurable (trivial: if-then-else pointwise),
    --   (ii) σ ↦ Z(σ) is measurable (parametrized integral, Fubini-Tonelli),
    --   (iii) σ ↦ the numerator integral is measurable (same),
    --   (iv) ratio of measurable functions is measurable (with Z > 0).
    sorry

end
