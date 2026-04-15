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

/-! ## The YM Gibbs specification (scaffold)

This is the main construction. Many of the verifications (measurability,
properness, consistency) require careful product-measure arguments.
Included here as definitions; proofs of the structure axioms are
left as future work. -/

/-- The YM Gibbs specification on the link lattice.

The conditional distribution γ(Λ, σ) is the product Haar measure on
Λ-links, weighted by exp(-S) and normalized, glued with σ outside Λ.

This definition is partial — the full structure verification
(properness, measurability, consistency) requires significant
product-measure infrastructure. The purpose of this file is to
expose the precise construction needed. -/
def gaugeFixedYMSpec (β : ℝ) : Type _ :=
  -- The full GibbsSpec construction (see PLAN_YM_GIBBS.md):
  -- condDist := fun Λ σ =>
  --   let weight := gibbsConditionalWeight G n d N plaq β Λ σ
  --   let Z := gibbsConditionalZ G n d N plaq β Λ σ
  --   ((Measure.pi (fun _ => haarG G)).withDensity (weight / Z) ⊗ δ_σ on Λᶜ).map glue
  -- (See LGT/Gibbs/YMSpec/Construction.lean for the explicit construction.)
  GibbsSpec (LatticeLink d N) G

end
