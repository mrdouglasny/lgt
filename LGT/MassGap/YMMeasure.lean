/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Yang-Mills Measure on the Lattice

Defines the Yang-Mills probability measure on gauge field configurations
for a compact gauge group G on a finite lattice.

## Definitions

- `haarG` — normalized Haar probability measure on G
- `productHaar` — product Haar measure on G^{links} (prior measure)
- `wilsonBoltzmann` — Boltzmann weight exp(-β · S(U)) for Wilson action
- `ymMeasure` — Yang-Mills probability measure (Boltzmann × Haar / Z)
- `ymExpect` — expectation under the YM measure
- `connected2pt` — connected 2-point function ⟨fg⟩ - ⟨f⟩⟨g⟩

## References

- Chatterjee (2026), §15.3–15.4
-/

import LGT.Lattice.CellComplex
import LGT.GaugeField.Connection
import LGT.GaugeField.GaugeGroup
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod

open MeasureTheory

noncomputable section

variable (G : Type*) [Group G] [TopologicalSpace G] [CompactSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

-- For finite lattices, the gauge configuration space is a finite product
-- G^{links}. We use the product sigma-algebra.
instance instMeasurableSpaceGaugeConnection (d N : ℕ) :
    MeasurableSpace (GaugeConnection G d N) := MeasurableSpace.pi

/-! ## Haar probability measure on compact G -/

/-- The normalized Haar probability measure on a compact group G.
For compact G, the Haar measure can be normalized to total mass 1.
We assume this as a hypothesis; Mathlib provides it via
`haarMeasure` on `PositiveCompacts G` after normalization. -/
class HasHaarProbability (G : Type*) [MeasurableSpace G] where
  haar : Measure G
  isProb : IsProbabilityMeasure haar

attribute [instance] HasHaarProbability.isProb

variable [HasHaarProbability G]

/-- The Haar probability measure on G. -/
def haarG : Measure G := HasHaarProbability.haar (G := G)

instance : IsProbabilityMeasure (haarG G) := HasHaarProbability.isProb

/-! ## Product measure on gauge configurations -/

variable (n : ℕ) [HasGaugeTrace G n]
variable (d N : ℕ)

/-- The set of links on the lattice (ℤ/Nℤ)^d. -/
abbrev Links := LatticeLink d N

/-- A gauge configuration assigns a group element to each link. -/
abbrev Config := Links d N → G

/-- The set of plaquettes on the lattice. -/
abbrev Plaquettes := LatticePlaquette d N

/-! ## Wilson action and Boltzmann weight -/

/-- The Wilson action: S(U) = Σ_p β · (n - Re Tr(U_p)).
Takes a finite set of plaquettes to sum over. -/
def wilsonAction (β : ℝ) (U : GaugeConnection G d N)
    (plaq : Finset (Plaquettes d N)) : ℝ :=
  ∑ p ∈ plaq, β * wilsonPlaquetteCost G n (plaquetteHolonomy U p)

/-- The Boltzmann weight: exp(-S(U)). -/
def boltzmannWeight (β : ℝ) (U : GaugeConnection G d N)
    (plaq : Finset (Plaquettes d N)) : ℝ :=
  Real.exp (-(wilsonAction G n d N β U plaq))

/-- The Boltzmann weight is always positive. -/
theorem boltzmannWeight_pos (β : ℝ) (U : GaugeConnection G d N)
    (plaq : Finset (Plaquettes d N)) :
    0 < boltzmannWeight G n d N β U plaq :=
  Real.exp_pos _

/-! ## Yang-Mills expectation value

The YM expectation of an observable f : Config → ℝ is:
  ⟨f⟩ = (1/Z) ∫ f(U) · exp(-S(U)) dμ_Haar(U)
where Z = ∫ exp(-S(U)) dμ_Haar(U) is the partition function.

For a finite lattice with compact G, the product Haar measure
on G^{links} is a probability measure, and the Boltzmann weight
is bounded, so all integrals are finite. -/

/-- The partition function Z = ∫ exp(-S(U)) dμ. -/
def partitionFn (β : ℝ) (plaq : Finset (Plaquettes d N))
    (μ : Measure (GaugeConnection G d N)) : ℝ :=
  ∫ U, boltzmannWeight G n d N β U plaq ∂μ

/-- The YM expectation: ⟨f⟩ = (1/Z) ∫ f · exp(-S) dμ. -/
def ymExpect (β : ℝ) (plaq : Finset (Plaquettes d N))
    (μ : Measure (GaugeConnection G d N))
    (f : GaugeConnection G d N → ℝ) : ℝ :=
  (∫ U, f U * boltzmannWeight G n d N β U plaq ∂μ) /
  partitionFn G n d N β plaq μ

/-- The connected 2-point function: ⟨f·g⟩ - ⟨f⟩·⟨g⟩. -/
def connected2pt (β : ℝ) (plaq : Finset (Plaquettes d N))
    (μ : Measure (GaugeConnection G d N))
    (f g : GaugeConnection G d N → ℝ) : ℝ :=
  ymExpect G n d N β plaq μ (fun U => f U * g U) -
  ymExpect G n d N β plaq μ f * ymExpect G n d N β plaq μ g

/-- The plaquette observable at a specific plaquette. -/
def plaqObs (p : Plaquettes d N) : GaugeConnection G d N → ℝ :=
  fun U => gaugeReTr G n (plaquetteHolonomy U p)

/-- Plaquette observables are bounded by n (since |Re Tr| ≤ n for G ⊂ U(n)). -/
theorem plaqObs_bounded (p : Plaquettes d N) (U : GaugeConnection G d N)
    (hTrace : ∀ g : G, |gaugeReTr G n g| ≤ ↑n) :
    |plaqObs G n d N p U| ≤ ↑n :=
  hTrace _

end
