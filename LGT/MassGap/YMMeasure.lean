/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Yang-Mills Measure on the Lattice

Defines the finite-volume Yang-Mills probability measure on gauge field
configurations for a compact gauge group G on a finite lattice.

## Definitions

- `haarG` — normalized Haar probability measure on G
- `productHaar` — product Haar measure on G^{links} (prior measure)
- `boltzmannWeight` — exp(-β · S(U)) for Wilson action
- `partitionFn` — Z = ∫ exp(-S) dμ_Haar, proved > 0
- `ymMeasure` — the Yang-Mills probability measure (Boltzmann × Haar / Z)
- `ymExpect` — expectation ⟨f⟩ under ymMeasure
- `connected2pt` — connected 2-point function ⟨fg⟩ - ⟨f⟩⟨g⟩

## References

- Chatterjee (2026), §15.3–15.4
-/

import LGT.Lattice.LatticeDistance
import LGT.GaugeField.Connection
import LGT.GaugeField.GaugeGroup
import LGT.MassGap.Integrability
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Constructions.Pi

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MeasureTheory

noncomputable section

variable (G : Type*) [Group G] [TopologicalSpace G] [CompactSpace G]
  [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

-- LatticeLink is finite for finite lattices.
-- (GaugeConnection G d N = LatticeLink d N → G needs Fintype for Measure.pi)
-- For now we add this as an assumption where needed.

-- Product sigma-algebra on gauge configurations G^{links}
instance instMeasurableSpaceGaugeConnection (d N : ℕ) :
    MeasurableSpace (GaugeConnection G d N) := MeasurableSpace.pi

/-! ## Haar probability measure on compact G -/

/-- Normalized Haar probability measure on a compact group G.
Every compact group admits a unique bi-invariant probability measure.
Mathlib provides this via `haarMeasure` on `PositiveCompacts G`
after normalization. We package it as a class for convenience. -/
class HasHaarProbability (G : Type*) [MeasurableSpace G] where
  haar : Measure G
  isProb : IsProbabilityMeasure haar

attribute [instance] HasHaarProbability.isProb

variable [HasHaarProbability G]

/-- The Haar probability measure on G. -/
def haarG : Measure G := HasHaarProbability.haar (G := G)

instance : IsProbabilityMeasure (haarG G) := HasHaarProbability.isProb

/-! ## Product Haar measure on configurations -/

variable (n : ℕ) [HasGaugeTrace G n]
variable (d N : ℕ) [Fintype (LatticeLink d N)]

/-- The product Haar measure on gauge configurations G^{links}. -/
def productHaar : Measure (GaugeConnection G d N) :=
  Measure.pi (fun _ : LatticeLink d N => haarG G)

/-! ## Wilson action and Boltzmann weight -/

/-- The Wilson action: S(U) = Σ_p β · (n - Re Tr(U_p)). -/
def wilsonAction (β : ℝ) (U : GaugeConnection G d N)
    (plaq : Finset (LatticePlaquette d N)) : ℝ :=
  ∑ p ∈ plaq, β * wilsonPlaquetteCost G n (plaquetteHolonomy U p)

/-- The Boltzmann weight: w(U) = exp(-S(U)). -/
def boltzmannWeight (β : ℝ) (U : GaugeConnection G d N)
    (plaq : Finset (LatticePlaquette d N)) : ℝ :=
  Real.exp (-(wilsonAction G n d N β U plaq))

/-- The Boltzmann weight is always positive. -/
theorem boltzmannWeight_pos (β : ℝ) (U : GaugeConnection G d N)
    (plaq : Finset (LatticePlaquette d N)) :
    0 < boltzmannWeight G n d N β U plaq :=
  Real.exp_pos _

/-- The Boltzmann weight is ≤ 1 when β ≥ 0 (since S ≥ 0).

S(U) = Σ_p β(n - Re Tr(U_p)) ≥ 0 when β ≥ 0 (as n - Re Tr ≥ 0
for G ⊂ U(n)), so exp(-S) ≤ exp(0) = 1. -/
theorem boltzmannWeight_le_one (β : ℝ) (hβ : 0 ≤ β)
    (U : GaugeConnection G d N)
    (plaq : Finset (LatticePlaquette d N))
    (hTrace : ∀ g : G, gaugeReTr G n g ≤ ↑n) :
    boltzmannWeight G n d N β U plaq ≤ 1 := by
  unfold boltzmannWeight
  rw [Real.exp_le_one_iff]
  apply neg_nonpos_of_nonneg
  unfold wilsonAction
  apply Finset.sum_nonneg
  intro p _
  apply mul_nonneg hβ
  unfold wilsonPlaquetteCost
  linarith [hTrace (plaquetteHolonomy U p)]

/-! ## Partition function -/

/-- The partition function: Z = ∫ exp(-S(U)) dμ_Haar(U).
This is the normalizing constant for the YM measure. -/
def partitionFn (β : ℝ) (plaq : Finset (LatticePlaquette d N)) : ℝ :=
  ∫ U, boltzmannWeight G n d N β U plaq ∂(productHaar G d N)

instance instIsProbabilityMeasureProductHaar :
    IsProbabilityMeasure (productHaar G d N) := by
  unfold productHaar
  exact MeasureTheory.Measure.pi.instIsProbabilityMeasure _

instance instIsFiniteMeasureProductHaar :
    IsFiniteMeasure (productHaar G d N) :=
  IsZeroOrProbabilityMeasure.toIsFiniteMeasure _

instance instSigmaFiniteProductHaar :
    SigmaFinite (productHaar G d N) :=
  IsFiniteMeasure.toSigmaFinite _

instance instSFiniteProductHaar :
    SFinite (productHaar G d N) := inferInstance

/-- **The partition function is positive.**

Z > 0 because the integrand exp(-S) is strictly positive everywhere
and the product Haar measure has full support on the compact space. -/
theorem partitionFn_pos (β : ℝ) (hβ : 0 ≤ β)
    (plaq : Finset (LatticePlaquette d N))
    (_hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hIntegrable : Integrable (fun U => boltzmannWeight G n d N β U plaq)
        (productHaar G d N)) :
    0 < partitionFn G n d N β plaq := by
  unfold partitionFn
  -- The integrand w(U) = exp(-S(U)) satisfies 0 < w(U) ≤ 1 everywhere.
  -- Since productHaar is a probability measure and w ≥ exp(-...) > 0,
  -- the integral is positive.
  -- Lower bound: w(U) ≥ exp(-β · |plaq| · 2n) > 0
  set c := Real.exp (-(β * ↑plaq.card * (2 * ↑n))) with hc_def
  have hc_pos : 0 < c := Real.exp_pos _
  have hc_lower : ∀ U, c ≤ boltzmannWeight G n d N β U plaq := by
    intro U
    unfold boltzmannWeight wilsonAction
    apply Real.exp_le_exp_of_le
    apply neg_le_neg
    -- Need: Σ β(n - ReTr(U_p)) ≤ β * |plaq| * 2n
    -- Each term: β(n - ReTr) ≤ β * 2n since ReTr ≥ -n
    calc ∑ p ∈ plaq, β * wilsonPlaquetteCost G n (plaquetteHolonomy U p)
        ≤ ∑ _ ∈ plaq, β * (2 * ↑n) := by
          apply Finset.sum_le_sum; intro p _
          apply mul_le_mul_of_nonneg_left _ hβ
          unfold wilsonPlaquetteCost
          linarith [hTrace_lower (plaquetteHolonomy U p)]
      _ = β * ↑plaq.card * (2 * ↑n) := by
          simp [Finset.sum_const, smul_eq_mul]; ring
  calc (0 : ℝ) < c := hc_pos
    _ = ∫ _, c ∂(productHaar G d N) := by
        rw [integral_const]; simp [IsProbabilityMeasure.measure_univ]
    _ ≤ ∫ U, boltzmannWeight G n d N β U plaq ∂(productHaar G d N) := by
        apply integral_mono (integrable_const _) hIntegrable
        exact fun U => hc_lower U

/-! ## The Yang-Mills probability measure -/

/-- **The Yang-Mills probability measure.**

μ_YM has density (1/Z) · exp(-S(U)) with respect to the product
Haar measure on G^{links}.

This is the finite-volume Gibbs measure for the Wilson lattice
gauge theory. -/
def ymDensity (β : ℝ) (plaq : Finset (LatticePlaquette d N))
    (U : GaugeConnection G d N) : ℝ :=
  boltzmannWeight G n d N β U plaq / partitionFn G n d N β plaq

/-! ## Expectation values -/

/-- The YM expectation: ⟨f⟩ = (1/Z) ∫ f · exp(-S) dμ_Haar. -/
def ymExpect (β : ℝ) (plaq : Finset (LatticePlaquette d N))
    (f : GaugeConnection G d N → ℝ) : ℝ :=
  (∫ U, f U * boltzmannWeight G n d N β U plaq ∂(productHaar G d N)) /
  partitionFn G n d N β plaq

/-- ⟨1⟩ = 1 (the expectation of the constant 1 is 1). -/
theorem ymExpect_one (β : ℝ) (plaq : Finset (LatticePlaquette d N))
    (hZ : partitionFn G n d N β plaq ≠ 0) :
    ymExpect G n d N β plaq (fun _ => 1) = 1 := by
  unfold ymExpect partitionFn
  simp only [one_mul]
  exact div_self hZ

/-- The connected 2-point function: ⟨f·g⟩ - ⟨f⟩·⟨g⟩. -/
def connected2pt (β : ℝ) (plaq : Finset (LatticePlaquette d N))
    (f g : GaugeConnection G d N → ℝ) : ℝ :=
  ymExpect G n d N β plaq (fun U => f U * g U) -
  ymExpect G n d N β plaq f * ymExpect G n d N β plaq g

/-! ## Plaquette observables -/

/-- The plaquette observable: O_p(U) = Re Tr(U_p). -/
def plaqObs (p : LatticePlaquette d N) : GaugeConnection G d N → ℝ :=
  fun U => gaugeReTr G n (plaquetteHolonomy U p)

/-- Plaquette observables are bounded by n. -/
theorem plaqObs_bounded (p : LatticePlaquette d N) (U : GaugeConnection G d N)
    (hTrace : ∀ g : G, |gaugeReTr G n g| ≤ ↑n) :
    |plaqObs G n d N p U| ≤ ↑n :=
  hTrace _

/-! ## The Yang-Mills measure as a `Measure` on gauge configurations

We package the finite-volume Boltzmann-weighted probability
distribution as an honest `Measure`, so it plugs into the abstract
`IsGibbsMeasure` framework in `markov-semigroups`. This is W1' of
`PLAN_PHASE3.md`. -/

/-- The Yang-Mills probability measure:
`μ_YM = (1/Z) · exp(-S) · productHaar`. -/
def ymMeasure (β : ℝ) (plaq : Finset (LatticePlaquette d N)) :
    Measure (GaugeConnection G d N) :=
  (productHaar G d N).withDensity
    (fun U => ENNReal.ofReal (ymDensity G n d N β plaq U))

/-- `ymDensity` is nonnegative. -/
theorem ymDensity_nonneg (β : ℝ) (hβ : 0 ≤ β)
    (plaq : Finset (LatticePlaquette d N))
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hIntegrable : Integrable (fun U => boltzmannWeight G n d N β U plaq)
        (productHaar G d N))
    (U : GaugeConnection G d N) :
    0 ≤ ymDensity G n d N β plaq U := by
  unfold ymDensity
  have hZ : 0 < partitionFn G n d N β plaq :=
    partitionFn_pos G n d N β hβ plaq hTrace_upper hTrace_lower hIntegrable
  exact div_nonneg (boltzmannWeight_pos G n d N β U plaq).le hZ.le

/-- `ymExpect f = ∫ f ∂ymMeasure` for integrable `f`.

This is the bridge: ratios of Haar integrals become a single
integral against `ymMeasure`. -/
theorem ymExpect_eq_integral_ymMeasure
    (β : ℝ) (hβ : 0 ≤ β)
    (plaq : Finset (LatticePlaquette d N))
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hIntegrable_w : Integrable (fun U => boltzmannWeight G n d N β U plaq)
        (productHaar G d N))
    (hw_meas : Measurable (fun U => boltzmannWeight G n d N β U plaq))
    (f : GaugeConnection G d N → ℝ)
    (_hf_meas : Measurable f)
    (_hfw_integrable : Integrable (fun U => f U * boltzmannWeight G n d N β U plaq)
        (productHaar G d N)) :
    ymExpect G n d N β plaq f = ∫ U, f U ∂(ymMeasure G n d N β plaq) := by
  have hZ_pos : 0 < partitionFn G n d N β plaq :=
    partitionFn_pos G n d N β hβ plaq hTrace_upper hTrace_lower hIntegrable_w
  have hZ_ne : partitionFn G n d N β plaq ≠ 0 := hZ_pos.ne'
  -- Integral of f against `withDensity (ofReal (w/Z))` = ∫ f · (w/Z) ∂productHaar
  have hdens_meas : Measurable
      (fun U => ENNReal.ofReal (ymDensity G n d N β plaq U)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    unfold ymDensity
    exact hw_meas.div_const _
  have hdens_nn : ∀ U, 0 ≤ ymDensity G n d N β plaq U :=
    fun U => ymDensity_nonneg G n d N β hβ plaq hTrace_upper hTrace_lower
      hIntegrable_w U
  -- Rewrite ∫ f d(withDensity (ofReal dens)) = ∫ f · dens dHaar.
  have hstep :
      ∫ U, f U ∂(ymMeasure G n d N β plaq) =
        ∫ U, ymDensity G n d N β plaq U * f U ∂(productHaar G d N) := by
    unfold ymMeasure
    rw [integral_withDensity_eq_integral_toReal_smul hdens_meas
          (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) f]
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall (fun U => ?_)
    simp [ENNReal.toReal_ofReal (hdens_nn U), smul_eq_mul]
  rw [hstep]
  -- ymDensity · f = f · w / Z, and integral / Z = integral-of-f·w / Z = ymExpect.
  have hrewrite :
      ∫ U, ymDensity G n d N β plaq U * f U ∂(productHaar G d N) =
        (∫ U, f U * boltzmannWeight G n d N β U plaq ∂(productHaar G d N)) /
          partitionFn G n d N β plaq := by
    unfold ymDensity
    rw [show (fun U => boltzmannWeight G n d N β U plaq /
          partitionFn G n d N β plaq * f U)
        = (fun U => (f U * boltzmannWeight G n d N β U plaq) /
          partitionFn G n d N β plaq) from funext (fun U => by ring)]
    rw [integral_div]
  rw [hrewrite]
  rfl

/-- `ymMeasure` is a probability measure. -/
theorem ymMeasure_isProbabilityMeasure
    (β : ℝ) (hβ : 0 ≤ β)
    (plaq : Finset (LatticePlaquette d N))
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hIntegrable_w : Integrable (fun U => boltzmannWeight G n d N β U plaq)
        (productHaar G d N))
    (hw_meas : Measurable (fun U => boltzmannWeight G n d N β U plaq)) :
    IsProbabilityMeasure (ymMeasure G n d N β plaq) := by
  -- total mass = ∫ 1 ∂ymMeasure = ymExpect 1 = 1.
  constructor
  have hZ_pos : 0 < partitionFn G n d N β plaq :=
    partitionFn_pos G n d N β hβ plaq hTrace_upper hTrace_lower hIntegrable_w
  have hZ_ne : partitionFn G n d N β plaq ≠ 0 := hZ_pos.ne'
  have hone_integrable :
      Integrable (fun U => (fun _ : GaugeConnection G d N => (1 : ℝ)) U *
          boltzmannWeight G n d N β U plaq) (productHaar G d N) := by
    simpa using hIntegrable_w
  have hone_meas :
      Measurable (fun _ : GaugeConnection G d N => (1 : ℝ)) := measurable_const
  have hEq := ymExpect_eq_integral_ymMeasure G n d N β hβ plaq
    hTrace_upper hTrace_lower hIntegrable_w hw_meas
    (fun _ => (1 : ℝ)) hone_meas hone_integrable
  have hOne := ymExpect_one G n d N β plaq hZ_ne
  -- So ∫ 1 ∂ymMeasure = 1, hence the measure of univ is 1.
  have hInt : ∫ _, (1 : ℝ) ∂(ymMeasure G n d N β plaq) = 1 := by rw [← hEq]; exact hOne
  -- Turn ∫ 1 = 1 into (ymMeasure univ) = 1.
  have : ((ymMeasure G n d N β plaq) Set.univ).toReal = 1 := by
    have := hInt
    simpa [integral_const, Measure.restrict_univ] using this
  -- Upgrade toReal = 1 to the ENNReal value = 1.
  have hlt : (ymMeasure G n d N β plaq) Set.univ < ⊤ := by
    -- If univ had measure ⊤, toReal would be 0, contradicting 1.
    by_contra h
    push Not at h
    have htop : (ymMeasure G n d N β plaq) Set.univ = ⊤ := le_antisymm le_top h
    rw [htop] at this
    norm_num at this
  exact (ENNReal.toReal_eq_one_iff _).1 this

end
