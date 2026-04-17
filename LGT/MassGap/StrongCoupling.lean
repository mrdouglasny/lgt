/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Strong Coupling Wrapper for the d ≥ 3 Mass Gap

Discharges the measure-theoretic "plumbing" hypotheses of
`ym_mass_gap_2pt_via_multisite` (integrability, boundedness,
indicator-integrability, conditional partition function positivity,
finite support) from first principles — leaving only the genuinely
hard analytic hypotheses (parametrised-integral measurability,
influence coefficient bounds, link distance structure).

## Main result

`ym_mass_gap_strong_coupling` takes ~15 hypotheses instead of ~28.
The ~13 discharged ones are all consequences of:
- `Continuous (HasGaugeTrace.rep)` implies measurability of
  boltzmannWeight and plaqObs (via continuity chain)
- boltzmannWeight is bounded by 1 (for β ≥ 0)
- plaqObs is bounded by n
- productHaar / ymMeasure are probability measures
- LatticeLink d N is a Fintype

## References

- Chatterjee (2026), §16.3
-/

import LGT.MassGap.MassGap3D

open MeasureTheory Real

open Classical

noncomputable section

variable (G : Type*) (n : ℕ) [Group G] [HasGaugeTrace G n]
variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
variable [MeasurableSpace G] [BorelSpace G]
variable [SecondCountableTopology G]
variable (d N : ℕ)

variable [HasHaarProbability G] [Fintype (LatticeLink d N)]
variable [DecidableEq (LatticeLink d N)]

/-! ## Topology and Borel structure on GaugeConnection -/

instance instTopologicalSpaceGaugeConnection :
    TopologicalSpace (GaugeConnection G d N) := Pi.topologicalSpace

instance instBorelSpaceGaugeConnection :
    BorelSpace (GaugeConnection G d N) := by
  constructor
  show instMeasurableSpaceGaugeConnection G d N =
    @borel (GaugeConnection G d N) (instTopologicalSpaceGaugeConnection G d N)
  show @MeasurableSpace.pi (LatticeLink d N) (fun _ => G) (fun _ => inferInstance) =
    @borel (LatticeLink d N → G)
      (@Pi.topologicalSpace (LatticeLink d N) (fun _ => G) (fun _ => inferInstance))
  exact (@Pi.borelSpace (LatticeLink d N) (fun _ => G) _ (fun _ => inferInstance)
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)).measurable_eq

/-! ## Continuity and measurability from representation continuity

These lemmas derive measurability of `boltzmannWeight` and `plaqObs`
from `Continuous (HasGaugeTrace.rep)` via the chain:
  rep continuous → gaugeTrace continuous → gaugeReTr continuous
  → wilsonPlaquetteCost continuous → wilsonAction continuous
  → boltzmannWeight continuous → measurable
  → plaquetteHolonomy continuous (from topological group ops)
  → plaqObs continuous → measurable -/

set_option linter.unusedSectionVars false in
/-- Link evaluation is continuous in the product topology. -/
theorem continuous_evalLink (l : LatticeLink d N) :
    Continuous (fun U : GaugeConnection G d N => U l) :=
  show Continuous (fun U : LatticeLink d N → G => U l) from continuous_apply l

set_option linter.unusedSectionVars false in
/-- gaugeReTr is continuous when the representation is continuous. -/
theorem continuous_gaugeReTr
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n))) :
    Continuous (gaugeReTr G n) := by
  unfold gaugeReTr gaugeTrace
  exact Complex.continuous_re.comp
    (continuous_finset_sum _ (fun i _ => (continuous_apply_apply i i).comp hRep_cont))

set_option linter.unusedSectionVars false in
/-- Plaquette holonomy is continuous (product of continuous group operations). -/
theorem continuous_plaquetteHolonomy (p : LatticePlaquette d N) :
    Continuous (fun U : GaugeConnection G d N => plaquetteHolonomy U p) := by
  unfold plaquetteHolonomy
  exact ((continuous_evalLink G d N (p.boundaryLinks 0) |>.mul
          (continuous_evalLink G d N (p.boundaryLinks 1))).mul
        (continuous_evalLink G d N (p.boundaryLinks 2) |>.inv)).mul
       (continuous_evalLink G d N (p.boundaryLinks 3) |>.inv)

set_option linter.unusedSectionVars false in
/-- plaqObs is continuous when the representation is continuous. -/
theorem continuous_plaqObs
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (p : LatticePlaquette d N) :
    Continuous (plaqObs G n d N p) := by
  unfold plaqObs
  exact (continuous_gaugeReTr G n hRep_cont).comp
    (continuous_plaquetteHolonomy G d N p)

set_option linter.unusedSectionVars false in
/-- boltzmannWeight is continuous when the representation is continuous. -/
theorem continuous_boltzmannWeight
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (β : ℝ) (plaq : Finset (LatticePlaquette d N)) :
    Continuous (fun U => boltzmannWeight G n d N β U plaq) := by
  unfold boltzmannWeight wilsonAction
  exact continuous_exp.comp (continuous_neg.comp
    (continuous_finset_sum _ fun p _ => by
      unfold wilsonPlaquetteCost
      exact continuous_const.mul (continuous_const.sub
        ((continuous_gaugeReTr G n hRep_cont).comp
          (continuous_plaquetteHolonomy G d N p)))))

set_option linter.unusedSectionVars false in
/-- boltzmannWeight is measurable when the representation is continuous. -/
theorem measurable_boltzmannWeight_of_rep
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (β : ℝ) (plaq : Finset (LatticePlaquette d N)) :
    Measurable (fun U => boltzmannWeight G n d N β U plaq) :=
  (continuous_boltzmannWeight G n d N hRep_cont β plaq).measurable

set_option linter.unusedSectionVars false in
/-- plaqObs is measurable when the representation is continuous. -/
theorem measurable_plaqObs_of_rep
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (p : LatticePlaquette d N) :
    Measurable (plaqObs G n d N p) :=
  (continuous_plaqObs G n d N hRep_cont p).measurable

/-! ## Helper lemmas: deriving integrability from boundedness -/

omit [T2Space G] [DecidableEq (LatticeLink d N)] in
/-- Boltzmann weight integrability: bounded (0 < w ≤ 1) + measurable
on a probability measure ⟹ integrable. -/
theorem boltzmannWeight_integrable
    (β : ℝ) (hβ : 0 ≤ β)
    (plaq : Finset (LatticePlaquette d N))
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hw_meas : Measurable (fun U => boltzmannWeight G n d N β U plaq)) :
    Integrable (fun U => boltzmannWeight G n d N β U plaq) (productHaar G d N) := by
  apply Integrable.of_bound hw_meas.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro U
  rw [Real.norm_of_nonneg (boltzmannWeight_pos G n d N β U plaq).le]
  exact boltzmannWeight_le_one G n d N β hβ U plaq hTrace_upper

/-- Conditional Boltzmann weight integrability: w(glue uΛ σ) is bounded
by 1 and measurable on the product Haar, hence integrable. -/
theorem gibbsConditionalWeight_integrable
    (β : ℝ) (hβ : 0 ≤ β)
    (plaq : Finset (LatticePlaquette d N))
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hw_meas : Measurable (fun U => boltzmannWeight G n d N β U plaq))
    (Λ : Finset (LatticeLink d N)) (σ : GaugeConnection G d N) :
    Integrable (fun uΛ : LatticeLink d N → G =>
        gibbsConditionalWeight G n d N plaq β Λ σ uΛ)
      (Measure.pi (fun _ : LatticeLink d N => haarG G)) := by
  -- gibbsConditionalWeight = boltzmannWeight ∘ gluedConfig, bounded ≤ 1
  have hmeas : Measurable (fun uΛ : LatticeLink d N → G =>
      gibbsConditionalWeight G n d N plaq β Λ σ uΛ) := by
    unfold gibbsConditionalWeight
    exact hw_meas.comp (measurable_gluedConfig G d N Λ σ)
  apply Integrable.of_bound hmeas.aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro uΛ
  unfold gibbsConditionalWeight
  rw [Real.norm_of_nonneg (boltzmannWeight_pos G n d N β _ plaq).le]
  exact boltzmannWeight_le_one G n d N β hβ _ plaq hTrace_upper

/-- Conditional partition function positivity: Z_Λ(σ) > 0 because
the integrand is strictly positive everywhere on a probability measure. -/
theorem gibbsConditionalZ_pos
    (β : ℝ) (hβ : 0 ≤ β)
    (plaq : Finset (LatticePlaquette d N))
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hw_meas : Measurable (fun U => boltzmannWeight G n d N β U plaq))
    (Λ : Finset (LatticeLink d N)) (σ : GaugeConnection G d N) :
    0 < gibbsConditionalZ G n d N plaq β Λ σ := by
  unfold gibbsConditionalZ
  -- Lower bound: each conditional weight ≥ exp(-β · |plaq| · 2n) > 0
  set c := Real.exp (-(β * ↑plaq.card * (2 * ↑n))) with hc_def
  have hc_pos : 0 < c := Real.exp_pos _
  have hc_lower : ∀ uΛ, c ≤ gibbsConditionalWeight G n d N plaq β Λ σ uΛ := by
    intro uΛ
    unfold gibbsConditionalWeight boltzmannWeight wilsonAction
    apply Real.exp_le_exp_of_le
    apply neg_le_neg
    calc ∑ p ∈ plaq, β * wilsonPlaquetteCost G n (plaquetteHolonomy _ p)
        ≤ ∑ _ ∈ plaq, β * (2 * ↑n) := by
          apply Finset.sum_le_sum; intro p _
          apply mul_le_mul_of_nonneg_left _ hβ
          unfold wilsonPlaquetteCost
          linarith [hTrace_lower (plaquetteHolonomy (gluedConfig G d N Λ uΛ σ) p)]
      _ = β * ↑plaq.card * (2 * ↑n) := by
          simp [Finset.sum_const]; ring
  have hint : Integrable (fun uΛ : LatticeLink d N → G =>
      gibbsConditionalWeight G n d N plaq β Λ σ uΛ)
    (Measure.pi (fun _ : LatticeLink d N => haarG G)) :=
    gibbsConditionalWeight_integrable G n d N β hβ plaq hTrace_upper hw_meas Λ σ
  calc (0 : ℝ) < c := hc_pos
    _ = ∫ _, c ∂(Measure.pi (fun _ : LatticeLink d N => haarG G)) := by
        rw [integral_const]; simp
    _ ≤ ∫ uΛ, gibbsConditionalWeight G n d N plaq β Λ σ uΛ
          ∂(Measure.pi (fun _ : LatticeLink d N => haarG G)) := by
        apply integral_mono (integrable_const _) hint
        exact fun uΛ => hc_lower uΛ

omit [T2Space G] [DecidableEq (LatticeLink d N)] in
/-- Indicator of Boltzmann weight is integrable: |1_A * w| <= w <= 1,
so integrability of w implies integrability of 1_A * w. -/
theorem boltzmannWeight_indicator_integrable
    (β : ℝ) (hβ : 0 ≤ β)
    (plaq : Finset (LatticePlaquette d N))
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hw_meas : Measurable (fun U => boltzmannWeight G n d N β U plaq))
    (A : Set (GaugeConnection G d N)) (hA : MeasurableSet A) :
    Integrable (Set.indicator A (fun U => boltzmannWeight G n d N β U plaq))
      (productHaar G d N) := by
  exact (boltzmannWeight_integrable G n d N β hβ plaq hTrace_upper hw_meas).indicator hA

omit [T2Space G] [DecidableEq (LatticeLink d N)] in
/-- plaqObs is integrable on ymMeasure (probability measure + bounded). -/
theorem plaqObs_integrable_ymMeasure
    (β : ℝ) (hβ : 0 ≤ β)
    (plaq : Finset (LatticePlaquette d N))
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hw_meas : Measurable (fun U => boltzmannWeight G n d N β U plaq))
    (p : LatticePlaquette d N)
    (hPlaqObs_meas : Measurable (plaqObs G n d N p)) :
    Integrable (plaqObs G n d N p) (ymMeasure G n d N β plaq) := by
  haveI : IsProbabilityMeasure (ymMeasure G n d N β plaq) :=
    ymMeasure_isProbabilityMeasure G n d N β hβ plaq hTrace_upper hTrace_lower
      (boltzmannWeight_integrable G n d N β hβ plaq hTrace_upper hw_meas) hw_meas
  apply Integrable.of_bound hPlaqObs_meas.aestronglyMeasurable (↑n : ℝ)
  apply Filter.Eventually.of_forall
  intro U
  exact plaqObs_bounded G n d N p U (fun g => abs_le.mpr
    ⟨by linarith [hTrace_lower g], hTrace_upper g⟩)

omit [T2Space G] [DecidableEq (LatticeLink d N)] in
/-- Product plaqObs p * plaqObs q integrable on ymMeasure. -/
theorem plaqObs_prod_integrable_ymMeasure
    (β : ℝ) (hβ : 0 ≤ β)
    (plaq : Finset (LatticePlaquette d N))
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hw_meas : Measurable (fun U => boltzmannWeight G n d N β U plaq))
    (p q : LatticePlaquette d N)
    (hPlaqObs_meas_p : Measurable (plaqObs G n d N p))
    (hPlaqObs_meas_q : Measurable (plaqObs G n d N q)) :
    Integrable (fun U => plaqObs G n d N p U * plaqObs G n d N q U)
      (ymMeasure G n d N β plaq) := by
  haveI : IsProbabilityMeasure (ymMeasure G n d N β plaq) :=
    ymMeasure_isProbabilityMeasure G n d N β hβ plaq hTrace_upper hTrace_lower
      (boltzmannWeight_integrable G n d N β hβ plaq hTrace_upper hw_meas) hw_meas
  apply Integrable.of_bound (hPlaqObs_meas_p.mul hPlaqObs_meas_q).aestronglyMeasurable
    ((↑n : ℝ) * ↑n)
  apply Filter.Eventually.of_forall
  intro U
  rw [Real.norm_eq_abs]
  calc |plaqObs G n d N p U * plaqObs G n d N q U|
      = |plaqObs G n d N p U| * |plaqObs G n d N q U| := abs_mul _ _
    _ ≤ ↑n * ↑n := by
        apply mul_le_mul
        · exact plaqObs_bounded G n d N p U (fun g => abs_le.mpr
            ⟨by linarith [hTrace_lower g], hTrace_upper g⟩)
        · exact plaqObs_bounded G n d N q U (fun g => abs_le.mpr
            ⟨by linarith [hTrace_lower g], hTrace_upper g⟩)
        · exact abs_nonneg _
        · exact Nat.cast_nonneg _

omit [T2Space G] [DecidableEq (LatticeLink d N)] in
/-- plaqObs * boltzmannWeight integrable on productHaar. -/
theorem plaqObs_boltzmann_integrable
    (β : ℝ) (hβ : 0 ≤ β)
    (plaq : Finset (LatticePlaquette d N))
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hw_meas : Measurable (fun U => boltzmannWeight G n d N β U plaq))
    (p : LatticePlaquette d N)
    (hPlaqObs_meas : Measurable (plaqObs G n d N p)) :
    Integrable (fun U => plaqObs G n d N p U *
      boltzmannWeight G n d N β U plaq) (productHaar G d N) := by
  -- |plaqObs * w| ≤ n * 1 = n, bounded measurable on probability measure
  apply Integrable.of_bound (hPlaqObs_meas.mul hw_meas).aestronglyMeasurable (↑n : ℝ)
  apply Filter.Eventually.of_forall
  intro U
  rw [Real.norm_eq_abs]
  calc |plaqObs G n d N p U * boltzmannWeight G n d N β U plaq|
      = |plaqObs G n d N p U| * |boltzmannWeight G n d N β U plaq| := abs_mul _ _
    _ = |plaqObs G n d N p U| * boltzmannWeight G n d N β U plaq := by
        rw [abs_of_pos (boltzmannWeight_pos G n d N β U plaq)]
    _ ≤ ↑n * 1 := by
        apply mul_le_mul
        · exact plaqObs_bounded G n d N p U (fun g => abs_le.mpr
            ⟨by linarith [hTrace_lower g], hTrace_upper g⟩)
        · exact boltzmannWeight_le_one G n d N β hβ U plaq hTrace_upper
        · exact (boltzmannWeight_pos G n d N β U plaq).le
        · exact Nat.cast_nonneg _
    _ = ↑n := mul_one _

omit [T2Space G] [DecidableEq (LatticeLink d N)] in
/-- (plaqObs p * plaqObs q) * boltzmannWeight integrable on productHaar. -/
theorem plaqObs_prod_boltzmann_integrable
    (β : ℝ) (hβ : 0 ≤ β)
    (plaq : Finset (LatticePlaquette d N))
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hw_meas : Measurable (fun U => boltzmannWeight G n d N β U plaq))
    (p q : LatticePlaquette d N)
    (hPlaqObs_meas_p : Measurable (plaqObs G n d N p))
    (hPlaqObs_meas_q : Measurable (plaqObs G n d N q)) :
    Integrable (fun U => (plaqObs G n d N p U * plaqObs G n d N q U) *
      boltzmannWeight G n d N β U plaq) (productHaar G d N) := by
  -- |(p * q) * w| ≤ n² * 1 = n², bounded measurable on probability measure
  apply Integrable.of_bound
    ((hPlaqObs_meas_p.mul hPlaqObs_meas_q).mul hw_meas).aestronglyMeasurable
    ((↑n : ℝ) * ↑n)
  apply Filter.Eventually.of_forall
  intro U
  rw [Real.norm_eq_abs]
  calc |((plaqObs G n d N p U) * (plaqObs G n d N q U)) *
          boltzmannWeight G n d N β U plaq|
      = |(plaqObs G n d N p U) * (plaqObs G n d N q U)| *
          |boltzmannWeight G n d N β U plaq| := abs_mul _ _
    _ = |(plaqObs G n d N p U) * (plaqObs G n d N q U)| *
          boltzmannWeight G n d N β U plaq := by
        rw [abs_of_pos (boltzmannWeight_pos G n d N β U plaq)]
    _ ≤ (↑n * ↑n) * 1 := by
        apply mul_le_mul
        · calc |(plaqObs G n d N p U) * (plaqObs G n d N q U)|
              = |plaqObs G n d N p U| * |plaqObs G n d N q U| := abs_mul _ _
            _ ≤ ↑n * ↑n := by
                apply mul_le_mul
                · exact plaqObs_bounded G n d N p U (fun g => abs_le.mpr
                    ⟨by linarith [hTrace_lower g], hTrace_upper g⟩)
                · exact plaqObs_bounded G n d N q U (fun g => abs_le.mpr
                    ⟨by linarith [hTrace_lower g], hTrace_upper g⟩)
                · exact abs_nonneg _
                · exact Nat.cast_nonneg _
        · exact boltzmannWeight_le_one G n d N β hβ U plaq hTrace_upper
        · exact (boltzmannWeight_pos G n d N β U plaq).le
        · exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    _ = ↑n * ↑n := mul_one _

/-- Influence coefficient support is finite on a Fintype. -/
theorem influenceCoeff_finsupp
    (plaq : Finset (LatticePlaquette d N))
    (β : ℝ)
    (hw_meas : Measurable (fun U => boltzmannWeight G n d N β U plaq))
    (hZcond_pos : ∀ (Λ : Finset (LatticeLink d N)) (σ : GaugeConnection G d N),
        0 < gibbsConditionalZ G n d N plaq β Λ σ)
    (hw_integrable_cond : ∀ (Λ : Finset (LatticeLink d N))
        (σ : GaugeConnection G d N),
        Integrable (fun uΛ : LatticeLink d N → G =>
            gibbsConditionalWeight G n d N plaq β Λ σ uΛ)
          (Measure.pi (fun _ : LatticeLink d N => haarG G)))
    (hmeas_condDist : ∀ (Λ : Finset (LatticeLink d N))
        (A : Set (GaugeConnection G d N)), MeasurableSet A →
        Measurable (fun σ : GaugeConnection G d N =>
          (gibbsCondMeasure G n d N plaq β Λ σ A).toReal))
    (z : LatticeLink d N) :
    (Function.support (fun w => influenceCoeff
      (ymGibbsSpec G n d N plaq β hZcond_pos hw_meas
        hw_integrable_cond hmeas_condDist) z w)).Finite :=
  Set.Finite.subset (Set.toFinite _) (Set.subset_univ _)

/-! ## The strong coupling wrapper theorem

Discharges 13 measure-theoretic hypotheses (including 3 measurability
facts derived from `hRep_cont`), passing through only the genuinely
hard ones. -/

set_option maxHeartbeats 800000 in
theorem ym_mass_gap_strong_coupling
    [Inhabited G] [Countable G] [MeasurableSingletonClass G]
    [MeasurableEq (SpinConfig (LatticeLink d N) G)]
    (hd : 2 ≤ d) (hn : 1 ≤ n)
    (β : ℝ) (hβ : 0 ≤ β)
    (hβ_small : β < 1 / (2 * ↑n * ↑(maxNeighbors d)))
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (plaq : Finset (LatticePlaquette d N))
    (p q : LatticePlaquette d N)
    -- Core continuity (implies measurability of boltzmannWeight and plaqObs):
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    -- Parametrised-integral measurability (genuine measure theory):
    (hmeas_condDist : ∀ (Λ : Finset (LatticeLink d N))
        (A : Set (GaugeConnection G d N)), MeasurableSet A →
        Measurable (fun σ : GaugeConnection G d N =>
          (gibbsCondMeasure G n d N plaq β Λ σ A).toReal))
    (hZcond_meas : ∀ Λ : Finset (LatticeLink d N),
        Measurable (fun σ : GaugeConnection G d N =>
          gibbsConditionalZ G n d N plaq β Λ σ))
    (hinner_meas : ∀ (Λ : Finset (LatticeLink d N))
        (A : Set (GaugeConnection G d N)), MeasurableSet A →
        Measurable (fun σ : GaugeConnection G d N =>
          ∫ uΛ, Set.indicator A
              (fun U => boltzmannWeight G n d N β U plaq)
              (gluedConfig G d N Λ uΛ σ) ∂(productHaar G d N)))
    (hinner_w_over_Z_int : ∀ (Λ : Finset (LatticeLink d N))
        (A : Set (GaugeConnection G d N)), MeasurableSet A →
        Integrable (fun σ : GaugeConnection G d N =>
            (∫ uΛ, Set.indicator A
                (fun U => boltzmannWeight G n d N β U plaq)
                (gluedConfig G d N Λ uΛ σ) ∂(productHaar G d N))
              / gibbsConditionalZ G n d N plaq β Λ σ
            * boltzmannWeight G n d N β σ plaq) (productHaar G d N))
    -- Dobrushin influence bounds (physics/combinatorics):
    (hInfluence : ∀ x y : LatticeLink d N,
      influenceCoeff
        (ymGibbsSpec G n d N plaq β
          (gibbsConditionalZ_pos G n d N β hβ plaq hTrace_upper hTrace_lower
            (measurable_boltzmannWeight_of_rep G n d N hRep_cont β plaq))
          (measurable_boltzmannWeight_of_rep G n d N hRep_cont β plaq)
          (gibbsConditionalWeight_integrable G n d N β hβ plaq hTrace_upper
            (measurable_boltzmannWeight_of_rep G n d N hRep_cont β plaq))
          hmeas_condDist) x y ≤
        (if sharesPlaquette d N plaq x y then influenceBound n β else 0))
    (hMaxNeighborsCol : ∀ y : LatticeLink d N,
      ((Finset.univ : Finset (LatticeLink d N)).filter
        (fun x => sharesPlaquette d N plaq x y)).card ≤ maxNeighbors d)
    (hMaxNeighborsRow : ∀ x : LatticeLink d N,
      ((Finset.univ : Finset (LatticeLink d N)).filter
        (fun y => sharesPlaquette d N plaq x y)).card ≤ maxNeighbors d)
    -- Conditional integrability of plaqObs q:
    (hPlaqObs_q_cond_int :
        ∀ a : ((Finset.univ : Finset (Fin 4)).image
            (LatticePlaquette.boundaryLinks p)) → G,
        ymMeasure G n d N β plaq
            (CovarianceBoundMultisite.multiFiber
              ((Finset.univ : Finset (Fin 4)).image
                (LatticePlaquette.boundaryLinks p))
              (CovarianceBoundMultisite.extendOnFinset _ a)) ≠ 0 →
        Integrable (plaqObs G n d N q)
          (CovarianceBoundMultisite.condFiniteSupportMeasure
            (ymMeasure G n d N β plaq)
            ((Finset.univ : Finset (Fin 4)).image
              (LatticePlaquette.boundaryLinks p))
            (CovarianceBoundMultisite.extendOnFinset _ a)))
    -- Link distance structure:
    (dLink : LatticeLink d N → LatticeLink d N → ℕ)
    (h_refl : ∀ x, dLink x x = 0)
    (h_triangle : ∀ x y z, dLink x y ≤ dLink x z + dLink z y)
    (h_support : ∀ u v, dLink u v > 1 →
        influenceCoeff
          (ymGibbsSpec G n d N plaq β
            (gibbsConditionalZ_pos G n d N β hβ plaq hTrace_upper hTrace_lower
              (measurable_boltzmannWeight_of_rep G n d N hRep_cont β plaq))
            (measurable_boltzmannWeight_of_rep G n d N hRep_cont β plaq)
            (gibbsConditionalWeight_integrable G n d N β hβ plaq hTrace_upper
              (measurable_boltzmannWeight_of_rep G n d N hRep_cont β plaq))
            hmeas_condDist) u v = 0)
    -- Local dependence:
    (h_dep_F : ∀ (z : LatticeLink d N)
        (A : Set (GaugeConnection G d N)), MeasurableSet A →
        ∀ (σ τ : GaugeConnection G d N),
          (∀ w ∈ (influenceCoeff_finsupp G n d N plaq β
            (measurable_boltzmannWeight_of_rep G n d N hRep_cont β plaq)
            (gibbsConditionalZ_pos G n d N β hβ plaq hTrace_upper hTrace_lower
              (measurable_boltzmannWeight_of_rep G n d N hRep_cont β plaq))
            (gibbsConditionalWeight_integrable G n d N β hβ plaq hTrace_upper
              (measurable_boltzmannWeight_of_rep G n d N hRep_cont β plaq))
            hmeas_condDist z).toFinset, σ w = τ w) →
          ((ymGibbsSpec G n d N plaq β
              (gibbsConditionalZ_pos G n d N β hβ plaq hTrace_upper hTrace_lower
                (measurable_boltzmannWeight_of_rep G n d N hRep_cont β plaq))
              (measurable_boltzmannWeight_of_rep G n d N hRep_cont β plaq)
              (gibbsConditionalWeight_integrable G n d N β hβ plaq hTrace_upper
                (measurable_boltzmannWeight_of_rep G n d N hRep_cont β plaq))
              hmeas_condDist).condDist
            {z} σ A).toReal =
          ((ymGibbsSpec G n d N plaq β
              (gibbsConditionalZ_pos G n d N β hβ plaq hTrace_upper hTrace_lower
                (measurable_boltzmannWeight_of_rep G n d N hRep_cont β plaq))
              (measurable_boltzmannWeight_of_rep G n d N hRep_cont β plaq)
              (gibbsConditionalWeight_integrable G n d N β hβ plaq hTrace_upper
                (measurable_boltzmannWeight_of_rep G n d N hRep_cont β plaq))
              hmeas_condDist).condDist
            {z} τ A).toReal) :
    |connected2pt G n d N β plaq (plaqObs G n d N p) (plaqObs G n d N q)| ≤
      2 * (↑n : ℝ) * (↑n : ℝ) *
        ∑ x ∈ ((Finset.univ : Finset (Fin 4)).image
                (LatticePlaquette.boundaryLinks p)),
          ∑ y ∈ ((Finset.univ : Finset (Fin 4)).image
                (LatticePlaquette.boundaryLinks q)),
            (dobrushinColumnSum n d β) ^ dLink y x /
              (1 - dobrushinColumnSum n d β) := by
  -- Derive measurability from representation continuity
  have hw_meas : Measurable (fun U => boltzmannWeight G n d N β U plaq) :=
    measurable_boltzmannWeight_of_rep G n d N hRep_cont β plaq
  have hPlaqObs_p_meas : Measurable (plaqObs G n d N p) :=
    measurable_plaqObs_of_rep G n d N hRep_cont p
  have hPlaqObs_q_meas : Measurable (plaqObs G n d N q) :=
    measurable_plaqObs_of_rep G n d N hRep_cont q
  -- Derive the easy hypotheses
  have hIntegrable_w : Integrable (fun U => boltzmannWeight G n d N β U plaq)
      (productHaar G d N) :=
    boltzmannWeight_integrable G n d N β hβ plaq hTrace_upper hw_meas
  have hZcond_pos : ∀ (Λ : Finset (LatticeLink d N)) (σ : GaugeConnection G d N),
      0 < gibbsConditionalZ G n d N plaq β Λ σ :=
    gibbsConditionalZ_pos G n d N β hβ plaq hTrace_upper hTrace_lower hw_meas
  have hw_integrable_cond : ∀ (Λ : Finset (LatticeLink d N))
      (σ : GaugeConnection G d N),
      Integrable (fun uΛ : LatticeLink d N → G =>
          gibbsConditionalWeight G n d N plaq β Λ σ uΛ)
        (Measure.pi (fun _ : LatticeLink d N => haarG G)) :=
    gibbsConditionalWeight_integrable G n d N β hβ plaq hTrace_upper hw_meas
  have hindA_fub_int : ∀ (A : Set (GaugeConnection G d N)), MeasurableSet A →
      Integrable (Set.indicator A (fun U => boltzmannWeight G n d N β U plaq))
        (productHaar G d N) :=
    boltzmannWeight_indicator_integrable G n d N β hβ plaq hTrace_upper hw_meas
  have hPlaqObs_p_int : Integrable (plaqObs G n d N p)
      (ymMeasure G n d N β plaq) :=
    plaqObs_integrable_ymMeasure G n d N β hβ plaq hTrace_upper hTrace_lower
      hw_meas p hPlaqObs_p_meas
  have hPlaqObs_q_int : Integrable (plaqObs G n d N q)
      (ymMeasure G n d N β plaq) :=
    plaqObs_integrable_ymMeasure G n d N β hβ plaq hTrace_upper hTrace_lower
      hw_meas q hPlaqObs_q_meas
  have hPlaqObs_pq_int : Integrable
      (fun U => plaqObs G n d N p U * plaqObs G n d N q U)
      (ymMeasure G n d N β plaq) :=
    plaqObs_prod_integrable_ymMeasure G n d N β hβ plaq hTrace_upper hTrace_lower
      hw_meas p q hPlaqObs_p_meas hPlaqObs_q_meas
  have hPlaqObs_pw_int : Integrable
      (fun U => plaqObs G n d N p U * boltzmannWeight G n d N β U plaq)
      (productHaar G d N) :=
    plaqObs_boltzmann_integrable G n d N β hβ plaq hTrace_upper hTrace_lower
      hw_meas p hPlaqObs_p_meas
  have hPlaqObs_qw_int : Integrable
      (fun U => plaqObs G n d N q U * boltzmannWeight G n d N β U plaq)
      (productHaar G d N) :=
    plaqObs_boltzmann_integrable G n d N β hβ plaq hTrace_upper hTrace_lower
      hw_meas q hPlaqObs_q_meas
  have hPlaqObs_pqw_int : Integrable
      (fun U => (plaqObs G n d N p U * plaqObs G n d N q U) *
        boltzmannWeight G n d N β U plaq) (productHaar G d N) :=
    plaqObs_prod_boltzmann_integrable G n d N β hβ plaq hTrace_upper hTrace_lower
      hw_meas p q hPlaqObs_p_meas hPlaqObs_q_meas
  have hfinsupp : ∀ z : LatticeLink d N,
      (Function.support (fun w => influenceCoeff
        (ymGibbsSpec G n d N plaq β hZcond_pos hw_meas
          hw_integrable_cond hmeas_condDist) z w)).Finite :=
    influenceCoeff_finsupp G n d N plaq β hw_meas
      hZcond_pos hw_integrable_cond hmeas_condDist
  -- Apply the upstream theorem
  exact ym_mass_gap_2pt_via_multisite G n d N hd hn β hβ hβ_small
    hTrace_lower hTrace_upper plaq p q
    hZcond_pos hw_meas hw_integrable_cond hmeas_condDist
    hZcond_meas hinner_meas hindA_fub_int hinner_w_over_Z_int hIntegrable_w
    hPlaqObs_p_meas hPlaqObs_q_meas hPlaqObs_p_int hPlaqObs_q_int hPlaqObs_pq_int
    hPlaqObs_pw_int hPlaqObs_qw_int hPlaqObs_pqw_int
    hInfluence hMaxNeighborsCol hMaxNeighborsRow hPlaqObs_q_cond_int
    dLink h_refl h_triangle h_support hfinsupp h_dep_F

end
