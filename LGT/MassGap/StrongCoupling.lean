/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Strong Coupling Wrapper for the d ≥ 3 Mass Gap

Discharges the measure-theoretic "plumbing" hypotheses of
`ym_mass_gap_2pt_via_multisite` (integrability, boundedness,
indicator-integrability, conditional partition function positivity,
finite support), the link distance structure, and conditional
integrability from first principles — leaving only the genuinely
hard analytic hypotheses (parametrised-integral measurability,
influence coefficient bounds, local dependence).

## Main result

`ym_mass_gap_strong_coupling` takes ~10 hypotheses instead of ~28.
The ~18 discharged ones are all consequences of:
- `Continuous (HasGaugeTrace.rep)` implies measurability of
  boltzmannWeight and plaqObs (via continuity chain)
- boltzmannWeight is bounded by 1 (for beta >= 0)
- plaqObs is bounded by n
- productHaar / ymMeasure are probability measures
- LatticeLink d N is a Fintype
- Concrete link distance `ymLinkDist` (0/1/2 based on plaquette
  adjacency) satisfies reflexivity, triangle inequality, and
  support property
- Bounded measurable functions are integrable on probability measures

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

/-! ## Link distance structure

A crude distance on `LatticeLink d N` based on plaquette adjacency:
- `ymLinkDist e₁ e₂ = 0` when `e₁ = e₂`
- `ymLinkDist e₁ e₂ = 1` when they share a plaquette
- `ymLinkDist e₁ e₂ = 2` otherwise

All values lie in `{0, 1, 2}`, making the triangle inequality
and support property trivial by case analysis. -/

/-- Crude metric on links: 0 if equal, 1 if plaquette-neighbors, 2 otherwise.
Uses classical decidability (via `open Classical`). -/
def ymLinkDist (plaq : Finset (LatticePlaquette d N))
    (e₁ e₂ : LatticeLink d N) : ℕ :=
  if e₁ = e₂ then 0
  else if sharesPlaquette d N plaq e₁ e₂ then 1
  else 2

omit [Fintype (LatticeLink d N)] in
theorem ymLinkDist_refl (plaq : Finset (LatticePlaquette d N))
    (e : LatticeLink d N) :
    ymLinkDist d N plaq e e = 0 := by
  simp [ymLinkDist]

omit [Fintype (LatticeLink d N)] in
theorem ymLinkDist_triangle (plaq : Finset (LatticePlaquette d N))
    (x y z : LatticeLink d N) :
    ymLinkDist d N plaq x y ≤ ymLinkDist d N plaq x z + ymLinkDist d N plaq z y := by
  simp only [ymLinkDist]
  -- All values are in {0, 1, 2}; case split on equality conditions.
  by_cases hxy : x = y
  · -- x = y: LHS = 0 ≤ RHS
    simp [hxy]
  · by_cases hxz : x = z
    · subst hxz; simp [hxy]
    · by_cases hzy : z = y
      · subst hzy; simp [hxy]
      · -- x ≠ z, z ≠ y: each summand ≥ 1, so RHS ≥ 2 ≥ LHS
        simp only [hxz, hzy, hxy, ↓reduceIte]
        have h1 : 1 ≤ (if sharesPlaquette d N plaq x z then 1 else 2) := by
          split_ifs <;> omega
        have h2 : 1 ≤ (if sharesPlaquette d N plaq z y then 1 else 2) := by
          split_ifs <;> omega
        have h3 : (if sharesPlaquette d N plaq x y then 1 else 2) ≤ 2 := by
          split_ifs <;> omega
        omega

omit [SecondCountableTopology G] in
/-- The distance-support property: links at distance > 1 have zero
influence coefficient. Follows from `hInfluence` (which bounds
influence by 0 off-plaquette) and nonnegativity of `influenceCoeff`. -/
theorem ymLinkDist_support (plaq : Finset (LatticePlaquette d N))
    (β : ℝ)
    (hZ_pos : ∀ Λ σ, 0 < gibbsConditionalZ G n d N plaq β Λ σ)
    (hw_meas : Measurable fun U => boltzmannWeight G n d N β U plaq)
    (hw_integrable : ∀ (Λ : Finset (LatticeLink d N))
        (σ : GaugeConnection G d N),
        Integrable (fun uΛ : LatticeLink d N → G =>
            gibbsConditionalWeight G n d N plaq β Λ σ uΛ)
          (Measure.pi (fun _ : LatticeLink d N => haarG G)))
    (hmeas_condDist : ∀ (Λ : Finset (LatticeLink d N))
        (A : Set (GaugeConnection G d N)), MeasurableSet A →
        Measurable (fun σ : GaugeConnection G d N =>
          (gibbsCondMeasure G n d N plaq β Λ σ A).toReal))
    (hInfluence : ∀ x y : LatticeLink d N,
      influenceCoeff
        (ymGibbsSpec G n d N plaq β hZ_pos hw_meas hw_integrable hmeas_condDist)
        x y ≤ (if sharesPlaquette d N plaq x y then influenceBound n β else 0))
    (u v : LatticeLink d N) (h : ymLinkDist d N plaq u v > 1) :
    influenceCoeff
      (ymGibbsSpec G n d N plaq β hZ_pos hw_meas hw_integrable hmeas_condDist)
      u v = 0 := by
  -- ymLinkDist > 1 means the value is 2, which means ¬ sharesPlaquette
  unfold ymLinkDist at h
  split_ifs at h with h1 h2
  · omega
  · omega
  · -- ¬ sharesPlaquette, so hInfluence gives influenceCoeff ≤ 0
    have hle := hInfluence u v
    simp only [↓reduceIte, h2] at hle
    exact le_antisymm hle (influenceCoeff_nonneg _ u v)

/-! ## Conditional integrability of bounded observables

A bounded measurable function is integrable on any probability measure.
We use this to discharge `hPlaqObs_q_cond_int`. -/

omit [T2Space G] in
/-- `plaqObs q` is integrable on any `condFiniteSupportMeasure` of
`ymMeasure` — bounded + measurable on a probability measure. -/
theorem plaqObs_cond_integrable
    [MeasurableSingletonClass G] [Countable G] [Inhabited G]
    (β : ℝ) (hβ : 0 ≤ β)
    (plaq : Finset (LatticePlaquette d N))
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hw_meas : Measurable (fun U => boltzmannWeight G n d N β U plaq))
    (p q : LatticePlaquette d N)
    (hPlaqObs_q_meas : Measurable (plaqObs G n d N q)) :
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
        (CovarianceBoundMultisite.extendOnFinset _ a)) := by
  intro a hne
  -- ymMeasure is a probability measure, so μ(fiber) ≤ 1 < ⊤
  haveI : IsProbabilityMeasure (ymMeasure G n d N β plaq) :=
    ymMeasure_isProbabilityMeasure G n d N β hβ plaq hTrace_upper hTrace_lower
      (boltzmannWeight_integrable G n d N β hβ plaq hTrace_upper hw_meas) hw_meas
  have hne_top : ymMeasure G n d N β plaq
      (CovarianceBoundMultisite.multiFiber
        ((Finset.univ : Finset (Fin 4)).image (LatticePlaquette.boundaryLinks p))
        (CovarianceBoundMultisite.extendOnFinset _ a)) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [measure_ne_top]) (measure_mono (Set.subset_univ _))
  -- Bounded + ae-measurable on finite measure → integrable.
  -- The condFiniteSupportMeasure is a probability measure, so it's finite.
  haveI : IsProbabilityMeasure
      (CovarianceBoundMultisite.condFiniteSupportMeasure
        (ymMeasure G n d N β plaq)
        ((Finset.univ : Finset (Fin 4)).image (LatticePlaquette.boundaryLinks p))
        (CovarianceBoundMultisite.extendOnFinset _ a)) :=
    CovarianceBoundMultisite.isProbabilityMeasure_condFiniteSupportMeasure
      _ _ _ hne hne_top
  exact Integrable.of_bound (μ := CovarianceBoundMultisite.condFiniteSupportMeasure
        (ymMeasure G n d N β plaq)
        ((Finset.univ : Finset (Fin 4)).image (LatticePlaquette.boundaryLinks p))
        (CovarianceBoundMultisite.extendOnFinset _ a))
    hPlaqObs_q_meas.aestronglyMeasurable (↑n : ℝ)
    (Filter.Eventually.of_forall (fun U =>
      plaqObs_bounded G n d N q U (fun g => abs_le.mpr
        ⟨by linarith [hTrace_lower g], hTrace_upper g⟩)))

/-! ## Cylinder-set local dependence of `condDist`

The z-marginal of `γ.condDist {z} σ` depends on σ only through
coordinates with nonzero influence coefficient. If σ and τ agree
on the support of `influenceCoeff γ z ·`, then the z-marginals
agree on every cylinder set `(· z) ⁻¹' B`.

Proof: build a chain from σ to τ by flipping one coordinate at a
time (only coordinates with `influenceCoeff = 0`). Each flip
preserves the z-marginal by `condDist_lipschitz_at_site_cylinder`. -/

/-- Interpolating configuration: agrees with τ on T, with σ elsewhere. -/
private def interpConfig {I S : Type*} (σ τ : I → S)
    (T : Finset I) [DecidableEq I] : I → S :=
  fun i => if i ∈ T then τ i else σ i

private theorem interpConfig_empty {I S : Type*} [DecidableEq I]
    (σ τ : I → S) : interpConfig σ τ ∅ = σ := by
  ext i; simp [interpConfig]

private theorem interpConfig_diff_only_at {I S : Type*} [DecidableEq I]
    (σ τ : I → S) (T : Finset I) (w : I) (_hw : w ∉ T) (i : I) (hi : i ≠ w) :
    interpConfig σ τ (insert w T) i = interpConfig σ τ T i := by
  simp only [interpConfig]
  congr 1
  exact propext ⟨fun h => (Finset.mem_insert.mp h).resolve_left hi,
    fun h => Finset.mem_insert_of_mem h⟩

private theorem interpConfig_eq_tau_of_agree {I S : Type*} [DecidableEq I]
    [Fintype I] (σ τ : I → S) (S' : Finset I)
    (hagree : ∀ i ∈ S', σ i = τ i) :
    interpConfig σ τ (Finset.univ \ S') = τ := by
  ext i
  simp only [interpConfig, Finset.mem_sdiff, Finset.mem_univ, true_and]
  by_cases h : i ∈ S'
  · simp [h, hagree i h]
  · simp [h]

/-- The z-marginal of `condDist {z}` is invariant under changes
to coordinates with zero influence coefficient. Chain argument
by Finset induction on the "complement of the support." -/
theorem condDist_cylinder_eq_of_agree_on_support
    {I S : Type*} [DecidableEq I] [Fintype I]
    [MeasurableSpace S] [MeasurableSpace (I → S)]
    (γ : GibbsSpec I S) (z : I)
    (B : Set S) (hB : MeasurableSet B)
    (hfinsupp : (Function.support (influenceCoeff γ z ·)).Finite)
    (σ τ : I → S)
    (hagree : ∀ w ∈ hfinsupp.toFinset, σ w = τ w) :
    (γ.condDist {z} σ ((· z) ⁻¹' B)).toReal =
    (γ.condDist {z} τ ((· z) ⁻¹' B)).toReal := by
  -- Let F = hfinsupp.toFinset (the support of influenceCoeff γ z ·)
  set F := hfinsupp.toFinset with hF_def
  -- We induct over T = Finset.univ \ F, showing the z-marginal is preserved
  -- at each step of the interpolation chain.
  suffices h : ∀ T : Finset I, T ⊆ Finset.univ \ F →
      (γ.condDist {z} σ ((· z) ⁻¹' B)).toReal =
      (γ.condDist {z} (interpConfig σ τ T) ((· z) ⁻¹' B)).toReal by
    have hfull := h (Finset.univ \ F) (Finset.Subset.refl _)
    rw [interpConfig_eq_tau_of_agree σ τ F hagree] at hfull
    exact hfull
  intro T
  refine Finset.induction_on T (fun _ => by rw [interpConfig_empty]) ?_
  intro w T' hw ih hT_sub
  -- T' ⊆ univ \ F
  have hT'_sub : T' ⊆ Finset.univ \ F :=
    (Finset.subset_insert w T').trans hT_sub
  -- w ∈ univ \ F, so w ∉ F, so influenceCoeff γ z w = 0
  have hw_mem : w ∈ Finset.univ \ F := hT_sub (Finset.mem_insert_self w T')
  have hw_notF : w ∉ F := (Finset.mem_sdiff.mp hw_mem).2
  have hw_zero : influenceCoeff γ z w = 0 := by
    have hnn := influenceCoeff_nonneg γ z w
    by_contra hne
    exact hw_notF (hfinsupp.mem_toFinset.mpr (Function.mem_support.mpr hne))
  -- By IH, condDist {z} σ agrees with condDist {z} (interpConfig σ τ T')
  have ih_eq := ih hT'_sub
  -- interpConfig σ τ (insert w T') and interpConfig σ τ T' differ only at w
  have hdiff_w : ∀ i, i ≠ w →
      interpConfig σ τ (insert w T') i = interpConfig σ τ T' i :=
    fun i hi => interpConfig_diff_only_at σ τ T' w hw i hi
  -- By condDist_lipschitz_at_site_cylinder with influenceCoeff = 0:
  have hlip := condDist_lipschitz_at_site_cylinder γ z w
    (interpConfig σ τ T') (interpConfig σ τ (insert w T'))
    (fun i hi => (hdiff_w i hi).symm) B hB
  rw [hw_zero] at hlip
  have heq : (γ.condDist {z} (interpConfig σ τ T') ((· z) ⁻¹' B)).toReal =
      (γ.condDist {z} (interpConfig σ τ (insert w T')) ((· z) ⁻¹' B)).toReal := by
    have h_abs_zero := le_antisymm hlip (abs_nonneg _)
    exact sub_eq_zero.mp (abs_eq_zero.mp h_abs_zero)
  linarith

/-! ## Off-plaquette locality of the Boltzmann conditional

When links x and y do not share a plaquette, the Boltzmann weight
factorizes so that the density ratio `w/Z` is the same for any two
boundary conditions σ, τ differing only at y. This makes the
x-marginal of the conditional independent of σ(y). -/

/-- A link is on the boundary of a plaquette. -/
private abbrev linkOnBdry (d N : ℕ) (ℓ : LatticeLink d N) (p : LatticePlaquette d N) : Prop :=
  ℓ ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks

/-- When x, y don't share a plaquette, the plaquette holonomy of
`gluedConfig {x} u σ` equals `gluedConfig {x} u τ` for plaquettes
containing x, and equals `σ` (resp. `τ`) for plaquettes not containing x. -/
private theorem holonomy_glue_eq_of_on_bdry
    (plaq : Finset (LatticePlaquette d N))
    (x y : LatticeLink d N)
    (h_no_shared : ¬ sharesPlaquette d N plaq x y)
    (σ τ : GaugeConnection G d N) (h_diff : ∀ z, z ≠ y → σ z = τ z)
    (u : LatticeLink d N → G)
    (p : LatticePlaquette d N) (hp : p ∈ plaq)
    (hx : linkOnBdry d N x p) :
    plaquetteHolonomy (gluedConfig G d N ({x} : Finset _) u σ) p =
    plaquetteHolonomy (gluedConfig G d N ({x} : Finset _) u τ) p := by
  -- Each boundary link of p agrees between gluedConfig u σ and gluedConfig u τ.
  simp only [plaquetteHolonomy]
  -- For each boundary link i:
  -- If p.boundaryLinks i ∈ {x}, gluedConfig gives u(p.boundaryLinks i) in both cases.
  -- If p.boundaryLinks i ∉ {x}, gluedConfig gives σ/τ, and we need σ = τ there.
  -- Since p.boundaryLinks i ≠ y (else sharesPlaquette x y), h_diff gives σ = τ.
  suffices ∀ i : Fin 4,
      gluedConfig G d N ({x} : Finset _) u σ (p.boundaryLinks i) =
      gluedConfig G d N ({x} : Finset _) u τ (p.boundaryLinks i) by
    rw [this 0, this 1, this 2, this 3]
  intro i
  by_cases hi : p.boundaryLinks i ∈ ({x} : Finset _)
  · rw [gluedConfig_eq_inside G d N _ u σ _ hi, gluedConfig_eq_inside G d N _ u τ _ hi]
  · rw [gluedConfig_eq_outside G d N _ u σ _ hi, gluedConfig_eq_outside G d N _ u τ _ hi]
    apply h_diff; intro hiy; subst hiy
    -- x is on boundary of p, so ∃ j with p.boundaryLinks j = x
    have : ∃ j, p.boundaryLinks j = x := by
      unfold linkOnBdry at hx
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
      exact hx
    obtain ⟨j, hj⟩ := this
    exact h_no_shared ⟨p, hp, j, i, hj, rfl⟩

private theorem holonomy_glue_eq_of_not_on_bdry
    (x : LatticeLink d N)
    (σ : GaugeConnection G d N) (u : LatticeLink d N → G)
    (p : LatticePlaquette d N) (hx : ¬ linkOnBdry d N x p) :
    plaquetteHolonomy (gluedConfig G d N ({x} : Finset _) u σ) p =
    plaquetteHolonomy σ p := by
  simp only [plaquetteHolonomy]
  suffices ∀ i : Fin 4,
      gluedConfig G d N ({x} : Finset _) u σ (p.boundaryLinks i) = σ (p.boundaryLinks i) by
    rw [this 0, this 1, this 2, this 3]
  intro i
  apply gluedConfig_eq_outside; simp only [Finset.mem_singleton]
  intro h; apply hx; show x ∈ _
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨i, h⟩

set_option maxHeartbeats 800000 in
/-- **Boltzmann weight factorization identity.**

When x, y don't share a plaquette and σ, τ differ only at y:
`w(gluedConfig u σ) * Z_τ = w(gluedConfig u τ) * Z_σ`.

This implies the density ratio `w/Z` is the same, which in turn
implies the x-marginals of the conditional measures are equal. -/
theorem boltzmannWeight_factor_eq
    (plaq : Finset (LatticePlaquette d N))
    (β : ℝ) (x y : LatticeLink d N)
    (h_no_shared : ¬ sharesPlaquette d N plaq x y)
    (σ τ : GaugeConnection G d N) (h_diff : ∀ z, z ≠ y → σ z = τ z)
    (u : LatticeLink d N → G) :
    boltzmannWeight G n d N β (gluedConfig G d N ({x} : Finset _) u σ) plaq *
      gibbsConditionalZ G n d N plaq β ({x} : Finset _) τ =
    boltzmannWeight G n d N β (gluedConfig G d N ({x} : Finset _) u τ) plaq *
      gibbsConditionalZ G n d N plaq β ({x} : Finset _) σ := by
  -- Rewrite wilsonAction by splitting plaquettes into those containing x and those not.
  have h_action : ∀ (ρ : GaugeConnection G d N) (v : LatticeLink d N → G),
      wilsonAction G n d N β (gluedConfig G d N ({x} : Finset _) v ρ) plaq =
      (∑ p ∈ plaq.filter (fun p => linkOnBdry d N x p),
          β * wilsonPlaquetteCost G n (plaquetteHolonomy
            (gluedConfig G d N ({x} : Finset _) v ρ) p))
        + ∑ p ∈ plaq.filter (fun p => ¬ linkOnBdry d N x p),
          β * wilsonPlaquetteCost G n (plaquetteHolonomy ρ p) := by
    intro ρ v; unfold wilsonAction
    rw [← Finset.sum_filter_add_sum_filter_not plaq (fun p => linkOnBdry d N x p)]
    congr 1; apply Finset.sum_congr rfl; intro p hp
    rw [Finset.mem_filter] at hp
    rw [holonomy_glue_eq_of_not_on_bdry G d N x ρ v p hp.2]
  -- For plaquettes containing x, the sum is the same for σ and τ.
  have h_x_eq : ∀ v,
      ∑ p ∈ plaq.filter (fun p => linkOnBdry d N x p),
        β * wilsonPlaquetteCost G n (plaquetteHolonomy
          (gluedConfig G d N ({x} : Finset _) v σ) p) =
      ∑ p ∈ plaq.filter (fun p => linkOnBdry d N x p),
        β * wilsonPlaquetteCost G n (plaquetteHolonomy
          (gluedConfig G d N ({x} : Finset _) v τ) p) := by
    intro v; apply Finset.sum_congr rfl; intro p hp
    rw [Finset.mem_filter] at hp
    rw [holonomy_glue_eq_of_on_bdry G d N plaq x y h_no_shared σ τ h_diff v p hp.1 hp.2]
  -- Abbreviations
  set Ax := fun v => ∑ p ∈ plaq.filter (fun p => linkOnBdry d N x p),
      β * wilsonPlaquetteCost G n (plaquetteHolonomy
        (gluedConfig G d N ({x} : Finset _) v σ) p)
  set Rσ := ∑ p ∈ plaq.filter (fun p => ¬ linkOnBdry d N x p),
      β * wilsonPlaquetteCost G n (plaquetteHolonomy σ p)
  set Rτ := ∑ p ∈ plaq.filter (fun p => ¬ linkOnBdry d N x p),
      β * wilsonPlaquetteCost G n (plaquetteHolonomy τ p)
  -- Rewrite everything using the action split
  have hσ : ∀ v, wilsonAction G n d N β
      (gluedConfig G d N ({x} : Finset _) v σ) plaq = Ax v + Rσ := h_action σ
  have hτ : ∀ v, wilsonAction G n d N β
      (gluedConfig G d N ({x} : Finset _) v τ) plaq = Ax v + Rτ := by
    intro v; rw [h_action τ v, (h_x_eq v).symm]
  -- Unfold definitions and use the split
  simp only [boltzmannWeight, gibbsConditionalZ, gibbsConditionalWeight]
  simp_rw [hσ, hτ, neg_add, Real.exp_add, MeasureTheory.integral_mul_const]
  ring

/-! ## The strong coupling wrapper theorem

Discharges measure-theoretic hypotheses (including 3 measurability
facts derived from `hRep_cont`), link distance, and conditional
integrability — leaving only the genuinely hard ones. -/

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
    -- Plaquette-per-link bound (combinatorial fact about the lattice):
    -- each link lies on at most `maxPlaquettesPerLink d = 2(d-1)` plaquettes.
    -- This implies the neighbor-count bounds `hMaxNeighborsCol/Row`
    -- via `maxNeighborsCol_of_plaqPerLink` / `maxNeighborsRow_of_plaqPerLink`.
    (hPlaqPerLink : ∀ ℓ : LatticeLink d N,
      (plaq.filter
        (fun p => ℓ ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks)).card
          ≤ maxPlaquettesPerLink d) :
    |connected2pt G n d N β plaq (plaqObs G n d N p) (plaqObs G n d N q)| ≤
      2 * (↑n : ℝ) * (↑n : ℝ) *
        ∑ x ∈ ((Finset.univ : Finset (Fin 4)).image
                (LatticePlaquette.boundaryLinks p)),
          ∑ y ∈ ((Finset.univ : Finset (Fin 4)).image
                (LatticePlaquette.boundaryLinks q)),
            (dobrushinColumnSum n d β) ^ ymLinkDist d N plaq y x /
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
  -- Discharge conditional integrability of plaqObs q
  have hPlaqObs_q_cond_int := plaqObs_cond_integrable G n d N β hβ plaq
    hTrace_upper hTrace_lower hw_meas p q hPlaqObs_q_meas
  -- Discharge link distance structure
  have h_refl := ymLinkDist_refl d N plaq
  have h_triangle := ymLinkDist_triangle d N plaq
  have h_support := ymLinkDist_support G n d N plaq β hZcond_pos
    hw_meas hw_integrable_cond hmeas_condDist hInfluence
  -- Derive neighbor-count bounds from plaquette-per-link bound.
  -- Since maxNeighbors d = 4 * maxPlaquettesPerLink d, the hLoose
  -- condition 4 * M ≤ maxNeighbors d is le_refl.
  have hMaxNeighborsCol : ∀ y : LatticeLink d N,
      ((Finset.univ : Finset (LatticeLink d N)).filter
        (fun x => sharesPlaquette d N plaq x y)).card ≤ maxNeighbors d :=
    fun y => (maxNeighborsCol_of_plaqPerLink d N plaq
      (maxPlaquettesPerLink d) hPlaqPerLink y).trans le_rfl
  have hMaxNeighborsRow : ∀ x : LatticeLink d N,
      ((Finset.univ : Finset (LatticeLink d N)).filter
        (fun y => sharesPlaquette d N plaq x y)).card ≤ maxNeighbors d :=
    fun x => (maxNeighborsRow_of_plaqPerLink d N plaq
      (maxPlaquettesPerLink d) hPlaqPerLink x).trans le_rfl
  -- Apply the upstream theorem
  exact ym_mass_gap_2pt_via_multisite G n d N hd hn β hβ hβ_small
    hTrace_lower hTrace_upper plaq p q
    hZcond_pos hw_meas hw_integrable_cond hmeas_condDist
    hZcond_meas hinner_meas hindA_fub_int hinner_w_over_Z_int hIntegrable_w
    hPlaqObs_p_meas hPlaqObs_q_meas hPlaqObs_p_int hPlaqObs_q_int hPlaqObs_pq_int
    hPlaqObs_pw_int hPlaqObs_qw_int hPlaqObs_pqw_int
    hInfluence hMaxNeighborsCol hMaxNeighborsRow hPlaqObs_q_cond_int
    (ymLinkDist d N plaq) h_refl h_triangle h_support hfinsupp
    (fun z B hB σ τ hagree =>
      condDist_cylinder_eq_of_agree_on_support
        (ymGibbsSpec G n d N plaq β hZcond_pos hw_meas
          hw_integrable_cond hmeas_condDist)
        z B hB (hfinsupp z) σ τ hagree)

end
