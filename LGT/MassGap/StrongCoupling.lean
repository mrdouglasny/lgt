/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Strong Coupling Wrapper for the d ≥ 3 Mass Gap

Discharges the measure-theoretic "plumbing" hypotheses of
`ym_mass_gap_2pt_via_multisite` (integrability, boundedness,
indicator-integrability, conditional partition function positivity,
finite support) and conditional integrability from first principles
— leaving only the genuinely hard analytic hypotheses
(parametrised-integral measurability, influence coefficient bounds,
local dependence) and a caller-supplied distance on links with the
standard refl / triangle / nearest-neighbor support hypotheses.

## Main result

`ym_mass_gap_strong_coupling` takes ~10 hypotheses instead of ~28.
The ~20 discharged ones (including `hcond_ae_bound` via
`condKernel_ae_bound`) are all consequences of:
- `Continuous (HasGaugeTrace.rep)` implies measurability of
  boltzmannWeight and plaqObs (via continuity chain)
- boltzmannWeight is bounded by 1 (for beta >= 0)
- plaqObs is bounded by n
- productHaar / ymMeasure are probability measures
- LatticeLink d N is a Fintype
- Bounded measurable functions are integrable on probability measures

The link distance is taken as a parameter; concrete instantiations
(an ambient shared-plaquette graph distance) yield genuine
geometric exponential decay — see `ym_mass_gap_exponential_decay`
below and `docs/mass-gap-completion-plan.md`.

## References

- Chatterjee (2026), §16.3
-/

import LGT.MassGap.MassGap3D
import LGT.GaugeField.UnitaryGroup
import Mathlib.Topology.Algebra.Star.Unitary
import MarkovSemigroups.Dobrushin.CondKernelDLR

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

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

instance instFirstCountableGaugeConnection :
    FirstCountableTopology (GaugeConnection G d N) :=
  show FirstCountableTopology (LatticeLink d N → G) from inferInstance

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

`ym_mass_gap_strong_coupling` below is parameterized by an arbitrary
distance `dLink : LatticeLink d N → LatticeLink d N → ℕ` together
with reflexivity, triangle inequality, and a nearest-neighbor
support hypothesis. The completion plan in
`docs/mass-gap-completion-plan.md` instantiates this at the ambient
shared-plaquette graph distance to obtain a genuine geometric
exponential decay theorem (`ym_mass_gap_exponential_decay`). -/


/-! ## Conditional integrability of bounded observables

A bounded measurable function is integrable on any probability measure.
We use this to discharge `hPlaqObs_q_cond_int`. -/

/-- `plaqObs q` is integrable on any `condFiniteSupportMeasure` of
`ymMeasure` — bounded + measurable on a probability measure. -/
theorem plaqObs_cond_integrable
    [Inhabited G]
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

/-! ## Continuity of parametric integrals (Fubini plumbing)

The key observation: `gluedConfig Λ uΛ σ` is continuous in σ (for each
fixed uΛ), because at each coordinate it's either constant (`uΛ e` when
`e ∈ Λ`) or `σ e` (continuous projection). Combined with
`continuous_boltzmannWeight`, this gives:

- `σ ↦ boltzmannWeight(gluedConfig Λ uΛ σ)` is continuous in σ for each uΛ
- By `continuous_of_dominated` (bounded by 1, integrable on prob measure),
  `σ ↦ ∫ uΛ, boltzmannWeight(gluedConfig Λ uΛ σ) = gibbsConditionalZ Λ σ`
  is continuous, hence measurable. -/

/-- `gluedConfig Λ uΛ` is continuous in σ: at each coordinate, it's
either constant (for `e ∈ Λ`) or the projection `σ e` (for `e ∉ Λ`). -/
theorem continuous_gluedConfig_sigma (Λ : Finset (LatticeLink d N))
    (uΛ : LatticeLink d N → G) :
    Continuous (fun σ : GaugeConnection G d N => gluedConfig G d N Λ uΛ σ) := by
  apply continuous_pi; intro e
  by_cases he : e ∈ Λ
  · -- e ∈ Λ: gluedConfig gives uΛ e, constant in σ
    have : (fun σ : GaugeConnection G d N => gluedConfig G d N Λ uΛ σ e) =
        fun _ => uΛ e := by
      funext σ; simp [gluedConfig, he]
    rw [this]; exact continuous_const
  · -- e ∉ Λ: gluedConfig gives σ e, a continuous projection
    have : (fun σ : GaugeConnection G d N => gluedConfig G d N Λ uΛ σ e) =
        fun σ => σ e := by
      funext σ; simp [gluedConfig, he]
    rw [this]; exact continuous_apply e

/-- The conditional Boltzmann weight is continuous in σ for each fixed uΛ. -/
theorem continuous_gibbsConditionalWeight_sigma
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (β : ℝ) (plaq : Finset (LatticePlaquette d N))
    (Λ : Finset (LatticeLink d N)) (uΛ : LatticeLink d N → G) :
    Continuous (fun σ : GaugeConnection G d N =>
      gibbsConditionalWeight G n d N plaq β Λ σ uΛ) := by
  unfold gibbsConditionalWeight
  exact (continuous_boltzmannWeight G n d N hRep_cont β plaq).comp
    (continuous_gluedConfig_sigma G d N Λ uΛ)

/-- `gibbsConditionalZ` is continuous in σ. Proved via `continuous_of_dominated`:
the integrand is continuous in σ (for each uΛ), bounded by 1, and 1 is integrable
on the probability measure `productHaar`. -/
theorem continuous_gibbsConditionalZ
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (β : ℝ) (hβ : 0 ≤ β) (plaq : Finset (LatticePlaquette d N))
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (Λ : Finset (LatticeLink d N)) :
    Continuous (fun σ => gibbsConditionalZ G n d N plaq β Λ σ) := by
  unfold gibbsConditionalZ
  apply continuous_of_dominated (μ := Measure.pi (fun _ : LatticeLink d N => haarG G))
  · -- AEStronglyMeasurable for each σ
    intro σ
    exact (measurable_boltzmannWeight_of_rep G n d N hRep_cont β plaq |>.comp
      (measurable_gluedConfig G d N Λ σ)).aestronglyMeasurable
  · -- Bounded by 1
    intro σ; apply Filter.Eventually.of_forall; intro uΛ
    simp only [gibbsConditionalWeight]
    rw [Real.norm_of_nonneg (boltzmannWeight_pos G n d N β _ plaq).le]
    exact boltzmannWeight_le_one G n d N β hβ _ plaq hTrace_upper
  · -- Bound 1 is integrable on probability measure
    exact integrable_const (1 : ℝ)
  · -- Pointwise continuity in σ for a.e. uΛ
    apply Filter.Eventually.of_forall; intro uΛ
    exact continuous_gibbsConditionalWeight_sigma G n d N hRep_cont β plaq Λ uΛ

/-- Measurability of `gibbsConditionalZ` follows from continuity. -/
theorem measurable_gibbsConditionalZ
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (β : ℝ) (hβ : 0 ≤ β) (plaq : Finset (LatticePlaquette d N))
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (Λ : Finset (LatticeLink d N)) :
    Measurable (fun σ => gibbsConditionalZ G n d N plaq β Λ σ) :=
  (continuous_gibbsConditionalZ G n d N hRep_cont β hβ plaq hTrace_upper Λ).measurable

set_option linter.unusedVariables false in
/-- Measurability of `σ ↦ ∫ uΛ, 1_A(gluedConfig uΛ σ) * w(gluedConfig uΛ σ)`.
Follows from `StronglyMeasurable.integral_prod_right'` via joint measurability. -/
theorem measurable_inner_integral
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (β : ℝ) (hβ : 0 ≤ β) (plaq : Finset (LatticePlaquette d N))
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (Λ : Finset (LatticeLink d N))
    (A : Set (GaugeConnection G d N)) (hA : MeasurableSet A) :
    Measurable (fun σ : GaugeConnection G d N =>
      ∫ uΛ, Set.indicator A
          (fun U => boltzmannWeight G n d N β U plaq)
          (gluedConfig G d N Λ uΛ σ) ∂(productHaar G d N)) := by
  -- The integrand is measurable in uΛ for each σ, bounded by 1.
  -- For measurability: use StronglyMeasurable.integral_prod_right
  -- The function (uΛ, σ) ↦ 1_A(glue uΛ σ) * w(glue uΛ σ) is measurable.
  unfold productHaar
  have hw_meas := measurable_boltzmannWeight_of_rep G n d N hRep_cont β plaq
  -- Use the fact that bounded measurable ⟹ strongly measurable integral
  -- and StronglyMeasurable.integral_prod_right for the parametric integral.
  -- The uncurried function f(σ, uΛ) = 1_A(glue uΛ σ) * w(glue uΛ σ) is measurable.
  -- gluedConfig is measurable jointly (σ, uΛ) ↦ glue uΛ σ.
  have hglue_joint : Measurable (fun (p : (LatticeLink d N → G) × (LatticeLink d N → G)) =>
      gluedConfig G d N Λ p.2 p.1) := by
    apply measurable_pi_iff.mpr; intro e
    by_cases he : e ∈ Λ
    · have : (fun p : (LatticeLink d N → G) × (LatticeLink d N → G) =>
          gluedConfig G d N Λ p.2 p.1 e) = fun p => p.2 e := by
        funext p; simp [gluedConfig, he]
      rw [this]; exact (measurable_pi_apply e).comp measurable_snd
    · have : (fun p : (LatticeLink d N → G) × (LatticeLink d N → G) =>
          gluedConfig G d N Λ p.2 p.1 e) = fun p => p.1 e := by
        funext p; simp [gluedConfig, he]
      rw [this]; exact (measurable_pi_apply e).comp measurable_fst
  -- f(σ, uΛ) = 1_A(glue uΛ σ) * w(glue uΛ σ) is measurable
  have hf_meas : Measurable (fun (p : (LatticeLink d N → G) × (LatticeLink d N → G)) =>
      Set.indicator A (fun U => boltzmannWeight G n d N β U plaq)
        (gluedConfig G d N Λ p.2 p.1)) :=
    (hw_meas.indicator hA).comp hglue_joint
  -- Use StronglyMeasurable.integral_prod_right (needs product measure, not Prod)
  -- Actually we need to convert to the right form. Use measurability from continuity approach.
  -- Alternative: prove measurability directly using AEStronglyMeasurable.integral
  -- For now, use Measurable.stronglyMeasurable and integral_prod_right.
  -- The measures are: σ lives on (LatticeLink d N → G) and uΛ on (LatticeLink d N → G).
  -- These are the same type! So we have f : (α × α) → ℝ measurable, and we integrate
  -- over the second coordinate. By StronglyMeasurable.integral_prod_right', this gives
  -- a strongly measurable function, hence measurable.
  exact (hf_meas.stronglyMeasurable.integral_prod_right').measurable

/-- Measurability of `σ ↦ (gibbsCondMeasure Λ σ A).toReal`.
This follows from measurability of the numerator integral and
the partition function Z(σ). -/
theorem measurable_gibbsCondMeasure_toReal
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (β : ℝ) (hβ : 0 ≤ β) (plaq : Finset (LatticePlaquette d N))
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (Λ : Finset (LatticeLink d N))
    (A : Set (GaugeConnection G d N)) (hA : MeasurableSet A) :
    Measurable (fun σ : GaugeConnection G d N =>
      (gibbsCondMeasure G n d N plaq β Λ σ A).toReal) := by
  have hw_meas := measurable_boltzmannWeight_of_rep G n d N hRep_cont β plaq
  -- Show: (gibbsCondMeasure ... σ A).toReal = inner(σ) / Z(σ) for each σ
  have hfun_eq : (fun σ => (gibbsCondMeasure G n d N plaq β Λ σ A).toReal) =
      fun σ => (∫ uΛ, Set.indicator A
            (fun U => boltzmannWeight G n d N β U plaq)
            (gluedConfig G d N Λ uΛ σ)
         ∂(productHaar G d N))
        / gibbsConditionalZ G n d N plaq β Λ σ := by
    funext σ
    exact gibbsCondMeasure_apply_toReal G n d N plaq β hw_meas Λ σ
      (gibbsConditionalZ_pos G n d N β hβ plaq hTrace_upper hTrace_lower hw_meas Λ σ)
      (gibbsConditionalWeight_integrable G n d N β hβ plaq hTrace_upper hw_meas Λ σ)
      A hA
  rw [hfun_eq]
  -- inner is measurable and Z is measurable
  exact (measurable_inner_integral G n d N hRep_cont β hβ plaq hTrace_upper Λ A hA).div
    (measurable_gibbsConditionalZ G n d N hRep_cont β hβ plaq hTrace_upper Λ)

/-- Integrability of `σ ↦ (inner(σ)/Z(σ)) * w(σ)` on productHaar.
All three factors are bounded: inner ≤ 1, 1/Z ≤ 1/c for some c > 0,
w ≤ 1. The product is bounded measurable on a probability measure. -/
theorem integrable_inner_w_over_Z
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (β : ℝ) (hβ : 0 ≤ β) (plaq : Finset (LatticePlaquette d N))
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (Λ : Finset (LatticeLink d N))
    (A : Set (GaugeConnection G d N)) (hA : MeasurableSet A) :
    Integrable (fun σ : GaugeConnection G d N =>
        (∫ uΛ, Set.indicator A
            (fun U => boltzmannWeight G n d N β U plaq)
            (gluedConfig G d N Λ uΛ σ) ∂(productHaar G d N))
          / gibbsConditionalZ G n d N plaq β Λ σ
        * boltzmannWeight G n d N β σ plaq) (productHaar G d N) := by
  have hw_meas := measurable_boltzmannWeight_of_rep G n d N hRep_cont β plaq
  -- Strategy: rewrite as (gibbsCondMeasure σ A).toReal * w(σ), both bounded by 1.
  -- Step 1: Show the function equals condMeasure.toReal * w
  have hfun_eq : (fun σ => (∫ uΛ, Set.indicator A
          (fun U => boltzmannWeight G n d N β U plaq)
          (gluedConfig G d N Λ uΛ σ) ∂(productHaar G d N))
        / gibbsConditionalZ G n d N plaq β Λ σ
      * boltzmannWeight G n d N β σ plaq) =
    fun σ => (gibbsCondMeasure G n d N plaq β Λ σ A).toReal *
      boltzmannWeight G n d N β σ plaq := by
    funext σ
    rw [← gibbsCondMeasure_apply_toReal G n d N plaq β hw_meas Λ σ
      (gibbsConditionalZ_pos G n d N β hβ plaq hTrace_upper hTrace_lower hw_meas Λ σ)
      (gibbsConditionalWeight_integrable G n d N β hβ plaq hTrace_upper hw_meas Λ σ)
      A hA]
  rw [hfun_eq]
  -- Step 2: Measurability
  have hmeas_condDist := measurable_gibbsCondMeasure_toReal G n d N hRep_cont β hβ plaq
    hTrace_upper hTrace_lower Λ A hA
  -- Step 3: Bounded by 1 on probability measure
  haveI : IsProbabilityMeasure (productHaar G d N) := by
    unfold productHaar
    exact MeasureTheory.Measure.pi.instIsProbabilityMeasure _
  apply Integrable.of_bound (hmeas_condDist.mul hw_meas).aestronglyMeasurable (1 : ℝ)
  apply Filter.Eventually.of_forall; intro σ
  -- (gibbsCondMeasure σ A).toReal ∈ [0, 1]
  have hcm_nn : 0 ≤ (gibbsCondMeasure G n d N plaq β Λ σ A).toReal :=
    ENNReal.toReal_nonneg
  have hcm_le : (gibbsCondMeasure G n d N plaq β Λ σ A).toReal ≤ 1 := by
    apply ENNReal.toReal_le_of_le_ofReal zero_le_one
    calc gibbsCondMeasure G n d N plaq β Λ σ A
        ≤ gibbsCondMeasure G n d N plaq β Λ σ Set.univ :=
          OuterMeasure.mono _ (Set.subset_univ _)
      _ = 1 := gibbsCondMeasure_total G n d N plaq β Λ σ
          (gibbsConditionalZ_pos G n d N β hβ plaq hTrace_upper hTrace_lower hw_meas Λ σ)
          hw_meas
          (gibbsConditionalWeight_integrable G n d N β hβ plaq hTrace_upper hw_meas Λ σ)
      _ = ENNReal.ofReal 1 := by simp
  -- w ∈ (0, 1]
  have hw_pos := boltzmannWeight_pos G n d N β σ plaq
  have hw_le := boltzmannWeight_le_one G n d N β hβ σ plaq hTrace_upper
  -- product ≤ 1
  rw [Real.norm_of_nonneg (mul_nonneg hcm_nn hw_pos.le)]
  exact mul_le_one₀ hcm_le hw_pos.le hw_le

/-! ## Off-plaquette influence: influenceCoeff = 0

When links x and y do not share a plaquette, the x-marginal of
`gibbsCondMeasure {x} σ` is the same for any two boundary conditions
σ, τ differing only at y. The proof uses `boltzmannWeight_factor_eq`
to show the density-weighted integrals are proportional, and then
that the normalised marginals agree. -/

/-- **Off-plaquette influence is zero.**

When `¬sharesPlaquette d N plaq x y`, the influence coefficient
`influenceCoeff (ymGibbsSpec ...) x y = 0`.

The proof: for any σ, τ differing only at y, `boltzmannWeight_factor_eq`
gives `w(glue u σ) / Z_σ = w(glue u τ) / Z_τ` for all u. Since the
x-component of `gluedConfig {x} u σ` is `u(x)` (independent of σ),
the marginals at x are equal, giving tvDist = 0 and hence
influenceCoeff = 0 (every element of the defining sSup set is 0). -/
theorem influenceCoeff_zero_off_plaquette
    (plaq : Finset (LatticePlaquette d N))
    (β : ℝ)
    (hZ_pos : ∀ Λ σ, 0 < gibbsConditionalZ G n d N plaq β Λ σ)
    (hw_meas : Measurable fun U => boltzmannWeight G n d N β U plaq)
    (hw_integrable : ∀ (Λ : Finset (LatticeLink d N))
        (σ : GaugeConnection G d N),
        Integrable (fun uΛ : LatticeLink d N → G =>
            gibbsConditionalWeight G n d N plaq β Λ σ uΛ)
          (Measure.pi (fun _ : LatticeLink d N => haarG G)))
    (hmeas_condDist : ∀ (Λ : Finset (LatticeLink d N))
      (A : Set (GaugeConnection G d N)),
      MeasurableSet A →
      Measurable (fun σ : GaugeConnection G d N =>
        ((gibbsCondMeasure G n d N plaq β Λ σ) A).toReal))
    (x y : LatticeLink d N)
    (h_no_shared : ¬ sharesPlaquette d N plaq x y) :
    influenceCoeff
      (ymGibbsSpec G n d N plaq β hZ_pos hw_meas hw_integrable hmeas_condDist)
      x y = 0 := by
  -- Strategy: show every element of the defining sSup set is 0.
  -- For each σ, τ differing only at y with ¬sharesPlaquette x y,
  -- the Boltzmann factorization identity implies the conditional measures
  -- at {x} have equal x-marginals, so tvDist = 0.
  set γ := ymGibbsSpec G n d N plaq β hZ_pos hw_meas hw_integrable hmeas_condDist
  -- Show: for all σ, τ differing only at y, the x-marginals of the conditional are equal.
  suffices h_marg_all : ∀ (σ τ : GaugeConnection G d N),
      (∀ z, z ≠ y → σ z = τ z) →
      ∀ (B : Set G), MeasurableSet B →
        (gibbsCondMeasure G n d N plaq β ({x} : Finset _) σ
            ((fun U : GaugeConnection G d N => U x) ⁻¹' B)) =
        (gibbsCondMeasure G n d N plaq β ({x} : Finset _) τ
            ((fun U : GaugeConnection G d N => U x) ⁻¹' B)) by
    -- From h_marg_all, derive marginal equality, then tvDist = 0, then influenceCoeff = 0.
    unfold influenceCoeff
    -- Every element of the defining set is 0
    have hall : ∀ c ∈ {c : ℝ | ∃ (σ τ : GaugeConnection G d N),
        (∀ z, z ≠ y → σ z = τ z) ∧
        c = tvDist (marginalAtSite (γ.condDist {x} σ) x)
                   (marginalAtSite (γ.condDist {x} τ) x)}, c = 0 := by
      rintro c ⟨σ, τ, hdiff, hc⟩
      rw [hc]
      -- The marginals are equal measures on G
      have hmarg_eq : marginalAtSite (γ.condDist {x} σ) x =
          marginalAtSite (γ.condDist {x} τ) x := by
        apply Measure.ext; intro B hB
        show (γ.condDist {x} σ).map (· x) B = (γ.condDist {x} τ).map (· x) B
        rw [Measure.map_apply (measurable_pi_apply x) hB,
            Measure.map_apply (measurable_pi_apply x) hB]
        exact h_marg_all σ τ hdiff B hB
      -- tvDist of equal measures is 0
      -- Rewrite using marginal equality: both marginals are the same measure
      have : tvDist (marginalAtSite (γ.condDist {x} σ) x)
                    (marginalAtSite (γ.condDist {x} τ) x) = 0 := by
        -- The two measures are equal, so every set difference is 0
        unfold tvDist
        have hset_eq : {c : ℝ | ∃ A : Set G, MeasurableSet A ∧
            c = |(marginalAtSite (γ.condDist {x} σ) x A).toReal -
                 (marginalAtSite (γ.condDist {x} τ) x A).toReal|} = {0} := by
          ext c
          simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
          constructor
          · rintro ⟨A, _, hcA⟩; rw [hcA, hmarg_eq]; simp
          · intro hc; exact ⟨Set.univ, MeasurableSet.univ, by rw [hc, hmarg_eq]; simp⟩
        rw [hset_eq, csSup_singleton]
      linarith
    -- We now need: sSup (defining set) = 0.
    -- This follows from: influenceCoeff_nonneg (gives ≥ 0) and hall (every element = 0 ≤ 0).
    -- Revert to the folded form and use the existing nonneg lemma.
    change influenceCoeff γ x y = 0
    exact le_antisymm
      (by -- influenceCoeff ≤ 0 because every element of the defining set is 0 (hence ≤ 0)
          unfold influenceCoeff
          apply csSup_le
          · -- Nonempty: take σ = τ = constant 1 config
            exact ⟨_, fun _ => (1 : G), fun _ => (1 : G), fun _ _ => rfl, rfl⟩
          · intro c hc; exact le_of_eq (hall c hc))
      (influenceCoeff_nonneg γ x y)
  -- Prove the key fact: conditional measure equality on cylinder sets
  intro σ τ hdiff B hB
  set A := (fun U : GaugeConnection G d N => U x) ⁻¹' B with hA_def
  have hA : MeasurableSet A := (measurable_pi_apply x) hB
  -- Use gibbsCondMeasure_apply_toReal for both sides
  have h_toReal_σ := gibbsCondMeasure_apply_toReal G n d N plaq β
    hw_meas ({x} : Finset _) σ (hZ_pos {x} σ) (hw_integrable {x} σ) A hA
  have h_toReal_τ := gibbsCondMeasure_apply_toReal G n d N plaq β
    hw_meas ({x} : Finset _) τ (hZ_pos {x} τ) (hw_integrable {x} τ) A hA
  -- Pointwise factor identity for indicator-weighted Boltzmann weights
  have h_pointwise : ∀ u : LatticeLink d N → G,
      Set.indicator A (fun U => boltzmannWeight G n d N β U plaq)
          (gluedConfig G d N ({x} : Finset _) u σ) *
        gibbsConditionalZ G n d N plaq β ({x} : Finset _) τ =
      Set.indicator A (fun U => boltzmannWeight G n d N β U plaq)
          (gluedConfig G d N ({x} : Finset _) u τ) *
        gibbsConditionalZ G n d N plaq β ({x} : Finset _) σ := by
    intro u
    have hx_mem : x ∈ ({x} : Finset (LatticeLink d N)) := Finset.mem_singleton_self x
    have hglue_σ_x := gluedConfig_eq_inside G d N _ u σ x hx_mem
    have hglue_τ_x := gluedConfig_eq_inside G d N _ u τ x hx_mem
    have hmem_iff : gluedConfig G d N ({x} : Finset _) u σ ∈ A ↔
        gluedConfig G d N ({x} : Finset _) u τ ∈ A := by
      simp only [hA_def, Set.mem_preimage, hglue_σ_x, hglue_τ_x]
    by_cases hmem : gluedConfig G d N ({x} : Finset _) u σ ∈ A
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hmem_iff.mp hmem)]
      exact boltzmannWeight_factor_eq G n d N plaq β x y h_no_shared σ τ hdiff u
    · rw [Set.indicator_of_notMem hmem,
        Set.indicator_of_notMem (fun h => hmem (hmem_iff.mpr h))]
      simp
  -- Integrate to get (∫ ind σ) * Z_τ = (∫ ind τ) * Z_σ
  have h_integral_factor :
      (∫ u, Set.indicator A (fun U => boltzmannWeight G n d N β U plaq)
          (gluedConfig G d N ({x} : Finset _) u σ) ∂(productHaar G d N)) *
        gibbsConditionalZ G n d N plaq β ({x} : Finset _) τ =
      (∫ u, Set.indicator A (fun U => boltzmannWeight G n d N β U plaq)
          (gluedConfig G d N ({x} : Finset _) u τ) ∂(productHaar G d N)) *
        gibbsConditionalZ G n d N plaq β ({x} : Finset _) σ := by
    rw [← integral_mul_const, ← integral_mul_const]
    exact integral_congr_ae (Filter.Eventually.of_forall h_pointwise)
  -- Show .toReal values equal, then lift to ENNReal
  have hZ_σ_pos := hZ_pos ({x} : Finset _) σ
  have hZ_τ_pos := hZ_pos ({x} : Finset _) τ
  have h_toReal_eq : (gibbsCondMeasure G n d N plaq β ({x} : Finset _) σ A).toReal =
      (gibbsCondMeasure G n d N plaq β ({x} : Finset _) τ A).toReal := by
    rw [h_toReal_σ, h_toReal_τ]
    rw [div_eq_div_iff hZ_σ_pos.ne' hZ_τ_pos.ne']
    linarith [h_integral_factor]
  -- The conditional measures are probability measures
  haveI : IsProbabilityMeasure (gibbsCondMeasure G n d N plaq β ({x} : Finset _) σ) :=
    (ymGibbsSpec G n d N plaq β hZ_pos hw_meas hw_integrable hmeas_condDist).isProb {x} σ
  haveI : IsProbabilityMeasure (gibbsCondMeasure G n d N plaq β ({x} : Finset _) τ) :=
    (ymGibbsSpec G n d N plaq β hZ_pos hw_meas hw_integrable hmeas_condDist).isProb {x} τ
  exact (ENNReal.toReal_eq_toReal_iff'
    (measure_ne_top _ _) (measure_ne_top _ _)).mp h_toReal_eq

/-! ## On-plaquette cylinder ratio bound

When links x, y share a plaquette, the conditional measure at {x}
satisfies a density ratio bound: for σ, τ differing only at y,

  condDist(τ)(B) ≤ exp(4nβ) · condDist(σ)(B)

The proof factors the Boltzmann weight as exp(-Ax) · exp(-R) where
Ax sums plaquettes containing x and R sums the rest. Since R is
constant with respect to the integration variable u (the link value
being sampled), it cancels in the conditional measure ratio, leaving
only the Ax ratio to bound. Among plaquettes containing x, only
those also containing y contribute to the Ax oscillation between σ
and τ (at most 2nβ per shared plaquette), giving the density ratio
exp(2nβ) and conditional ratio exp(4nβ). -/

/-- When a plaquette contains x but NOT y, the holonomy of
`gluedConfig {x} u σ` and `gluedConfig {x} u τ` agree (for σ, τ
differing only at y). This is the per-plaquette version of
`holonomy_glue_eq_of_on_bdry` without the global `¬sharesPlaquette`
hypothesis. -/
private theorem holonomy_glue_eq_of_on_bdry_not_y
    (x y : LatticeLink d N)
    (σ τ : GaugeConnection G d N) (h_diff : ∀ z, z ≠ y → σ z = τ z)
    (u : LatticeLink d N → G)
    (p : LatticePlaquette d N)
    (hx : linkOnBdry d N x p)
    (hy : ¬ linkOnBdry d N y p) :
    plaquetteHolonomy (gluedConfig G d N ({x} : Finset _) u σ) p =
    plaquetteHolonomy (gluedConfig G d N ({x} : Finset _) u τ) p := by
  simp only [plaquetteHolonomy]
  suffices ∀ i : Fin 4,
      gluedConfig G d N ({x} : Finset _) u σ (p.boundaryLinks i) =
      gluedConfig G d N ({x} : Finset _) u τ (p.boundaryLinks i) by
    rw [this 0, this 1, this 2, this 3]
  intro i
  by_cases hi : p.boundaryLinks i ∈ ({x} : Finset _)
  · rw [gluedConfig_eq_inside G d N _ u σ _ hi, gluedConfig_eq_inside G d N _ u τ _ hi]
  · rw [gluedConfig_eq_outside G d N _ u σ _ hi, gluedConfig_eq_outside G d N _ u τ _ hi]
    apply h_diff; intro hiy
    exact absurd (show linkOnBdry d N y p from by
      unfold linkOnBdry
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      exact ⟨i, hiy⟩) hy

set_option maxHeartbeats 800000 in
/-- **On-plaquette x-action oscillation bound.**

When σ, τ differ only at y, the x-plaquette action of `gluedConfig {x} u σ`
and `gluedConfig {x} u τ` differ by at most `β · 2n · K` where K is the
number of plaquettes containing both x and y. This uses the splitting of
x-plaquettes into those also containing y (bounded oscillation) and those
not containing y (zero oscillation). -/
private theorem xAction_oscillation_bound
    (plaq : Finset (LatticePlaquette d N))
    (β : ℝ) (hβ : 0 ≤ β)
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (x y : LatticeLink d N)
    (σ τ : GaugeConnection G d N) (h_diff : ∀ z, z ≠ y → σ z = τ z)
    (u : LatticeLink d N → G)
    (hK : (plaq.filter (fun p =>
      x ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks ∧
      y ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks)).card ≤ 1) :
    (∑ p ∈ plaq.filter (fun p => linkOnBdry d N x p),
        β * wilsonPlaquetteCost G n (plaquetteHolonomy
          (gluedConfig G d N ({x} : Finset _) u τ) p)) ≤
      (∑ p ∈ plaq.filter (fun p => linkOnBdry d N x p),
        β * wilsonPlaquetteCost G n (plaquetteHolonomy
          (gluedConfig G d N ({x} : Finset _) u σ) p)) + β * (2 * ↑n) := by
  -- Split x-plaquettes into those also containing y and those not.
  rw [← Finset.sum_filter_add_sum_filter_not
        (plaq.filter (fun p => linkOnBdry d N x p)) (fun p => linkOnBdry d N y p),
      ← Finset.sum_filter_add_sum_filter_not
        (plaq.filter (fun p => linkOnBdry d N x p)) (fun p => linkOnBdry d N y p)]
  -- For plaquettes containing x but NOT y, the sums are equal.
  have h_not_y_eq :
      ∑ p ∈ (plaq.filter (fun p => linkOnBdry d N x p)).filter
          (fun p => ¬ linkOnBdry d N y p),
        β * wilsonPlaquetteCost G n (plaquetteHolonomy
          (gluedConfig G d N ({x} : Finset _) u τ) p) =
      ∑ p ∈ (plaq.filter (fun p => linkOnBdry d N x p)).filter
          (fun p => ¬ linkOnBdry d N y p),
        β * wilsonPlaquetteCost G n (plaquetteHolonomy
          (gluedConfig G d N ({x} : Finset _) u σ) p) := by
    apply Finset.sum_congr rfl; intro p hp
    simp only [Finset.mem_filter] at hp
    rw [holonomy_glue_eq_of_on_bdry_not_y G d N x y σ τ h_diff u p hp.1.2 hp.2]
  rw [h_not_y_eq]
  -- Now need: shared_sum_τ + common ≤ shared_sum_σ + common + β * 2n
  -- Equivalently: shared_sum_τ ≤ shared_sum_σ + β * 2n
  linarith [show
      ∑ p ∈ (plaq.filter (fun p => linkOnBdry d N x p)).filter
          (fun p => linkOnBdry d N y p),
        β * wilsonPlaquetteCost G n (plaquetteHolonomy
          (gluedConfig G d N ({x} : Finset _) u τ) p) -
      ∑ p ∈ (plaq.filter (fun p => linkOnBdry d N x p)).filter
          (fun p => linkOnBdry d N y p),
        β * wilsonPlaquetteCost G n (plaquetteHolonomy
          (gluedConfig G d N ({x} : Finset _) u σ) p) ≤
        β * (2 * ↑n) from by
    -- The difference of sums over shared plaquettes:
    -- Each term β·cost ∈ [0, β·2n], so difference of sum ≤ β·2n when card ≤ 1.
    rw [← Finset.sum_sub_distrib]
    -- The shared plaquettes are those containing both x and y
    have hfilt_eq : (plaq.filter (fun p => linkOnBdry d N x p)).filter
        (fun p => linkOnBdry d N y p) =
        plaq.filter (fun p =>
          x ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks ∧
          y ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks) := by
      simp only [Finset.filter_filter]; congr 1; ext p; simp [linkOnBdry]
    rw [hfilt_eq]
    -- With at most 1 shared plaquette, the sum has at most 1 term.
    -- Each term: β * cost_τ - β * cost_σ = β * (cost_τ - cost_σ) ∈ [-β·2n, β·2n]
    -- So sum ≤ 1 · β · 2n = β · 2n.
    have hcard := hK
    -- Sum over at most 1 element, each in [-β·2n, β·2n]
    set S := plaq.filter (fun p =>
      x ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks ∧
      y ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks)
    -- Each term is bounded by β * 2n
    have hterm_bound : ∀ p ∈ S, β * wilsonPlaquetteCost G n
        (plaquetteHolonomy (gluedConfig G d N ({x} : Finset _) u τ) p) -
      β * wilsonPlaquetteCost G n
        (plaquetteHolonomy (gluedConfig G d N ({x} : Finset _) u σ) p) ≤
      β * (2 * ↑n) := by
      intro p _
      have hcost_τ : wilsonPlaquetteCost G n
          (plaquetteHolonomy (gluedConfig G d N ({x} : Finset _) u τ) p) ≤ 2 * ↑n := by
        unfold wilsonPlaquetteCost
        linarith [hTrace_lower (plaquetteHolonomy (gluedConfig G d N ({x} : Finset _) u τ) p)]
      have hcost_σ : 0 ≤ wilsonPlaquetteCost G n
          (plaquetteHolonomy (gluedConfig G d N ({x} : Finset _) u σ) p) := by
        unfold wilsonPlaquetteCost
        linarith [hTrace_upper (plaquetteHolonomy (gluedConfig G d N ({x} : Finset _) u σ) p)]
      nlinarith
    -- With card S ≤ 1 and each term ≤ β * 2n: sum ≤ β * 2n
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hcard with hc0 | hc1
    · -- card = 0 means S = ∅
      rw [Finset.card_eq_zero.mp hc0, Finset.sum_empty]
      positivity
    · -- card = 1 means S = {p} for some p
      obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc1
      rw [hp, Finset.sum_singleton]
      exact hterm_bound p (hp ▸ Finset.mem_singleton_self p)]

set_option maxHeartbeats 3200000 in
/-- **Boltzmann weight cross-product inequality (on-plaquette).**

When σ, τ differ only at y and at most 1 plaquette contains both x and y:
  w(glue u τ) · Z_σ ≤ exp(4nβ) · w(glue u σ) · Z_τ
Proved via the action decomposition into x-plaquettes (Ax) and rest (R).
The R-factors cancel in the cross product; the Ax oscillation gives
exp(2nβ) pointwise and exp(2nβ) from the integral, totalling exp(4nβ). -/
private theorem boltzmannWeight_factor_le
    (plaq : Finset (LatticePlaquette d N))
    (β : ℝ) (hβ : 0 ≤ β)
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (x y : LatticeLink d N)
    (σ τ : GaugeConnection G d N) (h_diff : ∀ z, z ≠ y → σ z = τ z)
    (hw_integrable : ∀ (Λ : Finset (LatticeLink d N))
        (σ : GaugeConnection G d N),
        Integrable (fun uΛ : LatticeLink d N → G =>
            gibbsConditionalWeight G n d N plaq β Λ σ uΛ)
          (Measure.pi (fun _ : LatticeLink d N => haarG G)))
    (hK : (plaq.filter (fun p =>
      x ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks ∧
      y ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks)).card ≤ 1)
    (u : LatticeLink d N → G) :
    boltzmannWeight G n d N β (gluedConfig G d N ({x} : Finset _) u τ) plaq *
      gibbsConditionalZ G n d N plaq β ({x} : Finset _) σ ≤
    Real.exp (4 * ↑n * β) *
      (boltzmannWeight G n d N β (gluedConfig G d N ({x} : Finset _) u σ) plaq *
        gibbsConditionalZ G n d N plaq β ({x} : Finset _) τ) := by
  -- Split the action into x-plaquettes (Ax) and rest (R)
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
  set Axσ := fun v => ∑ p ∈ plaq.filter (fun p => linkOnBdry d N x p),
      β * wilsonPlaquetteCost G n (plaquetteHolonomy
        (gluedConfig G d N ({x} : Finset _) v σ) p)
  set Axτ := fun v => ∑ p ∈ plaq.filter (fun p => linkOnBdry d N x p),
      β * wilsonPlaquetteCost G n (plaquetteHolonomy
        (gluedConfig G d N ({x} : Finset _) v τ) p)
  set Rσ := ∑ p ∈ plaq.filter (fun p => ¬ linkOnBdry d N x p),
      β * wilsonPlaquetteCost G n (plaquetteHolonomy σ p)
  set Rτ := ∑ p ∈ plaq.filter (fun p => ¬ linkOnBdry d N x p),
      β * wilsonPlaquetteCost G n (plaquetteHolonomy τ p)
  have hσ : ∀ v, wilsonAction G n d N β
      (gluedConfig G d N ({x} : Finset _) v σ) plaq = Axσ v + Rσ := h_action σ
  have hτ : ∀ v, wilsonAction G n d N β
      (gluedConfig G d N ({x} : Finset _) v τ) plaq = Axτ v + Rτ := h_action τ
  -- Key: Ax oscillation
  have hAx12 : ∀ v, Axτ v ≤ Axσ v + β * (2 * ↑n) :=
    fun v => xAction_oscillation_bound G n d N plaq β hβ hTrace_lower hTrace_upper
      x y σ τ h_diff v hK
  have hAx21 : ∀ v, Axσ v ≤ Axτ v + β * (2 * ↑n) :=
    fun v => xAction_oscillation_bound G n d N plaq β hβ hTrace_lower hTrace_upper
      x y τ σ (fun z hz => (h_diff z hz).symm) v hK
  -- Rewrite everything in terms of exp
  simp only [boltzmannWeight, gibbsConditionalZ, gibbsConditionalWeight]
  simp_rw [hσ, hτ, neg_add, Real.exp_add, MeasureTheory.integral_mul_const]
  -- After simplification, LHS and RHS have factor exp(-Rσ) * exp(-Rτ)
  -- which can be cancelled since it's positive.
  -- LHS: exp(-Axτ(u)) * exp(-Rτ) * (∫ exp(-Axσ) * exp(-Rσ))
  -- RHS: exp(4nβ) * (exp(-Axσ(u)) * exp(-Rσ) * (∫ exp(-Axτ) * exp(-Rτ)))
  -- Factor: both sides have exp(-Rσ) * exp(-Rτ) > 0
  have hRR_pos : 0 < Real.exp (-Rσ) * Real.exp (-Rτ) :=
    mul_pos (Real.exp_pos _) (Real.exp_pos _)
  -- Rearrange to isolate R factors
  suffices h : Real.exp (-Axτ u) * (∫ v, Real.exp (-Axσ v)
      ∂Measure.pi (fun _ : LatticeLink d N => haarG G)) ≤
      Real.exp (4 * ↑n * β) * (Real.exp (-Axσ u) * (∫ v, Real.exp (-Axτ v)
        ∂Measure.pi (fun _ : LatticeLink d N => haarG G))) by
    nlinarith [Real.exp_pos (-Rσ), Real.exp_pos (-Rτ)]
  -- Now prove the R-free inequality using Ax bounds
  have h1 : Real.exp (-Axτ u) ≤
      Real.exp (β * (2 * ↑n)) * Real.exp (-Axσ u) := by
    rw [← Real.exp_add]; apply Real.exp_le_exp_of_le; linarith [hAx21 u]
  -- Integrability lemmas
  have hAxσ_int : Integrable (fun v => Real.exp (-Axσ v))
      (Measure.pi (fun _ => haarG G)) := by
    have := hw_integrable ({x} : Finset _) σ
    rwa [show (fun v => gibbsConditionalWeight G n d N plaq β ({x} : Finset _) σ v) =
        fun v => Real.exp (-Axσ v) * Real.exp (-Rσ) from by
        ext v; simp [gibbsConditionalWeight, boltzmannWeight, hσ v, neg_add, Real.exp_add, mul_comm],
      MeasureTheory.integrable_mul_const_iff
        (isUnit_iff_ne_zero.mpr (Real.exp_pos (-Rσ)).ne')] at this
  have hAxτ_int : Integrable (fun v => Real.exp (-Axτ v))
      (Measure.pi (fun _ => haarG G)) := by
    have := hw_integrable ({x} : Finset _) τ
    rwa [show (fun v => gibbsConditionalWeight G n d N plaq β ({x} : Finset _) τ v) =
        fun v => Real.exp (-Axτ v) * Real.exp (-Rτ) from by
        ext v; simp [gibbsConditionalWeight, boltzmannWeight, hτ v, neg_add, Real.exp_add, mul_comm],
      MeasureTheory.integrable_mul_const_iff
        (isUnit_iff_ne_zero.mpr (Real.exp_pos (-Rτ)).ne')] at this
  have h2 : ∫ v, Real.exp (-Axσ v)
      ∂Measure.pi (fun _ : LatticeLink d N => haarG G) ≤
      Real.exp (β * (2 * ↑n)) * ∫ v, Real.exp (-Axτ v)
        ∂Measure.pi (fun _ : LatticeLink d N => haarG G) := by
    calc ∫ v, Real.exp (-Axσ v) ∂Measure.pi (fun _ => haarG G)
        ≤ ∫ v, Real.exp (β * (2 * ↑n)) * Real.exp (-Axτ v)
            ∂Measure.pi (fun _ => haarG G) := by
          apply MeasureTheory.integral_mono hAxσ_int (hAxτ_int.const_mul _)
          intro v; show Real.exp _ ≤ Real.exp _ * Real.exp _
          rw [← Real.exp_add]; apply Real.exp_le_exp_of_le; linarith [hAx12 v]
      _ = Real.exp (β * (2 * ↑n)) * ∫ v, Real.exp (-Axτ v)
            ∂Measure.pi (fun _ => haarG G) := by
          rw [integral_const_mul]
  -- Combine
  have hint_nn : 0 ≤ ∫ v, Real.exp (-Axτ v)
      ∂Measure.pi (fun _ : LatticeLink d N => haarG G) :=
    MeasureTheory.integral_nonneg (fun _ => (Real.exp_pos _).le)
  calc Real.exp (-Axτ u) * ∫ v, Real.exp (-Axσ v) ∂Measure.pi (fun _ => haarG G)
      ≤ (Real.exp (β * (2 * ↑n)) * Real.exp (-Axσ u)) *
        (Real.exp (β * (2 * ↑n)) * ∫ v, Real.exp (-Axτ v)
          ∂Measure.pi (fun _ => haarG G)) :=
        mul_le_mul h1 h2
          (MeasureTheory.integral_nonneg (fun _ => (Real.exp_pos _).le))
          (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    _ = Real.exp (4 * ↑n * β) *
        (Real.exp (-Axσ u) * ∫ v, Real.exp (-Axτ v) ∂Measure.pi (fun _ => haarG G)) := by
        have : Real.exp (β * (2 * ↑n)) * Real.exp (β * (2 * ↑n)) =
            Real.exp (4 * ↑n * β) := by
          rw [← Real.exp_add]; congr 1; ring
        calc Real.exp (β * (2 * ↑n)) * Real.exp (-Axσ u) *
              (Real.exp (β * (2 * ↑n)) *
                ∫ v, Real.exp (-Axτ v) ∂Measure.pi (fun _ => haarG G))
            = (Real.exp (β * (2 * ↑n)) * Real.exp (β * (2 * ↑n))) *
              (Real.exp (-Axσ u) *
                ∫ v, Real.exp (-Axτ v) ∂Measure.pi (fun _ => haarG G)) := by ring
          _ = _ := by rw [this]

set_option maxHeartbeats 3200000 in
/-- **On-plaquette cylinder ratio bound.** -/
theorem gibbsCondMeasure_cylinder_ratio
    (plaq : Finset (LatticePlaquette d N))
    (β : ℝ) (hβ : 0 ≤ β)
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (x y : LatticeLink d N)
    (hw_meas : Measurable fun U => boltzmannWeight G n d N β U plaq)
    (hZ_pos : ∀ Λ σ, 0 < gibbsConditionalZ G n d N plaq β Λ σ)
    (hw_integrable : ∀ (Λ : Finset (LatticeLink d N))
        (σ : GaugeConnection G d N),
        Integrable (fun uΛ : LatticeLink d N → G =>
            gibbsConditionalWeight G n d N plaq β Λ σ uΛ)
          (Measure.pi (fun _ : LatticeLink d N => haarG G)))
    (hK : (plaq.filter (fun p =>
      x ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks ∧
      y ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks)).card ≤ 1)
    (σ τ : GaugeConnection G d N) (h_diff : ∀ z, z ≠ y → σ z = τ z)
    (B : Set G) (hB : MeasurableSet B) :
    (gibbsCondMeasure G n d N plaq β ({x} : Finset _) τ
      ((fun U : GaugeConnection G d N => U x) ⁻¹' B)).toReal ≤
    Real.exp (4 * ↑n * β) *
      (gibbsCondMeasure G n d N plaq β ({x} : Finset _) σ
        ((fun U : GaugeConnection G d N => U x) ⁻¹' B)).toReal := by
  set A := (fun U : GaugeConnection G d N => U x) ⁻¹' B with hA_def
  have hA : MeasurableSet A := (measurable_pi_apply x) hB
  rw [gibbsCondMeasure_apply_toReal G n d N plaq β hw_meas ({x} : Finset _)
        σ (hZ_pos {x} σ) (hw_integrable {x} σ) A hA,
      gibbsCondMeasure_apply_toReal G n d N plaq β hw_meas ({x} : Finset _)
        τ (hZ_pos {x} τ) (hw_integrable {x} τ) A hA]
  set Zσ := gibbsConditionalZ G n d N plaq β ({x} : Finset _) σ
  set Zτ := gibbsConditionalZ G n d N plaq β ({x} : Finset _) τ
  have hZσ_pos := hZ_pos ({x} : Finset _) σ
  have hZτ_pos := hZ_pos ({x} : Finset _) τ
  -- Pointwise cross-product inequality
  have h_pointwise : ∀ u : LatticeLink d N → G,
      Set.indicator A (fun U => boltzmannWeight G n d N β U plaq)
          (gluedConfig G d N ({x} : Finset _) u τ) * Zσ ≤
      Real.exp (4 * ↑n * β) *
        (Set.indicator A (fun U => boltzmannWeight G n d N β U plaq)
          (gluedConfig G d N ({x} : Finset _) u σ) * Zτ) := by
    intro u
    have hx_mem : x ∈ ({x} : Finset (LatticeLink d N)) := Finset.mem_singleton_self x
    have hmem_iff : gluedConfig G d N ({x} : Finset _) u σ ∈ A ↔
        gluedConfig G d N ({x} : Finset _) u τ ∈ A := by
      simp only [hA_def, Set.mem_preimage,
        gluedConfig_eq_inside G d N _ u σ x hx_mem,
        gluedConfig_eq_inside G d N _ u τ x hx_mem]
    by_cases hmem : gluedConfig G d N ({x} : Finset _) u σ ∈ A
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hmem_iff.mp hmem)]
      exact boltzmannWeight_factor_le G n d N plaq β hβ hTrace_lower hTrace_upper
        x y σ τ h_diff hw_integrable hK u
    · rw [Set.indicator_of_notMem hmem,
          Set.indicator_of_notMem (fun h => hmem (hmem_iff.mpr h))]
      simp
  -- Divide the pointwise bound by (Zσ * Zτ) to get pointwise ratio bound
  have h_ratio_pointwise : ∀ u : LatticeLink d N → G,
      Set.indicator A (fun U => boltzmannWeight G n d N β U plaq)
          (gluedConfig G d N ({x} : Finset _) u τ) / Zτ ≤
      Real.exp (4 * ↑n * β) *
        (Set.indicator A (fun U => boltzmannWeight G n d N β U plaq)
          (gluedConfig G d N ({x} : Finset _) u σ) / Zσ) := by
    intro u
    have hp := h_pointwise u
    have hind_nn : 0 ≤ Set.indicator A (fun U => boltzmannWeight G n d N β U plaq)
        (gluedConfig G d N ({x} : Finset _) u σ) :=
      Set.indicator_nonneg (fun _ _ => (boltzmannWeight_pos G n d N β _ plaq).le) _
    rw [div_le_iff₀ hZτ_pos]
    calc Set.indicator A (fun U => boltzmannWeight G n d N β U plaq)
          (gluedConfig G d N ({x} : Finset _) u τ)
        = Set.indicator A (fun U => boltzmannWeight G n d N β U plaq)
            (gluedConfig G d N ({x} : Finset _) u τ) * Zσ / Zσ := by
          rw [mul_div_cancel_right₀ _ hZσ_pos.ne']
      _ ≤ Real.exp (4 * ↑n * β) *
            (Set.indicator A (fun U => boltzmannWeight G n d N β U plaq)
              (gluedConfig G d N ({x} : Finset _) u σ) * Zτ) / Zσ := by
          apply div_le_div_of_nonneg_right hp hZσ_pos.le
      _ = Real.exp (4 * ↑n * β) *
            (Set.indicator A (fun U => boltzmannWeight G n d N β U plaq)
              (gluedConfig G d N ({x} : Finset _) u σ) / Zσ) * Zτ := by
          ring
  -- Integrate the ratio bound
  calc (∫ u, Set.indicator A (fun U => boltzmannWeight G n d N β U plaq)
        (gluedConfig G d N ({x} : Finset _) u τ) ∂productHaar G d N) / Zτ
      = ∫ u, Set.indicator A (fun U => boltzmannWeight G n d N β U plaq)
          (gluedConfig G d N ({x} : Finset _) u τ) / Zτ ∂productHaar G d N := by
        rw [integral_div]
    _ ≤ ∫ u, Real.exp (4 * ↑n * β) *
          (Set.indicator A (fun U => boltzmannWeight G n d N β U plaq)
            (gluedConfig G d N ({x} : Finset _) u σ) / Zσ) ∂productHaar G d N := by
        apply MeasureTheory.integral_mono
        · -- Integrability of ind/Zτ: bounded on probability measure
          apply Integrable.div_const
          exact (integrable_const (1 : ℝ)).mono
            ((hw_meas.indicator hA).comp
              (measurable_gluedConfig G d N ({x} : Finset _) τ)).aestronglyMeasurable
            (Filter.Eventually.of_forall (fun u => by
              rw [Real.norm_of_nonneg (Set.indicator_nonneg
                (fun _ _ => (boltzmannWeight_pos G n d N β _ plaq).le) _), norm_one]
              exact Set.indicator_apply_le'
                (fun _ => boltzmannWeight_le_one G n d N β hβ _ plaq hTrace_upper)
                (fun _ => zero_le_one)))
        · -- Integrability of exp * (ind/Zσ)
          apply Integrable.const_mul; apply Integrable.div_const
          exact (integrable_const (1 : ℝ)).mono
            ((hw_meas.indicator hA).comp
              (measurable_gluedConfig G d N ({x} : Finset _) σ)).aestronglyMeasurable
            (Filter.Eventually.of_forall (fun u => by
              rw [Real.norm_of_nonneg (Set.indicator_nonneg
                (fun _ _ => (boltzmannWeight_pos G n d N β _ plaq).le) _), norm_one]
              exact Set.indicator_apply_le'
                (fun _ => boltzmannWeight_le_one G n d N β hβ _ plaq hTrace_upper)
                (fun _ => zero_le_one)))
        · exact h_ratio_pointwise
    _ = Real.exp (4 * ↑n * β) * ((∫ u, Set.indicator A
            (fun U => boltzmannWeight G n d N β U plaq)
            (gluedConfig G d N ({x} : Finset _) u σ) ∂productHaar G d N) / Zσ) := by
        rw [← integral_div, ← integral_const_mul]

/-! ## Combining influence bounds into hInfluence

The off-plaquette case (`influenceCoeff = 0` when `¬sharesPlaquette`) is
fully proved via `boltzmannWeight_factor_eq`. The on-plaquette case
(`influenceCoeff ≤ influenceBound n β`) is derived from the cylinder ratio
bound `gibbsCondMeasure_cylinder_ratio` via
`influenceCoeff_le_of_cylinder_ratio_bound_nocount` (local, without `[Countable]`).
The combinator `influenceCoeff_le_bound` then packages both cases. -/

/-- **Full influence coefficient bound.**

Combines the off-plaquette zero-influence theorem
(`influenceCoeff_zero_off_plaquette`) with an assumed on-plaquette
TV bound to produce the full `hInfluence` hypothesis. -/
theorem influenceCoeff_le_bound
    (plaq : Finset (LatticePlaquette d N))
    (β : ℝ)
    (hZ_pos : ∀ Λ σ, 0 < gibbsConditionalZ G n d N plaq β Λ σ)
    (hw_meas : Measurable fun U => boltzmannWeight G n d N β U plaq)
    (hw_integrable : ∀ (Λ : Finset (LatticeLink d N))
        (σ : GaugeConnection G d N),
        Integrable (fun uΛ : LatticeLink d N → G =>
            gibbsConditionalWeight G n d N plaq β Λ σ uΛ)
          (Measure.pi (fun _ : LatticeLink d N => haarG G)))
    (hmeas_condDist : ∀ (Λ : Finset (LatticeLink d N))
      (A : Set (GaugeConnection G d N)),
      MeasurableSet A →
      Measurable (fun σ : GaugeConnection G d N =>
        ((gibbsCondMeasure G n d N plaq β Λ σ) A).toReal))
    -- On-plaquette Boltzmann TV bound (standard Dobrushin estimate):
    (hOnPlaq : ∀ x y : LatticeLink d N, sharesPlaquette d N plaq x y →
      influenceCoeff
        (ymGibbsSpec G n d N plaq β hZ_pos hw_meas hw_integrable hmeas_condDist)
        x y ≤ influenceBound n β)
    (x y : LatticeLink d N) :
    influenceCoeff
      (ymGibbsSpec G n d N plaq β hZ_pos hw_meas hw_integrable hmeas_condDist)
      x y ≤ (if sharesPlaquette d N plaq x y then influenceBound n β else 0) := by
  by_cases hshare : sharesPlaquette d N plaq x y
  · -- On-plaquette: use the assumed TV bound
    rw [if_pos hshare]
    exact hOnPlaq x y hshare
  · -- Off-plaquette: influenceCoeff = 0
    rw [if_neg hshare]
    exact le_of_eq (influenceCoeff_zero_off_plaquette G n d N plaq β hZ_pos hw_meas
      hw_integrable hmeas_condDist x y hshare)

/-! ## Local `_nocount` version of `influenceCoeff_le_of_cylinder_ratio_bound`

The upstream lemma `influenceCoeff_le_of_cylinder_ratio_bound` in
`MarkovSemigroups.Dobrushin.Uniqueness` carries `[Countable S]` in its
signature, but its proof only uses `[MeasurableSingletonClass S]`.
We reproduce it here without `Countable` so that
`ym_mass_gap_strong_coupling` can drop the `[Countable G]` hypothesis. -/

private lemma abs_sub_le_one_sub_exp_neg'
    {p q C : ℝ} (hC : 0 ≤ C)
    (_ : 0 ≤ q) (hq1 : q ≤ 1)
    (h1 : Real.exp (-C) * q ≤ p)
    (h2 : Real.exp (-C) * (1 - q) ≤ 1 - p) :
    |p - q| ≤ 1 - Real.exp (-C) := by
  have hexp_le : Real.exp (-C) ≤ 1 := by
    rw [Real.exp_neg]; exact inv_le_one_of_one_le₀ (Real.one_le_exp hC)
  rw [abs_le]
  constructor
  · have : q * (1 - Real.exp (-C)) ≤ 1 - Real.exp (-C) :=
      mul_le_of_le_one_left (sub_nonneg.mpr hexp_le) hq1
    nlinarith
  · have : (1 - q) * (1 - Real.exp (-C)) ≤ 1 - Real.exp (-C) :=
      mul_le_of_le_one_left (sub_nonneg.mpr hexp_le) (by linarith)
    nlinarith

private lemma prob_compl_toReal_eq' {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (A : Set X) (hA : MeasurableSet A) :
    (μ Aᶜ).toReal = 1 - (μ A).toReal := by
  rw [prob_compl_eq_one_sub hA,
      ENNReal.toReal_sub_of_le (prob_le_one (s := A)) ENNReal.one_ne_top]
  simp

/-- Local version of `influenceCoeff_le_of_cylinder_ratio_bound` without
`[Countable S]`. The upstream version carries `[Countable S]` but only
uses `[MeasurableSingletonClass S]` in its proof. -/
theorem influenceCoeff_le_of_cylinder_ratio_bound_nocount
    {I : Type*} [DecidableEq I] {S : Type*} [MeasurableSpace S]
    (γ : GibbsSpec I S) (x y : I)
    (C : ℝ) (hC : 0 ≤ C)
    (hRatio : ∀ (σ τ : SpinConfig I S),
      (∀ z, z ≠ y → σ z = τ z) →
      ∀ (B : Set S), MeasurableSet B →
        (γ.condDist {x} τ ((fun σ => σ x) ⁻¹' B)).toReal ≤
          Real.exp C * (γ.condDist {x} σ ((fun σ => σ x) ⁻¹' B)).toReal) :
    influenceCoeff γ x y ≤ 1 - Real.exp (-C) := by
  unfold influenceCoeff
  by_cases hne : {c : ℝ | ∃ (σ τ : SpinConfig I S),
    (∀ z, z ≠ y → σ z = τ z) ∧
    c = tvDist (marginalAtSite (γ.condDist {x} σ) x)
               (marginalAtSite (γ.condDist {x} τ) x)}.Nonempty
  · apply csSup_le hne
    rintro c ⟨σ, τ, hdiff, rfl⟩
    apply csSup_le (tvDist_set_nonempty _ _)
    rintro c' ⟨B, hB, rfl⟩
    rw [marginalAtSite_apply _ _ hB, marginalAtSite_apply _ _ hB]
    set A := (fun σ' : SpinConfig I S => σ' x) ⁻¹' B
    have hA_meas : MeasurableSet A := (measurable_pi_apply x) hB
    have hexp_inv :
        Real.exp (-C) * (γ.condDist {x} τ A).toReal ≤
          (γ.condDist {x} σ A).toReal := by
      rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos C)]
      exact hRatio σ τ hdiff B hB
    have hexp_compl :
        Real.exp (-C) * (1 - (γ.condDist {x} τ A).toReal) ≤
          1 - (γ.condDist {x} σ A).toReal := by
      rw [Real.exp_neg, inv_mul_le_iff₀ (Real.exp_pos C)]
      have hBc : MeasurableSet Bᶜ := hB.compl
      have := hRatio σ τ hdiff Bᶜ hBc
      rwa [Set.preimage_compl,
           prob_compl_toReal_eq' _ _ hA_meas,
           prob_compl_toReal_eq' _ _ hA_meas] at this
    exact abs_sub_le_one_sub_exp_neg' hC
      ENNReal.toReal_nonneg (condDist_toReal_le_one γ x τ _)
      hexp_inv hexp_compl
  · simp only [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Real.sSup_empty]
    have : Real.exp (-C) ≤ 1 := by
      rw [Real.exp_neg]; exact inv_le_one_of_one_le₀ (Real.one_le_exp hC)
    linarith

/-! ## The strong coupling wrapper theorem

Discharges measure-theoretic hypotheses (including 3 measurability
facts derived from `hRep_cont`), link distance, and conditional
integrability — leaving only the genuinely hard ones. -/

set_option maxHeartbeats 3200000 in
theorem ym_mass_gap_strong_coupling
    [Inhabited G]
    (hd : 2 ≤ d) (hn : 1 ≤ n) (hN : 2 < N)
    (β : ℝ) (hβ : 0 ≤ β)
    (hβ_small : β < 1 / (4 * ↑n * ↑(maxNeighbors d)))
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (plaq : Finset (LatticePlaquette d N))
    (p q : LatticePlaquette d N)
    -- Core continuity (implies measurability of boltzmannWeight and plaqObs):
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    -- Distance on links + its metric/support hypotheses. The caller
    -- chooses the distance; the theorem is generic. Concrete instantiations:
    -- a genuine ambient shared-plaquette graph distance (see
    -- `docs/mass-gap-completion-plan.md`) yields exponential decay in
    -- geometric plaquette separation.
    (dLink : LatticeLink d N → LatticeLink d N → ℕ)
    (h_refl : ∀ x, dLink x x = 0)
    (h_triangle : ∀ x y z, dLink x y ≤ dLink x z + dLink z y)
    (h_support :
      ∀ Λ_pos hw_meas hw_int hmeas_cd,
      ∀ (_hInfluence : ∀ x y : LatticeLink d N,
          influenceCoeff
            (ymGibbsSpec G n d N plaq β Λ_pos hw_meas hw_int hmeas_cd) x y ≤
            (if sharesPlaquette d N plaq x y then influenceBound n β else 0)),
      ∀ (u v : LatticeLink d N), dLink u v > 1 →
        influenceCoeff
          (ymGibbsSpec G n d N plaq β Λ_pos hw_meas hw_int hmeas_cd) u v = 0)
    -- (Shared plaquette bound and plaquette-per-link bound are now discharged
    --  from the CellComplex incidence lemmas shared_plaquettes_le_one and
    --  plaquettes_per_link_le'.)
    :
    |connected2pt G n d N β plaq (plaqObs G n d N p) (plaqObs G n d N q)| ≤
      2 * (↑n : ℝ) * (↑n : ℝ) *
        ∑ x ∈ ((Finset.univ : Finset (Fin 4)).image
                (LatticePlaquette.boundaryLinks p)),
          ∑ y ∈ ((Finset.univ : Finset (Fin 4)).image
                (LatticePlaquette.boundaryLinks q)),
            (dobrushinAlpha n d β) ^ dLink y x /
              (1 - dobrushinAlpha n d β) := by
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
  -- Discharge the 4 Fubini/parametrised-integral hypotheses
  have hmeas_condDist : ∀ (Λ : Finset (LatticeLink d N))
      (A : Set (GaugeConnection G d N)), MeasurableSet A →
      Measurable (fun σ : GaugeConnection G d N =>
        (gibbsCondMeasure G n d N plaq β Λ σ A).toReal) :=
    fun Λ A hA => measurable_gibbsCondMeasure_toReal G n d N
      hRep_cont β hβ plaq hTrace_upper hTrace_lower Λ A hA
  have hZcond_meas : ∀ Λ : Finset (LatticeLink d N),
      Measurable (fun σ : GaugeConnection G d N =>
        gibbsConditionalZ G n d N plaq β Λ σ) :=
    fun Λ => measurable_gibbsConditionalZ G n d N hRep_cont β hβ plaq hTrace_upper Λ
  have hinner_meas : ∀ (Λ : Finset (LatticeLink d N))
      (A : Set (GaugeConnection G d N)), MeasurableSet A →
      Measurable (fun σ : GaugeConnection G d N =>
        ∫ uΛ, Set.indicator A
            (fun U => boltzmannWeight G n d N β U plaq)
            (gluedConfig G d N Λ uΛ σ) ∂(productHaar G d N)) :=
    fun Λ A hA => measurable_inner_integral G n d N hRep_cont β hβ plaq hTrace_upper Λ A hA
  have hinner_w_over_Z_int : ∀ (Λ : Finset (LatticeLink d N))
      (A : Set (GaugeConnection G d N)), MeasurableSet A →
      Integrable (fun σ : GaugeConnection G d N =>
          (∫ uΛ, Set.indicator A
              (fun U => boltzmannWeight G n d N β U plaq)
              (gluedConfig G d N Λ uΛ σ) ∂(productHaar G d N))
            / gibbsConditionalZ G n d N plaq β Λ σ
          * boltzmannWeight G n d N β σ plaq) (productHaar G d N) :=
    fun Λ A hA => integrable_inner_w_over_Z G n d N hRep_cont β hβ plaq
      hTrace_upper hTrace_lower Λ A hA
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
  -- Derive shared plaquette bound from CellComplex incidence lemma.
  -- shared_plaquettes_le_one requires x ≠ y; for x = y we handle separately.
  have hPlaqPerLink : ∀ ℓ : LatticeLink d N,
      (plaq.filter
        (fun p => ℓ ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks)).card
          ≤ maxPlaquettesPerLink d := by
    intro l
    have h := plaquettes_per_link_le' l plaq
    show _ ≤ maxPlaquettesPerLink d
    simp only [maxPlaquettesPerLink, maxPlaquettesPerLink'] at h ⊢
    convert h
  -- Derive the on-plaquette influence bound.
  -- For x ≠ y: use the cylinder ratio bound with shared_plaquettes_le_one.
  -- For x = y: the influence coefficient is 0 (condDist consistency).
  have hOnPlaq : ∀ x y : LatticeLink d N, sharesPlaquette d N plaq x y →
      influenceCoeff
        (ymGibbsSpec G n d N plaq β hZcond_pos hw_meas
          hw_integrable_cond hmeas_condDist) x y ≤ influenceBound n β := by
    intro x y hshare
    by_cases hxy : x = y
    · -- x = y: influenceCoeff γ x x = 0 by condDist consistency
      subst hxy
      set γ := ymGibbsSpec G n d N plaq β hZcond_pos hw_meas hw_integrable_cond hmeas_condDist
      have hle : influenceCoeff γ x x ≤ 1 - Real.exp (-(0 : ℝ)) :=
        influenceCoeff_le_of_cylinder_ratio_bound_nocount γ x x 0 le_rfl
          (fun σ τ hdiff B hB => by
            rw [Real.exp_zero, one_mul]
            have heq := γ.consistent {x} σ τ
              (fun z hz => hdiff z (by rwa [Finset.mem_singleton] at hz))
            rw [heq])
      simp [Real.exp_zero] at hle
      linarith [influenceBound_nonneg n β hβ]
    · -- x ≠ y: use shared_plaquettes_le_one and cylinder ratio bound
      have hSharedBound : (plaq.filter (fun p =>
          x ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks ∧
          y ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks)).card ≤ 1 := by
        have := shared_plaquettes_le_one hN x y hxy plaq
        convert this
      have hC : (0 : ℝ) ≤ 4 * ↑n * β := by positivity
      have hkey := influenceCoeff_le_of_cylinder_ratio_bound_nocount
        (ymGibbsSpec G n d N plaq β hZcond_pos hw_meas hw_integrable_cond hmeas_condDist)
        x y (4 * ↑n * β) hC
        (fun σ τ hdiff B hB => by
          show (gibbsCondMeasure G n d N plaq β ({x} : Finset _) τ
                ((fun U : GaugeConnection G d N => U x) ⁻¹' B)).toReal ≤
              Real.exp (4 * ↑n * β) *
                (gibbsCondMeasure G n d N plaq β ({x} : Finset _) σ
                  ((fun U : GaugeConnection G d N => U x) ⁻¹' B)).toReal
          exact gibbsCondMeasure_cylinder_ratio G n d N plaq β hβ hTrace_lower hTrace_upper
            x y hw_meas hZcond_pos hw_integrable_cond hSharedBound σ τ hdiff B hB)
      unfold influenceBound
      convert hkey using 2
      ring
  -- Construct the full influence bound from the derived on-plaquette bound
  -- and the off-plaquette zero-influence theorem.
  have hInfluence : ∀ x y : LatticeLink d N,
      influenceCoeff
        (ymGibbsSpec G n d N plaq β hZcond_pos hw_meas
          hw_integrable_cond hmeas_condDist) x y ≤
        (if sharesPlaquette d N plaq x y then influenceBound n β else 0) :=
    influenceCoeff_le_bound G n d N plaq β hZcond_pos hw_meas
      hw_integrable_cond hmeas_condDist hOnPlaq
  -- Distance refl/triangle come straight from caller's hypotheses.
  -- Specialize the caller-supplied support hypothesis to the YM Gibbs
  -- spec and the influence-bound just derived.
  have h_support_inst : ∀ u v : LatticeLink d N, dLink u v > 1 →
      influenceCoeff
        (ymGibbsSpec G n d N plaq β hZcond_pos hw_meas
          hw_integrable_cond hmeas_condDist) u v = 0 :=
    h_support hZcond_pos hw_meas hw_integrable_cond hmeas_condDist hInfluence
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
  -- Construct IsProbabilityMeasure for ymMeasure
  have hμ_prob : IsProbabilityMeasure (ymMeasure G n d N β plaq) :=
    ymMeasure_isProbabilityMeasure G n d N β hβ plaq hTrace_upper hTrace_lower
      hIntegrable_w hw_meas
  -- Derive the condKernel-based a.e. bound from upstream condKernel_ae_bound
  set γ_spec := ymGibbsSpec G n d N plaq β hZcond_pos hw_meas
    hw_integrable_cond hmeas_condDist with hγ_spec_def
  have hD_spec : DobrushinCondition γ_spec :=
    ymDobrushinCondition G n d N β hβ plaq hd hn hβ_small
      hZcond_pos hw_meas hw_integrable_cond hmeas_condDist
      hInfluence hMaxNeighborsCol hMaxNeighborsRow
  haveI : IsProbabilityMeasure (ymMeasure G n d N β plaq) := hμ_prob
  have hμ_gibbs := ymMeasure_isGibbs G n d N plaq β hβ hTrace_upper hTrace_lower
      hIntegrable_w hw_meas hZcond_pos hw_integrable_cond hmeas_condDist
      hZcond_meas hinner_meas hindA_fub_int hinner_w_over_Z_int hμ_prob
  have hbound_q : ∀ U, |plaqObs G n d N q U| ≤ (↑n : ℝ) :=
    fun U => plaqObs_bounded G n d N q U (fun g => abs_le.mpr
      ⟨by linarith [hTrace_lower g], hTrace_upper g⟩)
  have hg_local : ∀ (σ τ : GaugeConnection G d N),
      (∀ w ∈ ((Finset.univ : Finset (Fin 4)).image (LatticePlaquette.boundaryLinks q)),
        σ w = τ w) → plaqObs G n d N q σ = plaqObs G n d N q τ := by
    intro σ τ hστ
    unfold plaqObs plaquetteHolonomy
    have h0 : σ (q.boundaryLinks 0) = τ (q.boundaryLinks 0) :=
      hστ _ (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
    have h1 : σ (q.boundaryLinks 1) = τ (q.boundaryLinks 1) :=
      hστ _ (Finset.mem_image.mpr ⟨1, Finset.mem_univ _, rfl⟩)
    have h2 : σ (q.boundaryLinks 2) = τ (q.boundaryLinks 2) :=
      hστ _ (Finset.mem_image.mpr ⟨2, Finset.mem_univ _, rfl⟩)
    have h3 : σ (q.boundaryLinks 3) = τ (q.boundaryLinks 3) :=
      hστ _ (Finset.mem_image.mpr ⟨3, Finset.mem_univ _, rfl⟩)
    simp only [h0, h1, h2, h3]
  have h_dep_F : ∀ (z : LatticeLink d N) (B : Set G), MeasurableSet B →
      ∀ (σ τ : GaugeConnection G d N),
        (∀ w ∈ (hfinsupp z).toFinset, σ w = τ w) →
        (γ_spec.condDist {z} σ ((· z) ⁻¹' B)).toReal =
        (γ_spec.condDist {z} τ ((· z) ⁻¹' B)).toReal :=
    fun z B hB σ τ hagree =>
      condDist_cylinder_eq_of_agree_on_support γ_spec z B hB (hfinsupp z) σ τ hagree
  have hcond_ae_bound : CondKernelAEBound
      (ymMeasure G n d N β plaq) hμ_prob
      (plaqObs G n d N q) (↑n : ℝ)
      ((Finset.univ : Finset (Fin 4)).image (LatticePlaquette.boundaryLinks p))
      ((Finset.univ : Finset (Fin 4)).image (LatticePlaquette.boundaryLinks q))
      γ_spec :=
    @CondKernelDLR.condKernel_ae_bound (LatticeLink d N) _ _ G _ _ _ _ _ _ _
      γ_spec hD_spec
      (ymMeasure G n d N β plaq) hμ_prob hμ_gibbs
      (plaqObs G n d N q) hPlaqObs_q_meas
      (↑n : ℝ) (Nat.cast_nonneg _) hbound_q
      ((Finset.univ : Finset (Fin 4)).image (LatticePlaquette.boundaryLinks p))
      ((Finset.univ : Finset (Fin 4)).image (LatticePlaquette.boundaryLinks q))
      hg_local hPlaqObs_q_int hfinsupp h_dep_F
  -- Apply the upstream theorem
  exact ym_mass_gap_2pt_via_multisite G n d N hd hn β hβ hβ_small
    hTrace_lower hTrace_upper plaq p q
    hZcond_pos hw_meas hw_integrable_cond hmeas_condDist
    hZcond_meas hinner_meas hindA_fub_int hinner_w_over_Z_int hIntegrable_w
    hPlaqObs_p_meas hPlaqObs_q_meas hPlaqObs_p_int hPlaqObs_q_int hPlaqObs_pq_int
    hPlaqObs_pw_int hPlaqObs_qw_int hPlaqObs_pqw_int
    hInfluence hMaxNeighborsCol hMaxNeighborsRow
    hμ_prob hcond_ae_bound
    dLink h_refl h_triangle h_support_inst hfinsupp
    (fun z B hB σ τ hagree =>
      condDist_cylinder_eq_of_agree_on_support γ_spec z B hB (hfinsupp z) σ τ hagree)

end

/-! ## U(n) measurable-space instances

Borel measurable space + `BorelSpace` for `Matrix.unitaryGroup (Fin n) ℂ`,
needed by the U(n) specialization in `ym_mass_gap_exponential_decay`
below. The remaining U(n) hypotheses (`CompactSpace`,
`SecondCountableTopology`, `HasHaarProbability`) are proved in
`UnitaryGroup.lean` but appear as explicit instance arguments due to
Lean instance-resolution limits across files. -/

noncomputable section UNMassGap

open Matrix MeasureTheory Real

/-- Borel measurable space on U(n). -/
instance instMeasurableSpaceUN (n : ℕ) :
    MeasurableSpace (unitaryGroup (Fin n) ℂ) :=
  borel (unitaryGroup (Fin n) ℂ)

/-- The measurable space on U(n) is the Borel sigma-algebra. -/
instance instBorelSpaceUN (n : ℕ) :
    BorelSpace (unitaryGroup (Fin n) ℂ) := ⟨rfl⟩

end UNMassGap

/-! ## Mass gap target

For a genuine mass gap statement we need exponential decay of the
connected 2-point function in a distance that grows with geometric
separation on the lattice — not the upstream Dobrushin-contraction
output, which only bounds `α^{dLink}` for whatever distance is fed
into `ym_mass_gap_strong_coupling`.

### Distance on the torus

The periodic L₁ distance on (ℤ/Nℤ)ᵈ: for each coordinate, the
distance is min(|x−y|, N−|x−y|) in ℤ/Nℤ, summed over coordinates. -/

/-- Periodic distance in one coordinate on ℤ/Nℤ. -/
noncomputable def ZMod.periodicDist (N : ℕ) [NeZero N] (a b : ZMod N) : ℕ :=
  min (ZMod.val (a - b)) (N - ZMod.val (a - b))

/-- L₁ distance on the periodic lattice (ℤ/Nℤ)ᵈ. -/
noncomputable def latticeSiteDist (d N : ℕ) [NeZero N]
    (x y : GaussianField.FinLatticeSites d N) : ℕ :=
  ∑ i : Fin d, ZMod.periodicDist N (x i) (y i)

/-- Distance between plaquettes: L₁ distance between anchor sites. -/
noncomputable def latticePlaquetteDist (d N : ℕ) [NeZero N]
    (p q : LatticePlaquette d N) : ℕ :=
  latticeSiteDist d N p.site q.site

section MassGapProper

open Matrix

/-- **Mass gap theorem (target).**

For U(n) Wilson lattice gauge theory on (ℤ/Nℤ)ᵈ at strong coupling,
the connected 2-point function decays exponentially in the periodic
L₁ plaquette distance:

    |⟨Re Tr(U_p) · Re Tr(U_q)⟩_c|
        ≤ 32 n² / (1 − α) · α^{latticePlaquetteDist p q}

where α = dobrushinAlpha(n, d, β) < 1.

**Status: open.** The proof route is laid out in
`docs/mass-gap-completion-plan.md`: instantiate
`ym_mass_gap_strong_coupling` with the ambient shared-plaquette
graph distance on links, then bound the 16-term boundary-link sum
geometrically using the boundary-layer incidence structure. The
exponent in the eventual proved statement may be slightly weaker
than `α^{latticePlaquetteDist}` — see the plan for the actual
form, e.g. `α^{(latticePlaquetteDist − 1) / 2}`. -/
theorem ym_mass_gap_exponential_decay
    (n : ℕ) (hn : 1 ≤ n)
    (d N : ℕ) (hd : 2 ≤ d) (hN : 2 < N) [NeZero N]
    [CompactSpace (unitaryGroup (Fin n) ℂ)]
    [SecondCountableTopology (unitaryGroup (Fin n) ℂ)]
    [HasHaarProbability (unitaryGroup (Fin n) ℂ)]
    [Fintype (LatticeLink d N)]
    [DecidableEq (LatticeLink d N)]
    (β : ℝ) (hβ : 0 ≤ β)
    (hβ_small : β < 1 / (4 * ↑n * ↑(maxNeighbors d)))
    (plaq : Finset (LatticePlaquette d N))
    (p q : LatticePlaquette d N) :
    |connected2pt (unitaryGroup (Fin n) ℂ) n d N β plaq
        (plaqObs (unitaryGroup (Fin n) ℂ) n d N p)
        (plaqObs (unitaryGroup (Fin n) ℂ) n d N q)| ≤
      32 * (↑n : ℝ) ^ 2 / (1 - dobrushinAlpha n d β) *
        (dobrushinAlpha n d β) ^ latticePlaquetteDist d N p q := by
  sorry

end MassGapProper

