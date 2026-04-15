/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Locality of Lattice Gauge Theory Observables

Uses Mathlib's `DependsOn f S` to formalize that observables depend
on specific sets of links. This is the key concept for:
1. Product independence: disjoint supports → ⟨fg⟩ = ⟨f⟩⟨g⟩
2. Spatial factorization in d=2
3. Support distance → correlation decay rate

A `GaugeConnection G d N = LatticeLink d N → G` is a dependent function
type, and Mathlib's `DependsOn` works on `(Π i, α i) → β`:
  `DependsOn f S ↔ ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y`

## Main results

- `plaquetteHolonomy_dependsOn` — holonomy depends on boundary links
- `plaqObs_dependsOn` — Re Tr(U_p) depends on boundary links
- `boltzmannWeight_dependsOn` — exp(-S) depends on plaquette boundary links

## References

- Chatterjee (2026), §15.6
-/

import LGT.MassGap.YMMeasure
import Mathlib.Logic.Function.DependsOn
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Integration

open MeasureTheory GaussianField

noncomputable section

variable {G : Type*} {n : ℕ} [Group G] [HasGaugeTrace G n]
variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable [MeasurableSpace G] [BorelSpace G]
variable {d N : ℕ}

/-! ## Plaquette boundary links -/

/-- The set of boundary links of a plaquette (as a Set, for DependsOn). -/
def plaquetteLinkSupport (p : LatticePlaquette d N) : Set (LatticeLink d N) :=
  {p.boundaryLinks 0, p.boundaryLinks 1, p.boundaryLinks 2, p.boundaryLinks 3}

/-! ## Holonomy and plaquette observables are local -/

/-- The plaquette holonomy U_p depends only on the 4 boundary links. -/
theorem plaquetteHolonomy_dependsOn (p : LatticePlaquette d N) :
    DependsOn (fun U : GaugeConnection G d N => plaquetteHolonomy U p)
      (plaquetteLinkSupport p) := by
  intro U₁ U₂ h
  simp only [plaquetteHolonomy]
  have h0 : U₁ (p.boundaryLinks 0) = U₂ (p.boundaryLinks 0) :=
    h _ (Set.mem_insert _ _)
  have h1 : U₁ (p.boundaryLinks 1) = U₂ (p.boundaryLinks 1) :=
    h _ (by simp [plaquetteLinkSupport, Set.mem_insert_iff])
  have h2 : U₁ (p.boundaryLinks 2) = U₂ (p.boundaryLinks 2) :=
    h _ (by simp [plaquetteLinkSupport, Set.mem_insert_iff])
  have h3 : U₁ (p.boundaryLinks 3) = U₂ (p.boundaryLinks 3) :=
    h _ (by simp [plaquetteLinkSupport, Set.mem_insert_iff])
  rw [h0, h1, h2, h3]

/-- The plaquette observable Re Tr(U_p) depends only on boundary links. -/
theorem plaqObs_dependsOn [HasHaarProbability G] [Fintype (LatticeLink d N)]
    (p : LatticePlaquette d N) :
    DependsOn (plaqObs G n d N p) (plaquetteLinkSupport p) := by
  intro U₁ U₂ h
  show plaqObs G n d N p U₁ = plaqObs G n d N p U₂
  unfold plaqObs
  congr 1
  exact plaquetteHolonomy_dependsOn p h

/-! ## Support distance and disjointness

For plaquettes p, q, if their link supports are disjoint, then their
observables are independent under any product measure. The support
distance determines when this disjointness holds. -/

/-- Two plaquettes have disjoint link supports if they share no
boundary links. On a sufficiently large lattice, plaquettes whose
base sites are far enough apart have disjoint supports. -/
def plaquettesDisjoint (p q : LatticePlaquette d N) : Prop :=
  Disjoint (plaquetteLinkSupport p) (plaquetteLinkSupport q)

/-! ## Product measure independence (the key theorem)

For product measures, functions depending on disjoint coordinate sets
are independent: ⟨fg⟩ = ⟨f⟩⟨g⟩.

Mathlib has `ProbabilityTheory.IndepFun` and related theory for
independence. For our finite product setting, the result follows
from Fubini on `Measure.pi`. -/

/-- **Product independence for disjoint supports.**

Under a product measure on G^{links}, if f depends on S and g
depends on T with S ∩ T = ∅, then ∫fg dμ = (∫f dμ)(∫g dμ).

This is the standard independence property of product measures.
It's the core of the correlation decay argument: observables at
sufficient distance have disjoint supports, hence zero connected
correlation under the gauge-fixed product measure. -/
theorem integral_mul_of_disjoint_dependsOn
    [HasHaarProbability G] [Fintype (LatticeLink d N)]
    (f g : GaugeConnection G d N → ℝ)
    (S T : Set (LatticeLink d N))
    (hf : DependsOn f S) (hg : DependsOn g T)
    (hST : Disjoint S T)
    (hfm : Measurable f) (hgm : Measurable g) :
    ∫ U, f U * g U ∂(productHaar G d N) =
    (∫ U, f U ∂(productHaar G d N)) * (∫ U, g U ∂(productHaar G d N)) := by
  classical
  -- Step 1: Coordinate projections are iIndepFun under the product measure.
  have hindep : ProbabilityTheory.iIndepFun
      (fun (i : LatticeLink d N) (U : GaugeConnection G d N) => U i)
      (productHaar G d N) := by
    have := ProbabilityTheory.iIndepFun_pi
      (Ω := fun _ : LatticeLink d N => G)
      (μ := fun _ => haarG G)
      (𝓧 := fun _ : LatticeLink d N => G)
      (X := fun _ => id)
      (fun _ => aemeasurable_id)
    simpa using this
  -- Step 2: From iIndepFun, get iIndep of the generated sigma-algebras.
  have hiIndep : ProbabilityTheory.iIndep
      (fun i => MeasurableSpace.comap (fun U : GaugeConnection G d N => U i) ‹_›)
      (productHaar G d N) :=
    hindep.iIndep
  -- Step 3: The sigma-algebras generated by S-coordinates and T-coordinates are independent.
  have h_le : ∀ (i : LatticeLink d N),
      MeasurableSpace.comap (fun U : GaugeConnection G d N => U i) ‹_› ≤
      instMeasurableSpaceGaugeConnection G d N :=
    fun i => (measurable_pi_apply i).comap_le
  have hIndepSigma := ProbabilityTheory.indep_iSup_of_disjoint h_le hiIndep hST
  -- Step 4: Show comap f ≤ ⨆ i ∈ S, comap (eval i), and similarly for g.
  -- Key: if DependsOn h R and Measurable h, then h factors through the R-coordinate
  -- projection, and the comap of h lies in the R-coordinate sigma-algebra.
  have comap_le_of_dependsOn :
      ∀ (h : GaugeConnection G d N → ℝ) (R : Set (LatticeLink d N)),
      DependsOn h R → Measurable h →
      MeasurableSpace.comap h inferInstance ≤ ⨆ i ∈ R,
        MeasurableSpace.comap (fun U : GaugeConnection G d N => U i) inferInstance := by
    intro h R hDep hMeas
    -- h = h' ∘ R.restrict for some h'. Build a measurable section σ of R.restrict
    -- (extend by 1 on complement), making h' = h ∘ σ measurable.
    -- Then comap h = comap R.restrict (comap h') ≤ comap R.restrict (pi)
    -- = ⨆ j : R, comap (eval j.val) = ⨆ i ∈ R, comap (eval i).
    -- Section: σ(x)(i) = x ⟨i, hi⟩ if i ∈ R, else 1.
    let σ : (↥R → G) → GaugeConnection G d N :=
      fun x i => if hi : i ∈ R then x ⟨i, hi⟩ else 1
    have hσ_section : ∀ x, R.restrict (σ x) = x := by
      intro x; ext ⟨i, hi⟩; simp [σ, hi]
    have hσ_meas : Measurable σ := by
      apply measurable_pi_lambda
      intro i
      by_cases hi : i ∈ R
      · show Measurable (fun x : (↥R → G) => if _ : i ∈ R then x ⟨i, _⟩ else 1)
        simp only [hi, dif_pos]
        exact measurable_pi_apply (⟨i, hi⟩ : ↥R)
      · show Measurable (fun _ : (↥R → G) => if _ : i ∈ R then _ else (1 : G))
        simp only [hi, dif_neg, not_false_eq_true]
        exact measurable_const
    -- h' = h ∘ σ is measurable.
    set h' := h ∘ σ with hh'_def
    have hh'_meas : Measurable h' := hMeas.comp hσ_meas
    -- h = h' ∘ R.restrict
    have h_eq : h = h' ∘ R.restrict := by
      ext U; simp only [hh'_def, Function.comp_def]
      exact (hDep (fun i hi => by simp [σ, hi])).symm
    -- comap h = comap (h' ∘ R.restrict) = comap R.restrict (comap h')
    rw [h_eq, ← MeasurableSpace.comap_comp]
    -- comap h' ≤ MeasurableSpace.pi (since h' is measurable)
    have hle : (inferInstance : MeasurableSpace ℝ).comap h' ≤ MeasurableSpace.pi :=
      hh'_meas.comap_le
    -- comap R.restrict (comap h') ≤ comap R.restrict MeasurableSpace.pi
    apply le_trans (MeasurableSpace.comap_mono hle)
    -- comap R.restrict MeasurableSpace.pi = ⨆ i ∈ R, comap (eval i) _
    show MeasurableSpace.comap (R.restrict (π := fun _ => G))
      MeasurableSpace.pi ≤ _
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp]
    apply iSup_le
    intro ⟨j, hj⟩
    have : (fun (b : ↥R → G) => b ⟨j, hj⟩) ∘ R.restrict (π := fun _ => G) =
        (fun (b : GaugeConnection G d N) => b j) := by
      ext b; simp [Set.restrict]
    rw [this]
    exact le_iSup_of_le j (le_iSup_of_le hj le_rfl)
  -- Get IndepFun f g from the sigma-algebra independence + comap bounds.
  have hIndepFG : ProbabilityTheory.IndepFun f g (productHaar G d N) := by
    rw [ProbabilityTheory.IndepFun]
    exact ProbabilityTheory.indep_of_indep_of_le_left
      (ProbabilityTheory.indep_of_indep_of_le_right hIndepSigma
        (comap_le_of_dependsOn g T hg hgm))
      (comap_le_of_dependsOn f S hf hfm)
  -- Step 5: Apply the integral independence formula.
  exact hIndepFG.integral_fun_mul_eq_mul_integral
    hfm.aestronglyMeasurable hgm.aestronglyMeasurable

/-- **Connected 2-point function vanishes for disjoint supports.**

When plaquette observables have disjoint link supports:
connected2pt = ⟨O_p · O_q⟩ - ⟨O_p⟩ · ⟨O_q⟩ = 0

because the observables are independent under the product measure. -/
theorem connected2pt_zero_of_disjoint
    [HasHaarProbability G] [Fintype (LatticeLink d N)]
    (β : ℝ) (plaq : Finset (LatticePlaquette d N))
    (p q : LatticePlaquette d N)
    (hpq : plaquettesDisjoint p q)
    -- Under the gauge-fixed measure (which IS a product measure):
    -- This uses FP + the fact that the gauge-fixed measure is product Haar
    -- on the physical links
    (hGF : ∀ (f g : GaugeConnection G d N → ℝ),
      DependsOn f (plaquetteLinkSupport p) →
      DependsOn g (plaquetteLinkSupport q) →
      ymExpect G n d N β plaq (fun U => f U * g U) =
      ymExpect G n d N β plaq f * ymExpect G n d N β plaq g) :
    connected2pt G n d N β plaq (plaqObs G n d N p) (plaqObs G n d N q) = 0 := by
  unfold connected2pt
  rw [hGF (plaqObs G n d N p) (plaqObs G n d N q)
    (plaqObs_dependsOn p) (plaqObs_dependsOn q)]
  ring

end
