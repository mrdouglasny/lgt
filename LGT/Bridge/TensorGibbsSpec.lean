/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tensor Network to Gibbs Specification Bridge

Defines a `GibbsSpec` instance from a nearest-neighbor Boltzmann weight
on a finite lattice with a finite spin space. This bridges the EKR tensor
RG framework to the Dobrushin mass gap machinery.

## Setup

- **Sites**: `I` — a finite type with a neighbor relation `adj`
- **Spin space**: `S` — a finite type
- **Nearest-neighbor weight**: `w : S → S → ℝ` with `w > 0` and `w` symmetric
- **Boltzmann weight**: `∏_{⟨i,j⟩ touching Λ} w(σ_i, σ_j)`

The Gibbs conditional at region Λ given boundary σ is the normalized
finite sum of Dirac masses at configurations agreeing with σ outside Λ,
weighted by the Boltzmann factor.

## Main definitions

- `NNBoltzmannWeight S` — nearest-neighbor Boltzmann weight structure
- `tensorGibbsSpec` — the `GibbsSpec` instance

## References

- Chatterjee, *Gauge Theory Lecture Notes* (2026), §16
- markov-semigroups/Dobrushin/Specification.lean
-/

import MarkovSemigroups.Dobrushin.Specification
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Data.Fintype.Pi

open MeasureTheory Measure Finset

noncomputable section

/-! ## Nearest-neighbor Boltzmann weight -/

/-- A nearest-neighbor Boltzmann weight on spin space `S`.
Encodes the local interaction `w(s, s') > 0` between adjacent spins.
Examples: Ising `w(s,s') = exp(β s s')`, Potts `w(s,s') = exp(β δ_{s,s'})`. -/
structure NNBoltzmannWeight (S : Type*) where
  /-- The weight function for a pair of adjacent spins. -/
  w : S → S → ℝ
  /-- All weights are strictly positive. -/
  w_pos : ∀ s s', 0 < w s s'
  /-- The weight is symmetric (undirected interaction). -/
  w_symm : ∀ s s', w s s' = w s' s

namespace TensorGibbs

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {S : Type*} [Fintype S] [DecidableEq S]
  [MeasurableSpace S] [MeasurableSingletonClass S]
variable (adj : I → I → Prop) [DecidableRel adj]

/-! ## Glued configurations -/

/-- Glue: replace the values of `σ` on `Λ` with those of `τ`, keeping `σ` outside. -/
def gluedConfig (Λ : Finset I) (τ σ : I → S) : I → S :=
  fun i => if i ∈ Λ then τ i else σ i

omit [Fintype I] [Fintype S] [DecidableEq S] [MeasurableSpace S]
  [MeasurableSingletonClass S] [DecidableRel adj] in
@[simp]
theorem gluedConfig_outside (Λ : Finset I) (τ σ : I → S)
    (i : I) (hi : i ∉ Λ) : gluedConfig Λ τ σ i = σ i :=
  if_neg hi

omit [Fintype I] [Fintype S] [DecidableEq S] [MeasurableSpace S]
  [MeasurableSingletonClass S] [DecidableRel adj] in
@[simp]
theorem gluedConfig_inside (Λ : Finset I) (τ σ : I → S)
    (i : I) (hi : i ∈ Λ) : gluedConfig Λ τ σ i = τ i :=
  if_pos hi

omit [Fintype I] [Fintype S] [DecidableEq S] [MeasurableSpace S]
  [MeasurableSingletonClass S] [DecidableRel adj] in
theorem gluedConfig_self (Λ : Finset I) (σ : I → S) :
    gluedConfig Λ σ σ = σ := by
  ext i; simp [gluedConfig]

omit [Fintype I] [Fintype S] [DecidableEq S] [MeasurableSpace S]
  [MeasurableSingletonClass S] [DecidableRel adj] in
/-- A config that already agrees with σ outside Λ is its own gluing. -/
theorem gluedConfig_of_agree (Λ : Finset I) (τ σ : I → S)
    (h : ∀ i, i ∉ Λ → τ i = σ i) : gluedConfig Λ τ σ = τ := by
  ext i; by_cases hi : i ∈ Λ <;> simp [gluedConfig, hi, h i]

/-! ## Conditional weight and partition function -/

/-- The set of ordered adjacent pairs in `I × I`. -/
def adjPairs : Finset (I × I) :=
  Finset.univ.filter (fun p => adj p.1 p.2)

/-- Adjacent pairs touching Λ: at least one endpoint is in Λ. -/
def adjPairsTouching (Λ : Finset I) : Finset (I × I) :=
  (adjPairs adj).filter (fun p => p.1 ∈ Λ ∨ p.2 ∈ Λ)

/-- The conditional Boltzmann weight: product of `w` over edges touching Λ.
This is the factor in the Gibbs conditional that depends on the Λ-configuration. -/
def condWeight (W : NNBoltzmannWeight S) (Λ : Finset I) (σ : I → S) : ℝ :=
  ∏ p ∈ adjPairsTouching adj Λ, W.w (σ p.1) (σ p.2)

omit [Fintype S] [DecidableEq S] [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem condWeight_pos (W : NNBoltzmannWeight S) (Λ : Finset I) (σ : I → S) :
    0 < condWeight adj W Λ σ :=
  Finset.prod_pos (fun p _ => W.w_pos (σ p.1) (σ p.2))

/-- The set of configurations agreeing with σ outside Λ. -/
def agreeing (Λ : Finset I) (σ : I → S) : Finset (I → S) :=
  Finset.univ.filter (fun τ => ∀ i, i ∉ Λ → τ i = σ i)

omit [MeasurableSpace S] [MeasurableSingletonClass S] [DecidableRel adj] in
theorem mem_agreeing (Λ : Finset I) (σ τ : I → S) :
    τ ∈ agreeing Λ σ ↔ ∀ i, i ∉ Λ → τ i = σ i := by
  simp [agreeing]

omit [MeasurableSpace S] [MeasurableSingletonClass S] [DecidableRel adj] in
theorem self_mem_agreeing (Λ : Finset I) (σ : I → S) :
    σ ∈ agreeing Λ σ := by
  rw [mem_agreeing]; intro _ _; rfl

omit [MeasurableSpace S] [MeasurableSingletonClass S] [DecidableRel adj] in
theorem agreeing_nonempty (Λ : Finset I) (σ : I → S) :
    (agreeing Λ σ).Nonempty :=
  ⟨σ, self_mem_agreeing Λ σ⟩

/-- The conditional partition function: sum of conditional weights
over all configurations agreeing with σ outside Λ. -/
def condZ (W : NNBoltzmannWeight S) (Λ : Finset I) (σ : I → S) : ℝ :=
  ∑ τ ∈ agreeing Λ σ, condWeight adj W Λ τ

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
theorem condZ_pos (W : NNBoltzmannWeight S) (Λ : Finset I) (σ : I → S) :
    0 < condZ adj W Λ σ :=
  Finset.sum_pos (fun τ _ => condWeight_pos adj W Λ τ) (agreeing_nonempty Λ σ)

/-! ## Key lemma: agreeing and weights depend only on σ outside Λ -/

omit [MeasurableSpace S] [MeasurableSingletonClass S] [DecidableRel adj] in
/-- If σ₁ and σ₂ agree outside Λ, they have the same agreeing set. -/
theorem agreeing_eq_of_agree (Λ : Finset I) (σ₁ σ₂ : I → S)
    (h : ∀ i, i ∉ Λ → σ₁ i = σ₂ i) :
    agreeing Λ σ₁ = agreeing Λ σ₂ := by
  ext τ
  simp only [mem_agreeing]
  constructor
  · intro hτ i hi; rw [← h i hi, hτ i hi]
  · intro hτ i hi; rw [h i hi, hτ i hi]

omit [MeasurableSpace S] [MeasurableSingletonClass S] in
/-- The conditional partition function depends only on σ outside Λ. -/
theorem condZ_eq_of_agree (W : NNBoltzmannWeight S) (Λ : Finset I)
    (σ₁ σ₂ : I → S) (h : ∀ i, i ∉ Λ → σ₁ i = σ₂ i) :
    condZ adj W Λ σ₁ = condZ adj W Λ σ₂ := by
  unfold condZ
  rw [agreeing_eq_of_agree Λ σ₁ σ₂ h]

/-! ## The conditional probability measure

For region Λ and boundary σ, the conditional measure is a normalized
weighted sum of Dirac masses over all configurations agreeing with σ
outside Λ. -/

/-- The unnormalized conditional measure: weighted sum of Dirac masses. -/
def condMeasureUnnorm (W : NNBoltzmannWeight S) (Λ : Finset I) (σ : I → S) :
    Measure (I → S) :=
  ∑ τ ∈ agreeing Λ σ,
    ENNReal.ofReal (condWeight adj W Λ τ) • Measure.dirac τ

/-- The normalized conditional measure. -/
def condMeasure (W : NNBoltzmannWeight S) (Λ : Finset I) (σ : I → S) :
    Measure (I → S) :=
  ENNReal.ofReal (1 / condZ adj W Λ σ) • condMeasureUnnorm adj W Λ σ

/-! ## Total mass computation -/

omit [MeasurableSingletonClass S] in
/-- Evaluate the unnormalized conditional measure on a set. -/
theorem condMeasureUnnorm_apply (W : NNBoltzmannWeight S)
    (Λ : Finset I) (σ : I → S) (A : Set (I → S)) :
    condMeasureUnnorm adj W Λ σ A =
      ∑ τ ∈ agreeing Λ σ,
        ENNReal.ofReal (condWeight adj W Λ τ) * Measure.dirac τ A := by
  unfold condMeasureUnnorm
  rw [Measure.finset_sum_apply _ _ A]
  simp only [Measure.smul_apply, smul_eq_mul]

omit [MeasurableSingletonClass S] in
/-- The total mass of the unnormalized measure equals Z (as ENNReal). -/
theorem condMeasureUnnorm_univ (W : NNBoltzmannWeight S)
    (Λ : Finset I) (σ : I → S) :
    condMeasureUnnorm adj W Λ σ Set.univ =
      ENNReal.ofReal (condZ adj W Λ σ) := by
  rw [condMeasureUnnorm_apply]
  simp only [Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ,
    Pi.one_apply, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg
    (fun τ _ => le_of_lt (condWeight_pos adj W Λ τ))]
  rfl

omit [MeasurableSingletonClass S] in
/-- The normalized measure has total mass 1. -/
theorem condMeasure_univ (W : NNBoltzmannWeight S)
    (Λ : Finset I) (σ : I → S) :
    condMeasure adj W Λ σ Set.univ = 1 := by
  unfold condMeasure
  rw [Measure.smul_apply, smul_eq_mul, condMeasureUnnorm_univ]
  rw [← ENNReal.ofReal_mul (one_div_nonneg.mpr (le_of_lt (condZ_pos adj W Λ σ)))]
  rw [one_div_mul_cancel (ne_of_gt (condZ_pos adj W Λ σ))]
  exact ENNReal.ofReal_one

omit [MeasurableSingletonClass S] in
/-- The condMeasure is a probability measure. -/
theorem condMeasure_isProbabilityMeasure (W : NNBoltzmannWeight S)
    (Λ : Finset I) (σ : I → S) :
    IsProbabilityMeasure (condMeasure adj W Λ σ) :=
  ⟨condMeasure_univ adj W Λ σ⟩

/-! ## Properness: condMeasure concentrates on configs agreeing with σ outside Λ -/

omit [Fintype S] [DecidableEq S] in
/-- The "agrees outside Λ" set is measurable. -/
theorem measurableSet_agreesOutside (Λ : Finset I) (σ : I → S) :
    MeasurableSet {τ : I → S | ∀ i, i ∉ Λ → τ i = σ i} := by
  have hset : {τ : I → S | ∀ i, i ∉ Λ → τ i = σ i} =
      ⋂ i ∈ (Finset.univ \ Λ : Finset I),
        (fun τ : I → S => τ i) ⁻¹' {σ i} := by
    ext τ
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_sdiff,
      Finset.mem_univ, true_and, Set.mem_preimage, Set.mem_singleton_iff]
  rw [hset]
  exact MeasurableSet.biInter (Finset.univ \ Λ).countable_toSet
    (fun i _ => (measurable_pi_apply i) (measurableSet_singleton (σ i)))

omit [MeasurableSingletonClass S] in
/-- Each Dirac mass at τ ∈ agreeing Λ σ gives full mass to the agreeing set. -/
theorem dirac_agreeing_support (Λ : Finset I) (σ τ : I → S)
    (hτ : τ ∈ agreeing Λ σ) :
    Measure.dirac τ {ρ : I → S | ∀ i, i ∉ Λ → ρ i = σ i} = 1 :=
  Measure.dirac_apply_of_mem ((mem_agreeing Λ σ τ).mp hτ)

omit [MeasurableSingletonClass S] in
/-- The unnormalized measure gives the same mass to the agreeing set
as to the full space. -/
theorem condMeasureUnnorm_agreeing (W : NNBoltzmannWeight S)
    (Λ : Finset I) (σ : I → S) :
    condMeasureUnnorm adj W Λ σ {τ | ∀ i, i ∉ Λ → τ i = σ i} =
      condMeasureUnnorm adj W Λ σ Set.univ := by
  rw [condMeasureUnnorm_apply, condMeasureUnnorm_apply]
  apply Finset.sum_congr rfl
  intro τ hτ
  rw [dirac_agreeing_support Λ σ τ hτ, Measure.dirac_apply_of_mem (Set.mem_univ τ)]

omit [MeasurableSingletonClass S] in
/-- condMeasure gives full mass to configs agreeing with σ outside Λ. -/
theorem condMeasure_proper (W : NNBoltzmannWeight S)
    (Λ : Finset I) (σ : I → S) :
    condMeasure adj W Λ σ {τ | ∀ i, i ∉ Λ → τ i = σ i} = 1 := by
  unfold condMeasure
  rw [Measure.smul_apply, smul_eq_mul, condMeasureUnnorm_agreeing,
    condMeasureUnnorm_univ]
  rw [← ENNReal.ofReal_mul (one_div_nonneg.mpr (le_of_lt (condZ_pos adj W Λ σ)))]
  rw [one_div_mul_cancel (ne_of_gt (condZ_pos adj W Λ σ))]
  exact ENNReal.ofReal_one

/-! ## Consistency: condMeasure depends only on σ outside Λ -/

omit [MeasurableSingletonClass S] in
theorem condMeasure_consistent (W : NNBoltzmannWeight S)
    (Λ : Finset I) (σ₁ σ₂ : I → S)
    (h : ∀ i, i ∉ Λ → σ₁ i = σ₂ i) :
    condMeasure adj W Λ σ₁ = condMeasure adj W Λ σ₂ := by
  unfold condMeasure condMeasureUnnorm
  rw [condZ_eq_of_agree adj W Λ σ₁ σ₂ h,
    agreeing_eq_of_agree Λ σ₁ σ₂ h]

/-! ## Measurability of σ ↦ condMeasure Λ σ A

For `[Fintype I]` and `[Fintype S]`, the configuration space `I → S` is
finite. Every function from a finite type to a measurable space with
measurable singletons is measurable. -/

/-- σ ↦ condMeasure(Λ, σ)(A).toReal is measurable. -/
theorem measurable_condMeasure_apply (W : NNBoltzmannWeight S)
    (Λ : Finset I) (A : Set (I → S)) (_hA : MeasurableSet A) :
    Measurable (fun σ : I → S => (condMeasure adj W Λ σ A).toReal) :=
  measurable_of_finite _

/-! ## The Gibbs specification -/

/-- **The tensor network Gibbs specification.**

Given a finite site type `I` with neighbor relation `adj`,
a finite spin space `S`, and a nearest-neighbor Boltzmann weight `W`,
this produces a `GibbsSpec I S` whose conditional distribution at
region Λ with boundary σ is the normalized Boltzmann measure:

  `condDist Λ σ = (1/Z_Λ(σ)) ∑_{τ agreeing} w(τ) · δ_τ`

All axioms (normalization, consistency, properness, measurability)
are verified without sorry. -/
def tensorGibbsSpec (W : NNBoltzmannWeight S) : GibbsSpec I S where
  condDist := fun Λ σ => condMeasure adj W Λ σ
  isProb := fun Λ σ => condMeasure_isProbabilityMeasure adj W Λ σ
  consistent := fun Λ σ₁ σ₂ h => condMeasure_consistent adj W Λ σ₁ σ₂ h
  proper := fun Λ σ => condMeasure_proper adj W Λ σ
  measurable_condDist := fun Λ A hA => measurable_condMeasure_apply adj W Λ A hA

end TensorGibbs

end
