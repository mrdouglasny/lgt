/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dobrushin Condition for the Tensor Gibbs Specification

Proves that `tensorGibbsSpec adj W` satisfies Dobrushin's uniqueness
condition when the Boltzmann weight `W` has small oscillation
(high-temperature / weak-coupling regime).

## Main results

- `weightOscillation` -- max log-ratio of the weight
- `influenceBoundTensor` -- `1 - exp(-4 * weightOscillation W)`
- `tensorGibbsSpec_influence_le` -- influence coefficient bound
- `tensorGibbsSpec_dobrushin_condition` -- Dobrushin condition

## References

- Chatterjee (2026), S16.2-16.3
- Dobrushin (1968), Uniqueness condition
-/

import LGT.Bridge.TensorGibbsSpec
import MarkovSemigroups.Dobrushin.Specification
import MarkovSemigroups.Dobrushin.Uniqueness

open MeasureTheory Measure Finset Real

noncomputable section

namespace TensorGibbs

variable {I : Type*} [Fintype I] [DecidableEq I]
variable {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
  [MeasurableSpace S] [MeasurableSingletonClass S]
variable (adj : I → I → Prop) [DecidableRel adj]

/-! ## Weight oscillation -/

/-- Maximum log-ratio of `w` when one argument changes. -/
def weightOscillation (W : NNBoltzmannWeight S) : ℝ :=
  ⨆ (s₁ : S), ⨆ (s₂ : S), ⨆ (s₃ : S),
    |Real.log (W.w s₁ s₃ / W.w s₂ s₃)|

/-- Influence bound: `1 - exp(-4D)` where `D = weightOscillation W`. -/
def influenceBoundTensor (W : NNBoltzmannWeight S) : ℝ :=
  1 - Real.exp (-4 * weightOscillation W)

/-! ## Oscillation properties -/

theorem log_ratio_le_oscillation (W : NNBoltzmannWeight S)
    (s₁ s₂ s₃ : S) :
    |Real.log (W.w s₁ s₃ / W.w s₂ s₃)| ≤ weightOscillation W := by
  apply le_ciSup_of_le (Finite.bddAbove_range _) s₁
  apply le_ciSup_of_le (Finite.bddAbove_range _) s₂
  exact le_ciSup_of_le (Finite.bddAbove_range _) s₃ le_rfl

theorem weightOscillation_nonneg (W : NNBoltzmannWeight S) :
    0 ≤ weightOscillation W :=
  le_trans (abs_nonneg _) (log_ratio_le_oscillation W
    (Classical.arbitrary S) (Classical.arbitrary S) (Classical.arbitrary S))

theorem influenceBoundTensor_nonneg (W : NNBoltzmannWeight S) :
    0 ≤ influenceBoundTensor W := by
  unfold influenceBoundTensor
  linarith [exp_le_one_iff.mpr (by linarith [weightOscillation_nonneg W] :
    -4 * weightOscillation W ≤ 0)]

theorem influenceBoundTensor_lt_one (W : NNBoltzmannWeight S) :
    influenceBoundTensor W < 1 := by
  unfold influenceBoundTensor; linarith [exp_pos (-4 * weightOscillation W)]

/-! ## Cylinder ratio bound

The key technical result: for sigma, tau differing only at y (y != x),
the x-cylinder probabilities under `condMeasure adj W {x}` satisfy
  P_tau(B) <= exp(4D) * P_sigma(B)
for all measurable B in S.

This follows from:
1. condWeight ratio per spin value: exp(-2D) <= CW(tau,s)/CW(sigma,s) <= exp(2D)
2. Numerator sum ratio: num_tau <= exp(2D) * num_sigma
3. Denominator ratio: Z_sigma <= exp(2D) * Z_tau
4. Combined: P_tau(B) / P_sigma(B) <= exp(2D) * exp(2D) = exp(4D)

The proof requires ENNReal arithmetic on the finite condMeasure.
We accept this as a bridge hypothesis and verify it for specific models. -/

/-- The cylinder ratio bound for the tensor Gibbs spec.
This is the key physics input encoding the Boltzmann weight oscillation bound.
The proof converts between ENNReal condMeasure and real arithmetic
on the finite condWeight sums. -/

-- Helper: per-factor weight ratio bound from oscillation.
-- For any s₁, s₂, t : S, W.w s₁ t ≤ exp(D) * W.w s₂ t.
private theorem weight_le_exp_osc_mul (W : NNBoltzmannWeight S) (s₁ s₂ t : S) :
    W.w s₁ t ≤ Real.exp (weightOscillation W) * W.w s₂ t := by
  have hw_pos := W.w_pos s₂ t
  rw [← div_le_iff₀ hw_pos]
  have hlog : Real.log (W.w s₁ t / W.w s₂ t) ≤ weightOscillation W :=
    le_trans (le_abs_self _) (log_ratio_le_oscillation W s₁ s₂ t)
  have hdiv_pos : 0 < W.w s₁ t / W.w s₂ t := div_pos (W.w_pos s₁ t) hw_pos
  calc W.w s₁ t / W.w s₂ t
      = Real.exp (Real.log (W.w s₁ t / W.w s₂ t)) := (Real.exp_log hdiv_pos).symm
    _ ≤ Real.exp (weightOscillation W) := Real.exp_le_exp.mpr hlog

-- Helper: y ∉ {x} when x ≠ y.
private theorem not_mem_singleton_of_ne {α : Type*} [DecidableEq α] {x y : α}
    (h : x ≠ y) : y ∉ ({x} : Finset α) := by
  simp [h.symm]

-- Helper: pointwise condWeight bound.
-- When ρ ∈ agreeing {x} τ and φ(ρ) = update ρ y (σ y),
-- condWeight {x} ρ ≤ exp(2D) * condWeight {x} φ(ρ).
private theorem condWeight_update_le (W : NNBoltzmannWeight S)
    (x y : I) (hxy : x ≠ y) (σ τ : I → S) (_hdiff : ∀ z, z ≠ y → σ z = τ z)
    (ρ : I → S) (hρ : ρ ∈ TensorGibbs.agreeing ({x} : Finset I) τ) :
    TensorGibbs.condWeight adj W {x} ρ ≤
      Real.exp (2 * weightOscillation W) *
        TensorGibbs.condWeight adj W {x} (Function.update ρ y (σ y)) := by
  set D := weightOscillation W
  set φρ := Function.update ρ y (σ y)
  -- ρ agrees with τ outside {x}, so ρ z = τ z for z ≠ x. In particular ρ y = τ y.
  have hρy : ρ y = τ y :=
    (TensorGibbs.mem_agreeing ({x} : Finset I) τ ρ).mp hρ y
      (not_mem_singleton_of_ne hxy)
  -- Split adjPairsTouching into edges involving y and edges not involving y.
  unfold TensorGibbs.condWeight
  set edges := TensorGibbs.adjPairsTouching adj ({x} : Finset I)
  set ey := edges.filter (fun p => p.1 = y ∨ p.2 = y)
  set en := edges.filter (fun p => p.1 ≠ y ∧ p.2 ≠ y)
  -- Split the product
  have hdisj : Disjoint ey en := by
    apply Finset.disjoint_filter.mpr
    intro ⟨a, b⟩ _; simp; tauto
  have hunion : ey ∪ en = edges := by
    ext ⟨a, b⟩; simp [ey, en, Finset.mem_filter]; tauto
  rw [← hunion, Finset.prod_union hdisj, Finset.prod_union hdisj]
  -- For en: factors are equal since update doesn't change a ≠ y, b ≠ y
  have hen_eq : ∀ p ∈ en, W.w (ρ p.1) (ρ p.2) = W.w (φρ p.1) (φρ p.2) := by
    intro ⟨a, b⟩ hp
    simp only [en, Finset.mem_filter] at hp
    rw [show φρ a = ρ a from Function.update_of_ne hp.2.1 ..,
        show φρ b = ρ b from Function.update_of_ne hp.2.2 ..]
  rw [Finset.prod_congr rfl hen_eq]
  -- Need: ∏ ey, W.w (ρ ..) ≤ exp(2D) * ∏ ey, W.w (φρ ..)
  suffices h : ∏ p ∈ ey, W.w (ρ p.1) (ρ p.2) ≤
      Real.exp (2 * D) * ∏ p ∈ ey, W.w (φρ p.1) (φρ p.2) by
    have hc := Finset.prod_nonneg (fun p (_ : p ∈ en) =>
      le_of_lt (W.w_pos (φρ p.1) (φρ p.2)))
    calc (∏ p ∈ ey, W.w (ρ p.1) (ρ p.2)) * (∏ p ∈ en, W.w (φρ p.1) (φρ p.2))
        ≤ (Real.exp (2 * D) * ∏ p ∈ ey, W.w (φρ p.1) (φρ p.2)) *
          (∏ p ∈ en, W.w (φρ p.1) (φρ p.2)) :=
        mul_le_mul_of_nonneg_right h hc
      _ = Real.exp (2 * D) * ((∏ p ∈ ey, W.w (φρ p.1) (φρ p.2)) *
          (∏ p ∈ en, W.w (φρ p.1) (φρ p.2))) := by ring
  -- The edges in ey that touch {x} and involve y must be (x,y) or (y,x).
  have hey_sub : ∀ p ∈ ey, (p.1 = x ∧ p.2 = y) ∨ (p.1 = y ∧ p.2 = x) := by
    intro ⟨a, b⟩ hp
    simp only [ey, edges, TensorGibbs.adjPairsTouching, TensorGibbs.adjPairs,
      Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨⟨_, ha_or_hb⟩, hay_or_hby⟩ := hp
    rcases hay_or_hby with rfl | rfl
    · -- a = y, so b = x (from touching {x})
      rcases ha_or_hb with h | h
      · exact absurd (Finset.mem_singleton.mp h) (Ne.symm hxy)
      · exact Or.inr ⟨rfl, Finset.mem_singleton.mp h⟩
    · -- b = y, so a = x
      rcases ha_or_hb with h | h
      · exact Or.inl ⟨Finset.mem_singleton.mp h, rfl⟩
      · exact absurd (Finset.mem_singleton.mp h) (Ne.symm hxy)
  -- Bound each factor in ey using oscillation
  have hfactor_bound : ∀ p ∈ ey,
      W.w (ρ p.1) (ρ p.2) ≤ Real.exp D * W.w (φρ p.1) (φρ p.2) := by
    intro p hp
    rcases hey_sub p hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · -- p = (x, y)
      simp only [h1, h2]
      rw [show φρ x = ρ x from Function.update_of_ne hxy ..,
          show φρ y = σ y from Function.update_self .., hρy]
      rw [W.w_symm (ρ x) (τ y), W.w_symm (ρ x) (σ y)]
      exact weight_le_exp_osc_mul W (τ y) (σ y) (ρ x)
    · -- p = (y, x)
      simp only [h1, h2]
      rw [show φρ y = σ y from Function.update_self ..,
          show φρ x = ρ x from Function.update_of_ne hxy .., hρy]
      exact weight_le_exp_osc_mul W (τ y) (σ y) (ρ x)
  -- Bound the product: each factor ≤ exp(D) * ..., so product ≤ exp(D)^|ey| * ...
  -- and |ey| ≤ 2 since ey ⊆ {(x,y), (y,x)}.
  have hey_card : ey.card ≤ 2 := by
    have hsub : ey ⊆ ({(x, y), (y, x)} : Finset (I × I)) := by
      intro p hp
      rcases hey_sub p hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp [Prod.ext_iff, h1, h2]
      · simp [Prod.ext_iff, h1, h2]
    calc ey.card ≤ ({(x, y), (y, x)} : Finset (I × I)).card :=
          Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  calc ∏ p ∈ ey, W.w (ρ p.1) (ρ p.2)
      ≤ ∏ p ∈ ey, (Real.exp D * W.w (φρ p.1) (φρ p.2)) :=
        Finset.prod_le_prod
          (fun p _ => le_of_lt (W.w_pos (ρ p.1) (ρ p.2)))
          hfactor_bound
    _ = (Real.exp D) ^ ey.card * ∏ p ∈ ey, W.w (φρ p.1) (φρ p.2) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
    _ ≤ (Real.exp D) ^ 2 * ∏ p ∈ ey, W.w (φρ p.1) (φρ p.2) := by
        apply mul_le_mul_of_nonneg_right _ (Finset.prod_nonneg
          (fun p _ => le_of_lt (W.w_pos (φρ p.1) (φρ p.2))))
        exact pow_le_pow_right₀ (Real.one_le_exp (weightOscillation_nonneg W)) hey_card
    _ = Real.exp (2 * D) * ∏ p ∈ ey, W.w (φρ p.1) (φρ p.2) := by
        congr 1; rw [sq, ← Real.exp_add]; ring_nf

-- Helper: convert condMeasure applied to a measurable set into a real expression.
open Classical in
private theorem condMeasure_toReal_eq (W : NNBoltzmannWeight S) [Nonempty S]
    (Λ : Finset I) (σ : I → S) (A : Set (I → S)) (hA : MeasurableSet A) :
    (TensorGibbs.condMeasure adj W Λ σ A).toReal =
      (∑ ρ ∈ TensorGibbs.agreeing Λ σ,
        if ρ ∈ A then TensorGibbs.condWeight adj W Λ ρ else 0) /
      TensorGibbs.condZ adj W Λ σ := by
  unfold TensorGibbs.condMeasure
  rw [Measure.smul_apply, smul_eq_mul, TensorGibbs.condMeasureUnnorm_apply]
  have hdirac : ∀ τ : I → S,
      Measure.dirac τ A = if τ ∈ A then 1 else 0 := by
    intro τ
    rw [Measure.dirac_apply' τ hA, Set.indicator_apply, Pi.one_apply]
  simp_rw [hdirac, mul_ite, mul_one, mul_zero]
  have hZ_pos := TensorGibbs.condZ_pos adj W Λ σ
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (one_div_nonneg.mpr (le_of_lt hZ_pos))]
  rw [ENNReal.toReal_sum (fun ρ _ => by
    split_ifs
    · exact ENNReal.ofReal_ne_top
    · exact ENNReal.zero_ne_top)]
  simp_rw [apply_ite ENNReal.toReal, ENNReal.toReal_ofReal
    (le_of_lt (TensorGibbs.condWeight_pos adj W Λ _)), ENNReal.toReal_zero]
  rw [one_div, inv_mul_eq_div]

-- Helper: ratio bound for normalized measures (real-valued version).
private theorem ratio_bound_of_sum_bounds
    (num_σ num_τ Z_σ Z_τ C₁ C₂ : ℝ)
    (hnum_σ : 0 ≤ num_σ) (_hnum_τ : 0 ≤ num_τ)
    (hZσ : 0 < Z_σ) (hZτ : 0 < Z_τ)
    (hC₁ : 0 ≤ C₁) (_hC₂ : 0 ≤ C₂)
    (h_num : num_τ ≤ C₁ * num_σ) (h_Z : Z_σ ≤ C₂ * Z_τ) :
    num_τ / Z_τ ≤ C₁ * C₂ * (num_σ / Z_σ) := by
  rw [div_le_iff₀ hZτ]
  calc num_τ ≤ C₁ * num_σ := h_num
    _ = C₁ * (num_σ / Z_σ * Z_σ) := by rw [div_mul_cancel₀ num_σ (ne_of_gt hZσ)]
    _ ≤ C₁ * (num_σ / Z_σ * (C₂ * Z_τ)) := by
        apply mul_le_mul_of_nonneg_left _ hC₁
        exact mul_le_mul_of_nonneg_left h_Z (div_nonneg hnum_σ (le_of_lt hZσ))
    _ = C₁ * C₂ * (num_σ / Z_σ) * Z_τ := by ring

open Classical in
theorem cylinder_ratio_bound
    (W : NNBoltzmannWeight S) (x y : I) (hxy : x ≠ y)
    (σ τ : I → S) (hdiff : ∀ z, z ≠ y → σ z = τ z)
    (B : Set S) (hB : MeasurableSet B) :
    ((tensorGibbsSpec adj W).condDist {x} τ ((fun ρ : I → S => ρ x) ⁻¹' B)).toReal ≤
      Real.exp (4 * weightOscillation W) *
        ((tensorGibbsSpec adj W).condDist {x} σ
          ((fun ρ : I → S => ρ x) ⁻¹' B)).toReal := by
  set D := weightOscillation W
  set A := (fun ρ : I → S => ρ x) ⁻¹' B
  have hA : MeasurableSet A := measurableSet_preimage (measurable_pi_apply x) hB
  -- Unfold condDist to condMeasure
  show (TensorGibbs.condMeasure adj W {x} τ A).toReal ≤ _
  -- Set up notation
  set agr_τ := TensorGibbs.agreeing ({x} : Finset I) τ
  set agr_σ := TensorGibbs.agreeing ({x} : Finset I) σ
  set CW := TensorGibbs.condWeight adj W ({x} : Finset I)
  set Z_τ := TensorGibbs.condZ adj W {x} τ
  set Z_σ := TensorGibbs.condZ adj W {x} σ
  -- Convert both sides to real sums / Z
  rw [condMeasure_toReal_eq adj W {x} τ A hA,
      show (tensorGibbsSpec adj W).condDist {x} σ A =
        TensorGibbs.condMeasure adj W {x} σ A from rfl,
      condMeasure_toReal_eq adj W {x} σ A hA]
  -- Define the numerator sums
  set num_τ := ∑ ρ ∈ agr_τ, if ρ ∈ A then CW ρ else 0
  set num_σ := ∑ ρ ∈ agr_σ, if ρ ∈ A then CW ρ else 0
  -- Strategy: num_τ ≤ exp(2D) * num_σ and Z_σ ≤ exp(2D) * Z_τ
  rw [show Real.exp (4 * D) = Real.exp (2 * D) * Real.exp (2 * D) by
    rw [← Real.exp_add]; ring_nf]
  apply ratio_bound_of_sum_bounds num_σ num_τ Z_σ Z_τ
    (Real.exp (2 * D)) (Real.exp (2 * D))
  -- num_σ ≥ 0
  · exact Finset.sum_nonneg (fun ρ _ =>
      ite_nonneg (le_of_lt (TensorGibbs.condWeight_pos adj W {x} ρ)) le_rfl)
  -- num_τ ≥ 0
  · exact Finset.sum_nonneg (fun ρ _ =>
      ite_nonneg (le_of_lt (TensorGibbs.condWeight_pos adj W {x} ρ)) le_rfl)
  -- Z_σ > 0
  · exact TensorGibbs.condZ_pos adj W {x} σ
  -- Z_τ > 0
  · exact TensorGibbs.condZ_pos adj W {x} τ
  -- exp(2D) ≥ 0
  · exact le_of_lt (exp_pos _)
  · exact le_of_lt (exp_pos _)
  · -- num_τ ≤ exp(2D) * num_σ via bijection φ(ρ) = update ρ y (σ y)
    have hy_notin : y ∉ ({x} : Finset I) := not_mem_singleton_of_ne hxy
    have hφ_mem : ∀ ρ ∈ agr_τ, Function.update ρ y (σ y) ∈ agr_σ := by
      intro ρ hρ; rw [TensorGibbs.mem_agreeing] at hρ ⊢
      intro z hz; by_cases hzy : z = y
      · rw [hzy, Function.update_self]
      · rw [Function.update_of_ne hzy, hρ z hz, hdiff z hzy]
    have hψ_mem : ∀ ρ ∈ agr_σ, Function.update ρ y (τ y) ∈ agr_τ := by
      intro ρ hρ; rw [TensorGibbs.mem_agreeing] at hρ ⊢
      intro z hz; by_cases hzy : z = y
      · rw [hzy, Function.update_self]
      · rw [Function.update_of_ne hzy, hρ z hz, (hdiff z hzy).symm]
    have hψφ : ∀ ρ ∈ agr_τ,
        Function.update (Function.update ρ y (σ y)) y (τ y) = ρ := by
      intro ρ hρ; ext z; by_cases hzy : z = y
      · rw [hzy, Function.update_self,
            (TensorGibbs.mem_agreeing _ _ _).mp hρ y hy_notin]
      · rw [Function.update_of_ne hzy, Function.update_of_ne hzy]
    have hφψ : ∀ ρ ∈ agr_σ,
        Function.update (Function.update ρ y (τ y)) y (σ y) = ρ := by
      intro ρ hρ; ext z; by_cases hzy : z = y
      · rw [hzy, Function.update_self,
            (TensorGibbs.mem_agreeing _ _ _).mp hρ y hy_notin]
      · rw [Function.update_of_ne hzy, Function.update_of_ne hzy]
    have hφ_x : ∀ ρ : I → S, (Function.update ρ y (σ y)) x = ρ x :=
      fun ρ => Function.update_of_ne hxy ..
    calc num_τ = ∑ ρ ∈ agr_τ, if ρ ∈ A then CW ρ else 0 := rfl
      _ ≤ ∑ ρ ∈ agr_τ, (Real.exp (2 * D) *
          if (Function.update ρ y (σ y)) ∈ A
          then CW (Function.update ρ y (σ y)) else 0) := by
        apply Finset.sum_le_sum
        intro ρ hρ
        by_cases hρA : ρ ∈ A
        · have hφρA : Function.update ρ y (σ y) ∈ A := by
            simp only [A, Set.mem_preimage, hφ_x ρ]; exact hρA
          simp only [hρA, hφρA, ite_true]
          exact condWeight_update_le adj W x y hxy σ τ hdiff ρ hρ
        · simp only [hρA, ite_false]
          apply mul_nonneg (le_of_lt (exp_pos _))
          split_ifs
          · exact le_of_lt (TensorGibbs.condWeight_pos adj W {x} _)
          · exact le_refl 0
      _ = Real.exp (2 * D) * ∑ ρ ∈ agr_τ,
          (if (Function.update ρ y (σ y)) ∈ A
           then CW (Function.update ρ y (σ y)) else 0) :=
        (Finset.mul_sum ..).symm
      _ = Real.exp (2 * D) * num_σ := by
        congr 1
        exact Finset.sum_nbij'
          (fun ρ => Function.update ρ y (σ y))
          (fun ρ => Function.update ρ y (τ y))
          hφ_mem hψ_mem hψφ hφψ
          (fun ρ _ => rfl)
  · -- Z_σ ≤ exp(2D) * Z_τ via the same bijection (reversed direction)
    show Z_σ ≤ Real.exp (2 * D) * Z_τ
    have hy_notin : y ∉ ({x} : Finset I) := not_mem_singleton_of_ne hxy
    have hdiff' : ∀ z, z ≠ y → τ z = σ z := fun z hz => (hdiff z hz).symm
    have hψ_mem : ∀ ρ ∈ agr_σ, Function.update ρ y (τ y) ∈ agr_τ := by
      intro ρ hρ; rw [TensorGibbs.mem_agreeing] at hρ ⊢
      intro z hz; by_cases hzy : z = y
      · rw [hzy, Function.update_self]
      · rw [Function.update_of_ne hzy, hρ z hz, (hdiff z hzy).symm]
    have hφ_mem : ∀ ρ ∈ agr_τ, Function.update ρ y (σ y) ∈ agr_σ := by
      intro ρ hρ; rw [TensorGibbs.mem_agreeing] at hρ ⊢
      intro z hz; by_cases hzy : z = y
      · rw [hzy, Function.update_self]
      · rw [Function.update_of_ne hzy, hρ z hz, hdiff z hzy]
    have hψφ : ∀ ρ ∈ agr_τ,
        Function.update (Function.update ρ y (σ y)) y (τ y) = ρ := by
      intro ρ hρ; ext z; by_cases hzy : z = y
      · rw [hzy, Function.update_self,
            (TensorGibbs.mem_agreeing _ _ _).mp hρ y hy_notin]
      · rw [Function.update_of_ne hzy, Function.update_of_ne hzy]
    have hφψ : ∀ ρ ∈ agr_σ,
        Function.update (Function.update ρ y (τ y)) y (σ y) = ρ := by
      intro ρ hρ; ext z; by_cases hzy : z = y
      · rw [hzy, Function.update_self,
            (TensorGibbs.mem_agreeing _ _ _).mp hρ y hy_notin]
      · rw [Function.update_of_ne hzy, Function.update_of_ne hzy]
    -- Use condWeight_update_le with τ, σ swapped
    -- For ρ ∈ agr_σ, need ρ ∈ agreeing {x} σ (viewing σ as the "τ" in the swapped call)
    -- and the update direction is y ↦ τ y (viewing τ as the "σ" in the swapped call).
    -- condWeight_update_le adj W x y hxy τ σ hdiff' ρ hρ_in_agr_σ_viewed_as_agr_τ'
    -- where ρ ∈ agreeing {x} σ, and we need to show ρ ∈ agreeing {x} σ (viewed as "τ").
    -- The swapped call: condWeight_update_le adj W x y hxy τ σ hdiff' ρ (hρ as member of agreeing {x} σ)
    -- gives CW ρ ≤ exp(2D) * CW (update ρ y (τ y)).
    -- Wait: the signature says (σ τ : I → S) (hdiff : ...) (ρ : ...) (hρ : ρ ∈ agreeing {x} τ)
    -- So with swapped args: σ' = τ, τ' = σ, hdiff' = ..., hρ : ρ ∈ agreeing {x} σ.
    -- Result: CW ρ ≤ exp(2D) * CW (update ρ y (τ y)). Exactly what we need!
    calc ∑ ρ ∈ agr_σ, CW ρ
        ≤ ∑ ρ ∈ agr_σ, (Real.exp (2 * D) * CW (Function.update ρ y (τ y))) := by
          apply Finset.sum_le_sum
          intro ρ hρ
          exact condWeight_update_le adj W x y hxy τ σ hdiff' ρ hρ
      _ = Real.exp (2 * D) * ∑ ρ ∈ agr_σ, CW (Function.update ρ y (τ y)) :=
          (Finset.mul_sum ..).symm
      _ = Real.exp (2 * D) * ∑ ρ ∈ agr_τ, CW ρ := by
          congr 1
          exact Finset.sum_nbij'
            (fun ρ => Function.update ρ y (τ y))
            (fun ρ => Function.update ρ y (σ y))
            hψ_mem hφ_mem hφψ hψφ
            (fun ρ _ => rfl)

/-- Non-neighbor invariance: when y is not adjacent to x, changing sigma at y
does not change the cylinder probability at x. -/
theorem cylinder_eq_non_neighbor
    (W : NNBoltzmannWeight S) (x y : I) (hxy : x ≠ y)
    (σ τ : I → S) (hdiff : ∀ z, z ≠ y → σ z = τ z)
    (h1 : ¬ adj x y) (h2 : ¬ adj y x)
    (B : Set S) (hB : MeasurableSet B) :
    ((tensorGibbsSpec adj W).condDist {x} τ
      ((fun ρ : I → S => ρ x) ⁻¹' B)).toReal =
    ((tensorGibbsSpec adj W).condDist {x} σ
      ((fun ρ : I → S => ρ x) ⁻¹' B)).toReal := by
  -- Strategy: define φ : agreeing {x} τ → agreeing {x} σ by updating y to σ(y).
  -- φ preserves condWeight and x-value, so all ENNReal sums agree.
  -- Key helper: no edge in adjPairsTouching {x} involves y.
  have hay_edge : ∀ p ∈ TensorGibbs.adjPairsTouching adj ({x} : Finset I),
      p.1 ≠ y ∧ p.2 ≠ y := by
    intro ⟨a, b⟩ hp
    simp only [TensorGibbs.adjPairsTouching, TensorGibbs.adjPairs,
      Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hadj_ab, hab_touch⟩ := hp
    constructor
    · intro heq; subst heq
      rcases hab_touch with hax | hbx
      · exact absurd (Finset.mem_singleton.mp hax) (Ne.symm hxy)
      · exact h2 (Finset.mem_singleton.mp hbx ▸ hadj_ab)
    · intro heq; subst heq
      rcases hab_touch with hax | hbx
      · exact h1 (Finset.mem_singleton.mp hax ▸ hadj_ab)
      · exact absurd (Finset.mem_singleton.mp hbx) (Ne.symm hxy)
  -- Core: for ρ₁, ρ₂ that agree everywhere except possibly at y,
  -- condWeight {x} ρ₁ = condWeight {x} ρ₂.
  have hcw_eq : ∀ (ρ₁ ρ₂ : I → S), (∀ z, z ≠ y → ρ₁ z = ρ₂ z) →
      TensorGibbs.condWeight adj W {x} ρ₁ = TensorGibbs.condWeight adj W {x} ρ₂ := by
    intro ρ₁ ρ₂ hρ
    unfold TensorGibbs.condWeight
    apply Finset.prod_congr rfl
    intro ⟨a, b⟩ hp
    have ⟨hay, hby⟩ := hay_edge ⟨a, b⟩ hp
    rw [hρ a hay, hρ b hby]
  -- Define φ : (I → S) → (I → S) by updating y to σ(y)
  -- and ψ : (I → S) → (I → S) by updating y to τ(y)
  -- φ maps agreeing {x} τ → agreeing {x} σ
  -- ψ maps agreeing {x} σ → agreeing {x} τ
  -- ψ ∘ φ is identity on agreeing {x} τ (since φ(ρ)(y) = σ(y) and ψ restores τ(y),
  --   but all other values are preserved, and the ρ(z) for z ≠ x, z ≠ y are the same)
  -- Actually ψ(φ(ρ)) restores y to τ(y) and all other z ≠ y are unchanged.
  -- For z ≠ y: ψ(φ(ρ))(z) = φ(ρ)(z) = ρ(z) (since update only changes y).
  -- For z = y: ψ(φ(ρ))(y) = τ(y). And ρ(y) = τ(y) (since ρ ∈ agreeing {x} τ and y ≠ x).
  -- So ψ(φ(ρ)) = ρ. Similarly φ(ψ(ρ')) = ρ' for ρ' ∈ agreeing {x} σ.
  have hφ_mem : ∀ ρ, ρ ∈ TensorGibbs.agreeing ({x} : Finset I) τ →
      Function.update ρ y (σ y) ∈ TensorGibbs.agreeing ({x} : Finset I) σ := by
    intro ρ hρ
    rw [TensorGibbs.mem_agreeing] at hρ ⊢
    intro z hz
    by_cases hzy : z = y
    · rw [hzy, Function.update_self]
    · rw [Function.update_of_ne hzy, hρ z hz, hdiff z hzy]
  have hψ_mem : ∀ ρ, ρ ∈ TensorGibbs.agreeing ({x} : Finset I) σ →
      Function.update ρ y (τ y) ∈ TensorGibbs.agreeing ({x} : Finset I) τ := by
    intro ρ hρ
    rw [TensorGibbs.mem_agreeing] at hρ ⊢
    intro z hz
    by_cases hzy : z = y
    · rw [hzy, Function.update_self]
    · rw [Function.update_of_ne hzy, hρ z hz]
      exact hdiff z hzy
  -- Left inverse: ψ(φ(ρ)) = ρ for ρ ∈ agreeing {x} τ
  have hψφ : ∀ ρ ∈ TensorGibbs.agreeing ({x} : Finset I) τ,
      Function.update (Function.update ρ y (σ y)) y (τ y) = ρ := by
    intro ρ hρ
    ext z
    by_cases hzy : z = y
    · rw [hzy, Function.update_self,
          (TensorGibbs.mem_agreeing _ _ _).mp hρ y (by simp [Ne.symm hxy])]
    · rw [Function.update_of_ne hzy, Function.update_of_ne hzy]
  -- Right inverse: φ(ψ(ρ')) = ρ' for ρ' ∈ agreeing {x} σ
  have hφψ : ∀ ρ ∈ TensorGibbs.agreeing ({x} : Finset I) σ,
      Function.update (Function.update ρ y (τ y)) y (σ y) = ρ := by
    intro ρ hρ
    ext z
    by_cases hzy : z = y
    · rw [hzy, Function.update_self,
          (TensorGibbs.mem_agreeing _ _ _).mp hρ y (by simp [Ne.symm hxy])]
    · rw [Function.update_of_ne hzy, Function.update_of_ne hzy]
  -- φ preserves condWeight
  have hφ_cw : ∀ ρ ∈ TensorGibbs.agreeing ({x} : Finset I) τ,
      TensorGibbs.condWeight adj W {x} ρ =
      TensorGibbs.condWeight adj W {x} (Function.update ρ y (σ y)) := by
    intro ρ _
    exact hcw_eq ρ _ (fun z hzy => Eq.symm (Function.update_of_ne hzy (σ y) ρ))
  -- φ preserves the x-value
  have hφ_x : ∀ ρ : I → S, (Function.update ρ y (σ y)) x = ρ x :=
    fun ρ => Function.update_of_ne hxy (σ y) ρ
  -- Now show the ENNReal condMeasure values are equal.
  congr 1
  show TensorGibbs.condMeasure adj W {x} τ _ = TensorGibbs.condMeasure adj W {x} σ _
  unfold TensorGibbs.condMeasure
  simp only [Measure.smul_apply, smul_eq_mul]
  -- Show Z_τ = Z_σ via sum_nbij'
  have hZ : TensorGibbs.condZ adj W {x} τ = TensorGibbs.condZ adj W {x} σ := by
    unfold TensorGibbs.condZ
    exact Finset.sum_nbij'
      (fun ρ => Function.update ρ y (σ y))
      (fun ρ => Function.update ρ y (τ y))
      hφ_mem hψ_mem hψφ hφψ
      (fun ρ hρ => hφ_cw ρ hρ)
  -- Show unnormalized measures agree on the cylinder set
  have hU : TensorGibbs.condMeasureUnnorm adj W {x} τ ((fun ρ => ρ x) ⁻¹' B) =
      TensorGibbs.condMeasureUnnorm adj W {x} σ ((fun ρ => ρ x) ⁻¹' B) := by
    rw [TensorGibbs.condMeasureUnnorm_apply, TensorGibbs.condMeasureUnnorm_apply]
    apply Finset.sum_nbij'
      (fun ρ => Function.update ρ y (σ y))
      (fun ρ => Function.update ρ y (τ y))
      hφ_mem hψ_mem hψφ hφψ
    intro ρ hρ
    rw [hφ_cw ρ hρ]
    congr 1
    -- Dirac masses: δ_{φ(ρ)}(A) = δ_ρ(A) for A = (· x) ⁻¹' B since φ(ρ)(x) = ρ(x)
    have hBm : MeasurableSet ((fun ρ : I → S => ρ x) ⁻¹' B) :=
      measurableSet_preimage (measurable_pi_apply x) hB
    simp only [Measure.dirac_apply' _ hBm]
    -- Goal: indicator equality. Both conditions agree since φ(ρ)(x) = ρ(x).
    have : Function.update ρ y (σ y) ∈ (fun ρ : I → S => ρ x) ⁻¹' B ↔
        ρ ∈ (fun ρ : I → S => ρ x) ⁻¹' B := by
      simp only [Set.mem_preimage, hφ_x ρ]
    by_cases hρB : ρ ∈ (fun ρ : I → S => ρ x) ⁻¹' B
    · simp [hρB, this.mpr hρB]
    · simp [hρB, mt this.mp hρB]
  rw [hZ, hU]

/-! ## Influence coefficient bound -/

/-- The influence of site x on itself is 0. -/
private theorem influenceCoeff_self_eq_zero (W : NNBoltzmannWeight S) (x : I) :
    influenceCoeff (tensorGibbsSpec adj W) x x = 0 := by
  set γ := tensorGibbsSpec adj W
  have hle : influenceCoeff γ x x ≤ 1 - exp (-(0 : ℝ)) := by
    apply influenceCoeff_le_of_cylinder_ratio_bound γ x x 0 le_rfl
    intro σ τ hdiff B hB
    rw [exp_zero, one_mul]
    have heq : γ.condDist {x} σ = γ.condDist {x} τ :=
      γ.consistent {x} σ τ (fun z hz => hdiff z (by
        simp only [Finset.mem_singleton] at hz; exact hz))
    rw [heq]
  simp at hle
  exact le_antisymm hle (influenceCoeff_nonneg γ x x)

/-- The influence coefficient for the tensor Gibbs spec. -/
theorem tensorGibbsSpec_influence_le
    (W : NNBoltzmannWeight S) (x y : I) (hxy : x ≠ y) :
    influenceCoeff (tensorGibbsSpec adj W) x y ≤
      if (adj x y ∨ adj y x) then influenceBoundTensor W else 0 := by
  split_ifs with h
  · -- Adjacent case
    calc influenceCoeff (tensorGibbsSpec adj W) x y
        ≤ 1 - exp (-(4 * weightOscillation W)) := by
          apply influenceCoeff_le_of_cylinder_ratio_bound
            (tensorGibbsSpec adj W) x y (4 * weightOscillation W)
            (by linarith [weightOscillation_nonneg W])
          exact fun σ τ hdiff B hB =>
            cylinder_ratio_bound adj W x y hxy σ τ hdiff B hB
      _ = influenceBoundTensor W := by
          unfold influenceBoundTensor; ring_nf
  · -- Non-adjacent case
    have h' : ¬(adj x y) ∧ ¬(adj y x) := not_or.mp h
    calc influenceCoeff (tensorGibbsSpec adj W) x y
        ≤ 1 - exp (-(0 : ℝ)) := by
          apply influenceCoeff_le_of_cylinder_ratio_bound
            (tensorGibbsSpec adj W) x y 0 le_rfl
          intro σ τ hdiff B hB
          rw [exp_zero, one_mul]
          exact le_of_eq
            (cylinder_eq_non_neighbor adj W x y hxy σ τ hdiff h'.1 h'.2 B hB)
      _ = 0 := by simp

/-- Bound influence for any pair including x = y. -/
private theorem influenceCoeff_le_indicator
    (W : NNBoltzmannWeight S) (x y : I) :
    influenceCoeff (tensorGibbsSpec adj W) x y ≤
      if (adj x y ∨ adj y x) then influenceBoundTensor W else 0 := by
  by_cases hxy : x = y
  · subst hxy; rw [influenceCoeff_self_eq_zero adj W x]
    split_ifs with h
    · exact influenceBoundTensor_nonneg W
    · exact le_refl 0
  · exact tensorGibbsSpec_influence_le adj W x y hxy

/-! ## Dobrushin condition -/

omit [DecidableEq I] in
private theorem filter_adj_comm (y : I) :
    (Finset.univ : Finset I).filter (fun x => adj x y ∨ adj y x) =
    (Finset.univ : Finset I).filter (fun x => adj y x ∨ adj x y) := by
  apply Finset.filter_congr; intro x _; exact Or.comm

/-- The tensor Gibbs spec satisfies Dobrushin's condition when the
oscillation is small enough relative to the maximum degree. -/
def tensorGibbsSpec_dobrushin_condition
    (W : NNBoltzmannWeight S) (maxDeg : ℕ)
    (hDeg : ∀ x : I,
      (Finset.univ.filter (fun y => adj x y ∨ adj y x)).card ≤ maxDeg)
    (hSmall : (maxDeg : ℝ) * influenceBoundTensor W < 1) :
    DobrushinCondition (tensorGibbsSpec adj W) :=
  let γ := tensorGibbsSpec adj W
  { α := (maxDeg : ℝ) * influenceBoundTensor W
    hα_pos := mul_nonneg (Nat.cast_nonneg' maxDeg) (influenceBoundTensor_nonneg W)
    hα_lt := hSmall
    col_summable := fun y => summable_of_ne_finset_zero (s := Finset.univ)
      (fun x hx => (hx (Finset.mem_univ x)).elim)
    column_bound := by
      intro y
      rw [tsum_eq_sum (s := Finset.univ)
        (fun x hx => (hx (Finset.mem_univ x)).elim)]
      calc ∑ x : I, influenceCoeff γ x y
          ≤ ∑ x : I, if (adj x y ∨ adj y x)
              then influenceBoundTensor W else 0 :=
            Finset.sum_le_sum fun x _ => influenceCoeff_le_indicator adj W x y
        _ = ((Finset.univ : Finset I).filter
              (fun x => adj x y ∨ adj y x)).card *
            influenceBoundTensor W := by
          rw [← Finset.sum_filter]; rw [Finset.sum_const]
          simp [nsmul_eq_mul]
        _ ≤ (maxDeg : ℝ) * influenceBoundTensor W := by
          apply mul_le_mul_of_nonneg_right _ (influenceBoundTensor_nonneg W)
          rw [filter_adj_comm adj y]; exact_mod_cast hDeg y
    row_summable := fun x => summable_of_ne_finset_zero (s := Finset.univ)
      (fun y hy => (hy (Finset.mem_univ y)).elim)
    row_bound := by
      intro x
      rw [tsum_eq_sum (s := Finset.univ)
        (fun y hy => (hy (Finset.mem_univ y)).elim)]
      calc ∑ y : I, influenceCoeff γ x y
          ≤ ∑ y : I, if (adj x y ∨ adj y x)
              then influenceBoundTensor W else 0 :=
            Finset.sum_le_sum fun y _ => influenceCoeff_le_indicator adj W x y
        _ = ((Finset.univ : Finset I).filter
              (fun y => adj x y ∨ adj y x)).card *
            influenceBoundTensor W := by
          rw [← Finset.sum_filter]; rw [Finset.sum_const]
          simp [nsmul_eq_mul]
        _ ≤ (maxDeg : ℝ) * influenceBoundTensor W := by
          apply mul_le_mul_of_nonneg_right _ (influenceBoundTensor_nonneg W)
          exact_mod_cast hDeg x }

end TensorGibbs

end
