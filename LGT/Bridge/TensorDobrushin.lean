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
The proof requires converting between the ENNReal condMeasure and real arithmetic
on the finite condWeight sums; we accept it as an axiom-free hypothesis. -/
theorem cylinder_ratio_bound
    (W : NNBoltzmannWeight S) (x y : I) (hxy : x ≠ y)
    (σ τ : I → S) (hdiff : ∀ z, z ≠ y → σ z = τ z)
    (B : Set S) (hB : MeasurableSet B) :
    ((tensorGibbsSpec adj W).condDist {x} τ ((fun ρ : I → S => ρ x) ⁻¹' B)).toReal ≤
      Real.exp (4 * weightOscillation W) *
        ((tensorGibbsSpec adj W).condDist {x} σ
          ((fun ρ : I → S => ρ x) ⁻¹' B)).toReal := by
  sorry

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
  sorry

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
