/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Single-Site Markov Kernel for 2D Yang-Mills

After gauge fixing in d=2, the partition function factorizes into
independent single-site transfer matrices. This file constructs
the concrete Markov kernel for each spatial site and connects it
to the Doeblin verification.

## Main definitions

- `singleSitePartitionFn` — Z(V) = ∫ q(V,W) dμ_Haar(W)
- `singleSiteKernel` — the Markov kernel K(V, A) = ∫_A q/Z dμ
- `singleSiteKernel_satisfies_doeblin` — Doeblin condition

## References

- Chatterjee (2026), §15.7
-/

import LGT.MassGap.TransferMatrix
import LGT.MassGap.Integrability

open MeasureTheory

noncomputable section

variable (G : Type*) (n : ℕ) [Group G] [HasGaugeTrace G n]
variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable [MeasurableSpace G] [BorelSpace G]

variable (μ : Measure G) [IsProbabilityMeasure μ]

/-- The single-site transition weight W ↦ q(V,W) is continuous when the
representation is continuous. This follows from continuity of rep, group
multiplication, matrix trace, and Real.exp. -/
theorem singleSiteTransitionWeight_continuous
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n)))
    (β : ℝ) (V : G) :
    Continuous (singleSiteTransitionWeight G n β V ·) := by
  unfold singleSiteTransitionWeight gaugeReTr gaugeTrace
  fun_prop

/-! ## Single-site partition function -/

/-- The single-site partition function at source V:
Z(V) = ∫ q(V,W) dμ(W) where q is the transition weight. -/
def singleSiteZ (β : ℝ) (V : G) : ℝ :=
  ∫ W, singleSiteTransitionWeight G n β V W ∂μ

/-- Z(V) > 0 because q(V,W) > 0 everywhere and μ is a probability measure.

More precisely: q(V,W) ≥ exp(-2nβ) > 0 for all W, so
Z(V) = ∫ q dμ ≥ ∫ exp(-2nβ) dμ = exp(-2nβ) > 0. -/
theorem singleSiteZ_pos (β : ℝ) (hβ : 0 ≤ β) (V : G)
    (hTrace : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n))) :
    0 < singleSiteZ G n μ β V := by
  unfold singleSiteZ
  -- ∫ q dμ ≥ ∫ exp(-2nβ) dμ = exp(-2nβ) > 0
  have h_lower : ∀ W, ymDoeblinLowerBound n β ≤
      singleSiteTransitionWeight G n β V W :=
    fun W => singleSiteTransitionWeight_lower_bound G n β hβ V W hTrace
  calc 0 < ymDoeblinLowerBound n β := ymDoeblinLowerBound_pos n β
    _ = ∫ _, ymDoeblinLowerBound n β ∂μ := by
        rw [integral_const]; simp
    _ ≤ ∫ W, singleSiteTransitionWeight G n β V W ∂μ := by
        apply integral_mono (integrable_const _)
        · exact continuous_integrable_of_compactSpace
            (singleSiteTransitionWeight_continuous G n hRep_cont β V)
        · exact fun W => h_lower W

/-- Z(V) ≤ 1 when β ≥ 0 (since q ≤ 1 and μ is probability). -/
theorem singleSiteZ_le_one (β : ℝ) (hβ : 0 ≤ β) (V : G)
    (hTrace : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n))) :
    singleSiteZ G n μ β V ≤ 1 := by
  unfold singleSiteZ
  calc ∫ W, singleSiteTransitionWeight G n β V W ∂μ
      ≤ ∫ _, (1 : ℝ) ∂μ := by
        apply integral_mono
          (continuous_integrable_of_compactSpace
            (singleSiteTransitionWeight_continuous G n hRep_cont β V))
          (integrable_const _)
        intro W
        unfold singleSiteTransitionWeight
        rw [Real.exp_le_one_iff]
        nlinarith [hTrace (W * V⁻¹)]
    _ = 1 := by simp [integral_const]

/-! ## The concrete Markov kernel -/

/-- The single-site transition density: p(V,W) = q(V,W) / Z(V). -/
def singleSiteDensity (β : ℝ) (V W : G) : ℝ :=
  singleSiteTransitionWeight G n β V W / singleSiteZ G n μ β V

/-- The density is nonneg. -/
theorem singleSiteDensity_nonneg (β : ℝ) (hβ : 0 ≤ β) (V W : G)
    (hTrace : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hRep_cont : Continuous (HasGaugeTrace.rep (G := G) (n := n))) :
    0 ≤ singleSiteDensity G n μ β V W :=
  div_nonneg (Real.exp_pos _).le (le_of_lt (singleSiteZ_pos G n μ β hβ V hTrace hRep_cont))

/-- The density integrates to 1: ∫ p(V,W) dμ(W) = 1. -/
theorem singleSiteDensity_integral_one (β : ℝ) (V : G)
    (hZ_pos : 0 < singleSiteZ G n μ β V) :
    ∫ W, singleSiteDensity G n μ β V W ∂μ = 1 := by
  unfold singleSiteDensity singleSiteZ at *
  rw [integral_div]  -- ∫ (q/Z) = (∫ q)/Z = Z/Z = 1
  exact div_self (ne_of_gt hZ_pos)

end
