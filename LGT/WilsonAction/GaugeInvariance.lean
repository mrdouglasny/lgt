/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gauge Invariance of the Wilson Action

The Wilson action S(U) = β Σ_p (n - Re Tr(U_p)) is invariant under
gauge transformations U ↦ g·U·g⁻¹, because:
1. Holonomy transforms as U_p ↦ g(x)·U_p·g(x)⁻¹ (Connection.lean)
2. The plaquette cost n - Re Tr(U_p) is invariant under conjugation
   (cyclicity of trace: Tr(gAg⁻¹) = Tr(A))

## Main results

- `gaugeReTr_conj_invariant` — Re Tr(gUg⁻¹) = Re Tr(U)
- `wilsonAction_gauge_invariant` — S(g·U) = S(U)
- `boltzmannWeight_gauge_invariant` — exp(-S(g·U)) = exp(-S(U))
- `plaqObs_gauge_invariant` — plaquette observables are gauge-invariant

## References

- Chatterjee (2026), §15.3 (gauge invariance)
-/

import LGT.MassGap.YMMeasure

set_option linter.unusedSectionVars false

open MeasureTheory GaussianField

noncomputable section

variable {G : Type*} {n : ℕ} [Group G] [HasGaugeTrace G n]
variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable [MeasurableSpace G] [BorelSpace G]
variable {d N : ℕ}

/-! ## Trace cyclicity ⟹ plaquette cost is conjugation-invariant -/

/-- The trace is invariant under conjugation: Tr(gAg⁻¹) = Tr(A).

For rep : G →* M_n(ℂ), Tr(rep(g·h·g⁻¹)) = Tr(rep(g)·rep(h)·rep(g)⁻¹)
= Tr(rep(h)) by cyclicity of matrix trace. -/
theorem gaugeTrace_conj_invariant (g h : G) :
    gaugeTrace G n (g * h * g⁻¹) = gaugeTrace G n h := by
  simp only [gaugeTrace, map_mul]
  -- Goal: trace (rep g * (rep h * rep g⁻¹)) = trace (rep h)
  -- Use trace_mul_cycle: Tr(A * B * C) = Tr(C * A * B)
  rw [Matrix.trace_mul_cycle]
  -- Goal: trace (rep g⁻¹ * rep g * rep h) = trace (rep h)
  rw [← map_mul, inv_mul_cancel, map_one, Matrix.one_mul]

/-- Re Tr is conjugation-invariant. -/
theorem gaugeReTr_conj_invariant (g h : G) :
    gaugeReTr G n (g * h * g⁻¹) = gaugeReTr G n h := by
  simp only [gaugeReTr, gaugeTrace_conj_invariant]

/-- The plaquette cost is conjugation-invariant. -/
theorem wilsonPlaquetteCost_conj_invariant (g Up : G) :
    wilsonPlaquetteCost G n (g * Up * g⁻¹) = wilsonPlaquetteCost G n Up := by
  simp only [wilsonPlaquetteCost, gaugeReTr_conj_invariant]

/-! ## Wilson action is gauge-invariant -/

/-- The Wilson action is gauge-invariant: S(g·U) = S(U). -/
theorem wilsonAction_gauge_invariant [HasHaarProbability G]
    [Fintype (LatticeLink d N)]
    (g : GaugeTransform G d N) (U : GaugeConnection G d N)
    (β : ℝ) (plaq : Finset (LatticePlaquette d N)) :
    wilsonAction G n d N β (gaugeTransformConnection g U) plaq =
    wilsonAction G n d N β U plaq := by
  simp only [wilsonAction]
  apply Finset.sum_congr rfl
  intro p _
  congr 1
  rw [holonomy_gauge_covariant, wilsonPlaquetteCost_conj_invariant]

/-- The Boltzmann weight is gauge-invariant: exp(-S(g·U)) = exp(-S(U)). -/
theorem boltzmannWeight_gauge_invariant [HasHaarProbability G]
    [Fintype (LatticeLink d N)]
    (g : GaugeTransform G d N) (U : GaugeConnection G d N)
    (β : ℝ) (plaq : Finset (LatticePlaquette d N)) :
    boltzmannWeight G n d N β (gaugeTransformConnection g U) plaq =
    boltzmannWeight G n d N β U plaq := by
  simp only [boltzmannWeight, wilsonAction_gauge_invariant]

/-! ## Gauge-invariant observables -/

/-- An observable is gauge-invariant if f(g·U) = f(U) for all g. -/
def IsGaugeInvariant (f : GaugeConnection G d N → ℝ) : Prop :=
  ∀ (g : GaugeTransform G d N) (U : GaugeConnection G d N),
    f (gaugeTransformConnection g U) = f U

/-- Plaquette observables Re Tr(U_p) are gauge-invariant. -/
theorem plaqObs_gauge_invariant [HasHaarProbability G]
    [Fintype (LatticeLink d N)]
    (p : LatticePlaquette d N) :
    IsGaugeInvariant (plaqObs G n d N p) := by
  intro g U
  simp only [plaqObs, holonomy_gauge_covariant, gaugeReTr_conj_invariant]

/-- Products of gauge-invariant observables are gauge-invariant. -/
theorem isGaugeInvariant_mul {f₁ f₂ : GaugeConnection G d N → ℝ}
    (h₁ : IsGaugeInvariant f₁) (h₂ : IsGaugeInvariant f₂) :
    IsGaugeInvariant (fun U => f₁ U * f₂ U) := by
  intro g U; simp [h₁ g U, h₂ g U]

end
