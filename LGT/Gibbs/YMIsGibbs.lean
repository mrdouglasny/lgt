/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `ymMeasure` is a Gibbs measure for `ymGibbsSpec`

Proves the DLR identity:
```
(ymMeasure A).toReal = ∫ σ, (gibbsCondMeasure Λ σ A).toReal ∂ymMeasure
```
for every finite `Λ ⊂ LatticeLink d N` and every measurable
`A ⊂ GaugeConnection G d N`.

## Proof sketch

Write the RHS as
```
∫ σ [(1/Z(σ_Λᶜ)) · ∫ uΛ 1_A(glue uΛ σ) · w(glue uΛ σ) dHaar^Λ(uΛ)] · (w(σ)/Z) dHaar(σ)
```
Split `σ = (σ_Λ, σ_Λᶜ)` via the link-Λ/Λᶜ factorisation of
`productHaar`. The conditional partition `Z(σ_Λᶜ) = ∫ σ_Λ, w(σ_Λ, σ_Λᶜ) dHaar^Λ`
(depends only on `σ_Λᶜ`) is exactly the inner integral needed to
normalise `(w(σ)/Z(σ_Λᶜ))`, which integrates over `σ_Λ` to 1. Fubini
then reassembles the remaining factor into `(1/Z) · ∫ 1_A · w dHaar =
(ymMeasure A).toReal`.

## Status

This file sets up the DLR identity as a series of named
intermediate lemmas. Several of them involve Fubini on the
`Haar^Λ ⊗ Haar^Λᶜ` factorisation of `productHaar`, which is
genuine measure-theoretic work. They are left as `sorry` with
precise statements; the main theorem `ymMeasure_isGibbs` is a
mechanical assembly of those lemmas.

## References

- Chatterjee (2026), §16.3
- markov-semigroups/Dobrushin/Specification.lean — DLR definition
-/

import LGT.MassGap.YMMeasure
import LGT.Gibbs.YMSpec
import MarkovSemigroups.Dobrushin.Specification

open MeasureTheory

noncomputable section

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
variable [HasHaarProbability G]
variable (n d N : ℕ) [HasGaugeTrace G n] [Fintype (LatticeLink d N)]
variable [DecidableEq (LatticeLink d N)]
variable (plaq : Finset (LatticePlaquette d N))

/-! ## Intermediate lemmas for the DLR identity -/

/-- The conditional partition function depends only on the boundary
`σ|_{Λᶜ}`.

If `σ` and `τ` agree outside `Λ`, then
`gibbsConditionalZ Λ σ = gibbsConditionalZ Λ τ`. This is a
direct consequence of the definition of `gluedConfig`, which
reads `σ` only on `Λᶜ`. -/
theorem gibbsConditionalZ_eq_of_agrees_outside
    (β : ℝ) (Λ : Finset (LatticeLink d N))
    (σ τ : GaugeConnection G d N)
    (hστ : ∀ x, x ∉ Λ → σ x = τ x) :
    gibbsConditionalZ G n d N plaq β Λ σ =
      gibbsConditionalZ G n d N plaq β Λ τ := by
  unfold gibbsConditionalZ gibbsConditionalWeight
  congr 1
  funext uΛ
  congr 1
  funext e
  by_cases he : e ∈ Λ
  · simp [gluedConfig, he]
  · simp [gluedConfig, he, hστ e he]

/-- **Key identity.** The integral of the Boltzmann weight equals
`∫ σ Z(σ) dHaar(σ)`, the σ-average of the conditional partition
function.

### Proof sketch (Fubini over `piEquivPiSubtypeProd`)

Let `p := fun e : LatticeLink d N => e ∈ Λ`. Then
`MeasurableEquiv.piEquivPiSubtypeProd _ p` gives a measurable
equivalence `(LatticeLink → G) ≃ᵐ (Λ → G) × (Λᶜ → G)`, and
`MeasureTheory.measurePreserving_piEquivPiSubtypeProd` says it is
measure-preserving from `productHaar` to `(Measure.pi Λ haarG) ⊗
(Measure.pi Λᶜ haarG)`.

Under this equivalence:
- `partitionFn = ∫ U w(U) dHaar = ∫ (uΛ, uΛᶜ) w(combine uΛ uΛᶜ) d(μΛ ⊗ μΛᶜ)`
- `gibbsConditionalZ Λ σ = ∫ uΛ_all w(glue uΛ_all σ) dHaar`; the integrand
  depends only on `uΛ_all|_Λ` and `σ|_Λᶜ`, so by the split +
  `μΛᶜ(univ) = 1`:
    `= ∫ uΛ w(combine uΛ σ|_Λᶜ) dμΛ`
- `∫ σ Z(σ) dHaar = ∫ (σΛ, σΛᶜ) Z(σ) d(μΛ ⊗ μΛᶜ)`, integrand
  depends only on `σΛᶜ`, so by `μΛ(univ) = 1`:
    `= ∫ σΛᶜ (∫ uΛ w(combine uΛ σΛᶜ) dμΛ) dμΛᶜ`
- Fubini combines the two into `∫ (uΛ, σΛᶜ) w(combine) d(μΛ ⊗ μΛᶜ)
  = partitionFn` via the inverse equivalence.

Estimated ~80 lines. Uses: `MeasurePreserving.integral_map_equiv`,
`integral_prod`, `integral_const` over probability measures. -/
theorem partitionFn_eq_integral_gibbsConditionalZ
    (β : ℝ) (Λ : Finset (LatticeLink d N)) :
    partitionFn G n d N β plaq =
      ∫ σ, gibbsConditionalZ G n d N plaq β Λ σ ∂(productHaar G d N) := by
  sorry

/-- **Key identity.** Fubini on `Haar^Λ × Haar^Λᶜ` for the
indicator × Boltzmann integrand:
```
∫ U, 1_A(U) · w(U) dHaar
  = ∫ σ [∫ uΛ, 1_A(glue Λ uΛ σ) · w(glue Λ uΛ σ) dHaar(uΛ)] dHaar(σ)
```

### Proof sketch

Same decomposition as `partitionFn_eq_integral_gibbsConditionalZ`,
applied to `F(U) := 1_A(U) · w(U)` instead of `w(U)`:
- Split `productHaar ≃ᵐ μΛ ⊗ μΛᶜ` via `piEquivPiSubtypeProd`.
- Under the equivalence, the LHS integrand is `F(combine uΛ uΛᶜ)`,
  depending on both coordinates.
- The inner integral on the RHS, `∫ uΛ F(glue Λ uΛ σ) dHaar(uΛ)`,
  decomposes as `∫ (uΛ_Λ, uΛ_Λᶜ) F(combine uΛ_Λ σ_Λᶜ) d(μΛ ⊗ μΛᶜ)`.
  Integrand doesn't depend on `uΛ_Λᶜ`, so equals
  `∫ uΛ_Λ F(combine uΛ_Λ σ_Λᶜ) dμΛ`.
- Outer integral over σ: split `σ = (σΛ, σΛᶜ)`. The inner
  integral depends on σ only via σ_Λᶜ. So `∫ σ [...] dHaar =
  ∫ σΛᶜ [...] dμΛᶜ`.
- Combining: RHS = `∫ (uΛ_Λ, σΛᶜ) F(combine uΛ_Λ σΛᶜ) d(μΛ ⊗ μΛᶜ)
  = ∫ U F(U) dHaar(U) = LHS`.

Estimated ~100 lines, structurally identical to
`partitionFn_eq_integral_gibbsConditionalZ`. Could be factored
through a general `integral_split_glue` helper lemma. -/
theorem integral_indicator_w_fubini_link_split
    (β : ℝ) (Λ : Finset (LatticeLink d N))
    (A : Set (GaugeConnection G d N)) (hA : MeasurableSet A) :
    ∫ U, Set.indicator A (fun U => boltzmannWeight G n d N β U plaq) U
        ∂(productHaar G d N) =
    ∫ σ, (∫ uΛ,
        Set.indicator A
          (fun U => boltzmannWeight G n d N β U plaq)
          (gluedConfig G d N Λ uΛ σ)
        ∂(Measure.pi (fun _ : LatticeLink d N => haarG G)))
      ∂(productHaar G d N) := by
  sorry

/-- **Main DLR identity: `ymMeasure` satisfies DLR for `ymGibbsSpec`.**

For every finite `Λ` and measurable `A`:
`(ymMeasure A).toReal = ∫ σ, (gibbsCondMeasure Λ σ A).toReal ∂ymMeasure`.

Assumes:
- `hβ`, `hTrace_lower`, `hTrace_upper` — for `Z > 0` and trace bounds
- `hIntegrable_w` — integrability of the Boltzmann weight
- `hw_meas` — measurability of the Boltzmann weight
- `hZcond_pos` — the conditional partition function is positive for
  every boundary (from strict positivity of `w > 0` and `Haar^Λ` being
  a probability measure; direct analogue of `partitionFn_pos`).
- `hw_integrable_cond` — the conditional Boltzmann weight is
  `Haar^Λ`-integrable for every boundary.
-/
theorem ymMeasure_dlr
    (β : ℝ) (hβ : 0 ≤ β)
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hIntegrable_w : Integrable (fun U => boltzmannWeight G n d N β U plaq)
        (productHaar G d N))
    (hw_meas : Measurable (fun U => boltzmannWeight G n d N β U plaq))
    (hZcond_pos : ∀ (Λ : Finset (LatticeLink d N)) (σ : GaugeConnection G d N),
        0 < gibbsConditionalZ G n d N plaq β Λ σ)
    (hw_integrable_cond : ∀ (Λ : Finset (LatticeLink d N))
        (σ : GaugeConnection G d N),
        Integrable (fun uΛ : LatticeLink d N → G =>
            gibbsConditionalWeight G n d N plaq β Λ σ uΛ)
          (Measure.pi (fun _ : LatticeLink d N => haarG G)))
    (Λ : Finset (LatticeLink d N))
    (A : Set (GaugeConnection G d N)) (hA : MeasurableSet A) :
    ((ymMeasure G n d N β plaq) A).toReal =
      ∫ σ, (gibbsCondMeasure G n d N plaq β Λ σ A).toReal
        ∂(ymMeasure G n d N β plaq) := by
  -- Scope sorry: the explicit computation unfolds both measures via
  -- `withDensity`, applies `partitionFn_eq_integral_gibbsConditionalZ`
  -- and `integral_indicator_w_fubini_link_split`, and cancels the
  -- `Z(σ_Λᶜ)` factors. ~150 lines of measure-theoretic bookkeeping.
  sorry

/-- **`ymMeasure` is a Gibbs measure for `ymGibbsSpec`.**

Packages the DLR identity into the `IsGibbsMeasure` structure.

The `ymGibbsSpec` constructor takes four hypotheses (`hZ_pos`,
`hw_meas`, `hw_integrable`, `hmeas_condDist`); we require all
four here, but this theorem is the final bridge to the abstract
Dobrushin framework. -/
theorem ymMeasure_isGibbs
    (β : ℝ) (hβ : 0 ≤ β)
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hIntegrable_w : Integrable (fun U => boltzmannWeight G n d N β U plaq)
        (productHaar G d N))
    (hw_meas : Measurable (fun U => boltzmannWeight G n d N β U plaq))
    (hZcond_pos : ∀ (Λ : Finset (LatticeLink d N)) (σ : GaugeConnection G d N),
        0 < gibbsConditionalZ G n d N plaq β Λ σ)
    (hw_integrable_cond : ∀ (Λ : Finset (LatticeLink d N))
        (σ : GaugeConnection G d N),
        Integrable (fun uΛ : LatticeLink d N → G =>
            gibbsConditionalWeight G n d N plaq β Λ σ uΛ)
          (Measure.pi (fun _ : LatticeLink d N => haarG G)))
    (hmeas_condDist : ∀ (Λ : Finset (LatticeLink d N))
        (A : Set (GaugeConnection G d N)),
        MeasurableSet A →
        Measurable (fun σ : GaugeConnection G d N =>
          (gibbsCondMeasure G n d N plaq β Λ σ A).toReal))
    (hμ_prob : IsProbabilityMeasure (ymMeasure G n d N β plaq)) :
    @IsGibbsMeasure _ _ _ _
      (ymGibbsSpec G n d N plaq β
        hZcond_pos hw_meas hw_integrable_cond hmeas_condDist)
      (ymMeasure G n d N β plaq) hμ_prob :=
  @IsGibbsMeasure.mk _ _ _ _
    (ymGibbsSpec G n d N plaq β
      hZcond_pos hw_meas hw_integrable_cond hmeas_condDist)
    (ymMeasure G n d N β plaq) hμ_prob
    (fun Λ A hA =>
      ymMeasure_dlr G n d N plaq β hβ hTrace_upper hTrace_lower
        hIntegrable_w hw_meas hZcond_pos hw_integrable_cond Λ A hA)

end
