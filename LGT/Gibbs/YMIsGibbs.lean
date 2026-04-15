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

Proven end-to-end: no sorries, no axioms. The DLR identity is
assembled from named intermediate lemmas — `glue_measurePreserving`
for the core pushforward, `integral_glue_split_eq` for the Fubini
reduction, `integral_smul_condZ_eq_integral_smul_w` and
`cancellation_identity` for the σ-weighted cancellation, and
`ymMeasure_apply_toReal` / `gibbsCondMeasure_apply_toReal` for
the LHS/RHS reformulations. The main theorem `ymMeasure_isGibbs`
packages the DLR identity into the `IsGibbsMeasure` structure.

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

/-! ## Core Fubini helper for `gluedConfig`

Both `partitionFn_eq_integral_gibbsConditionalZ` and
`integral_indicator_w_fubini_link_split` are special cases of
a single identity: integrating any integrable function `F`
against the double `(productHaar × productHaar)`-measure
through `gluedConfig` equals integrating `F` against
`productHaar` directly.

The core fact is that `γ(uΛ, σ) := gluedConfig Λ uΛ σ` pushes
`productHaar × productHaar` forward to `productHaar`, proven
below as `glue_measurePreserving` via `Measure.pi_eq` on
boxes. -/

/-- The pushforward of `productHaar × productHaar` under
`(uΛ, σ) ↦ gluedConfig Λ uΛ σ` is `productHaar`.

Proven directly via `Measure.pi_eq`: the preimage of a box
`Set.pi univ s` factors as `A ×ˢ B` where `A` constrains the
Λ-indexed coordinates and `B` the Λᶜ-indexed ones. Each partial
box's measure is a product of `haarG(s e)` over the constrained
coordinates, and the two products recombine via
`Finset.prod_mul_distrib` into the full-box product measure. -/
theorem glue_measurePreserving (Λ : Finset (LatticeLink d N)) :
    MeasurePreserving
      (fun p : (LatticeLink d N → G) × (LatticeLink d N → G) =>
        gluedConfig G d N Λ p.1 p.2)
      ((productHaar G d N).prod (productHaar G d N))
      (productHaar G d N) := by
  classical
  set γ : (LatticeLink d N → G) × (LatticeLink d N → G) → GaugeConnection G d N :=
    fun p => gluedConfig G d N Λ p.1 p.2 with hγ_def
  -- Step 1: γ is measurable.
  have hγ_meas : Measurable γ := by
    apply measurable_pi_iff.mpr
    intro e
    by_cases he : e ∈ Λ
    · have : (fun p => γ p e) = fun p => p.1 e := by
        funext p; simp [γ, gluedConfig, he]
      rw [this]
      exact (measurable_pi_apply e).comp measurable_fst
    · have : (fun p => γ p e) = fun p => p.2 e := by
        funext p; simp [γ, gluedConfig, he]
      rw [this]
      exact (measurable_pi_apply e).comp measurable_snd
  refine ⟨hγ_meas, ?_⟩
  -- Step 2: The pushforward equals productHaar. Prove via pi_eq on boxes.
  show Measure.map γ
      ((productHaar G d N).prod (productHaar G d N)) = productHaar G d N
  unfold productHaar
  refine (Measure.pi_eq (fun s hs => ?_)).symm
  -- For a box `Set.pi univ s`, compute the pushforward value.
  -- Preimage: {p | ∀ e, γ p e ∈ s e}
  --        = {p.1 | ∀ e ∈ Λ, p.1 e ∈ s e} ×ˢ {p.2 | ∀ e ∉ Λ, p.2 e ∈ s e}
  set aΛ : LatticeLink d N → Set G := fun e => if e ∈ Λ then s e else Set.univ
  set aΛc : LatticeLink d N → Set G := fun e => if e ∈ Λ then Set.univ else s e
  have haΛ_meas : ∀ e, MeasurableSet (aΛ e) := by
    intro e; simp only [aΛ]; split_ifs
    · exact hs e
    · exact MeasurableSet.univ
  have haΛc_meas : ∀ e, MeasurableSet (aΛc e) := by
    intro e; simp only [aΛc]; split_ifs
    · exact MeasurableSet.univ
    · exact hs e
  have hpre :
      γ ⁻¹' Set.pi Set.univ s =
        (Set.pi Set.univ aΛ) ×ˢ (Set.pi Set.univ aΛc) := by
    ext ⟨u, σ⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_prod, aΛ, aΛc]
    constructor
    · intro h
      refine ⟨fun e => ?_, fun e => ?_⟩
      · by_cases he : e ∈ Λ
        · simp [he]; simpa [γ, gluedConfig, he] using h e
        · simp [he]
      · by_cases he : e ∈ Λ
        · simp [he]
        · simp [he]; simpa [γ, gluedConfig, he] using h e
    · rintro ⟨hA, hB⟩ e
      by_cases he : e ∈ Λ
      · have := hA e; simp [he] at this; simpa [γ, gluedConfig, he]
      · have := hB e; simp [he] at this; simpa [γ, gluedConfig, he]
  -- Compute (map γ (ph × ph))(box) = (ph × ph)(preimage)
  calc (Measure.map γ
          ((Measure.pi fun _ : LatticeLink d N => haarG G).prod
           (Measure.pi fun _ : LatticeLink d N => haarG G))) (Set.univ.pi s)
      = ((Measure.pi fun _ : LatticeLink d N => haarG G).prod
          (Measure.pi fun _ : LatticeLink d N => haarG G))
          (γ ⁻¹' Set.univ.pi s) := by
        exact Measure.map_apply hγ_meas (MeasurableSet.univ_pi hs)
    _ = ((Measure.pi fun _ : LatticeLink d N => haarG G).prod
          (Measure.pi fun _ : LatticeLink d N => haarG G))
          ((Set.pi Set.univ aΛ) ×ˢ (Set.pi Set.univ aΛc)) := by rw [hpre]
    _ = (Measure.pi fun _ : LatticeLink d N => haarG G) (Set.pi Set.univ aΛ)
        * (Measure.pi fun _ : LatticeLink d N => haarG G) (Set.pi Set.univ aΛc) :=
        Measure.prod_prod _ _
    _ = (∏ e, haarG G (aΛ e)) * (∏ e, haarG G (aΛc e)) := by
        rw [Measure.pi_pi, Measure.pi_pi]
    _ = ∏ e, haarG G (s e) := by
        rw [← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl (fun e _ => ?_)
        by_cases he : e ∈ Λ
        · simp [aΛ, aΛc, he, HasHaarProbability.isProb.measure_univ]
        · simp [aΛ, aΛc, he, HasHaarProbability.isProb.measure_univ]

/-- Reduces the double integral through `glue` to a single
integral over `productHaar`, given `glue_measurePreserving`.

Uses `integral_map` for change-of-variables through the
measure-preserving map `γ(u, σ) := glue Λ u σ`, then
`integral_prod_symm` for Fubini swap. -/
theorem integral_glue_split_eq
    (Λ : Finset (LatticeLink d N))
    (F : GaugeConnection G d N → ℝ)
    (hF_meas : Measurable F)
    (hF_int : Integrable F (productHaar G d N)) :
    ∫ σ, (∫ uΛ, F (gluedConfig G d N Λ uΛ σ)
            ∂(productHaar G d N)) ∂(productHaar G d N)
    = ∫ U, F U ∂(productHaar G d N) := by
  set γ : (LatticeLink d N → G) × (LatticeLink d N → G) → GaugeConnection G d N :=
    fun p => gluedConfig G d N Λ p.1 p.2 with hγ_def
  have hMP : MeasurePreserving γ
      ((productHaar G d N).prod (productHaar G d N))
      (productHaar G d N) :=
    glue_measurePreserving G d N Λ
  have hmap_eq :
      (productHaar G d N) =
        Measure.map γ ((productHaar G d N).prod (productHaar G d N)) :=
    hMP.map_eq.symm
  have hF_aesm :
      AEStronglyMeasurable F
        (Measure.map γ ((productHaar G d N).prod (productHaar G d N))) := by
    rw [← hmap_eq]; exact hF_int.aestronglyMeasurable
  have hchg :
      ∫ U, F U ∂(productHaar G d N)
        = ∫ p, F (γ p) ∂((productHaar G d N).prod (productHaar G d N)) := by
    conv_lhs => rw [hmap_eq]
    exact integral_map hMP.measurable.aemeasurable hF_aesm
  have hFγ_int :
      Integrable (fun p => F (γ p))
        ((productHaar G d N).prod (productHaar G d N)) := by
    have : Integrable F (Measure.map γ
        ((productHaar G d N).prod (productHaar G d N))) := by
      rw [← hmap_eq]; exact hF_int
    exact (integrable_map_measure hF_aesm hMP.measurable.aemeasurable).mp this
  have hfub :
      ∫ p, F (γ p) ∂((productHaar G d N).prod (productHaar G d N))
        = ∫ σ, (∫ uΛ, F (gluedConfig G d N Λ uΛ σ)
              ∂(productHaar G d N)) ∂(productHaar G d N) :=
    MeasureTheory.integral_prod_symm _ hFγ_int
  rw [← hfub, ← hchg]

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
    (β : ℝ) (Λ : Finset (LatticeLink d N))
    (hw_meas : Measurable (fun U => boltzmannWeight G n d N β U plaq))
    (hw_int : Integrable (fun U => boltzmannWeight G n d N β U plaq)
        (productHaar G d N)) :
    partitionFn G n d N β plaq =
      ∫ σ, gibbsConditionalZ G n d N plaq β Λ σ ∂(productHaar G d N) := by
  unfold partitionFn gibbsConditionalZ gibbsConditionalWeight
  -- The RHS has an inner integral over `Measure.pi (fun _ => haarG G)`,
  -- which definitionally equals `productHaar G d N`.
  exact (integral_glue_split_eq G d N Λ
    (fun U => boltzmannWeight G n d N β U plaq) hw_meas hw_int).symm

/-- **Identity A.** For any observable `h` that depends on `σ`
only through `σ|_Λᶜ`:
```
∫ σ h(σ) · Z_Λ(σ) ∂productHaar = ∫ U h(U) · w(U) ∂productHaar
```

Direct consequence of `integral_glue_split_eq` applied to
`F(U) := h(U) · w(U)`: the inner integral over `uΛ` produces
`h(σ) · gibbsConditionalZ Λ σ` (since `h` is constant along the
glued `Λ`-fibre). -/
theorem integral_smul_condZ_eq_integral_smul_w
    (β : ℝ) (Λ : Finset (LatticeLink d N))
    (h : GaugeConnection G d N → ℝ)
    (hh_outside : ∀ (uΛ : LatticeLink d N → G)
        (σ : GaugeConnection G d N),
        h (gluedConfig G d N Λ uΛ σ) = h σ)
    (hh_meas : Measurable h)
    (hw_meas : Measurable (fun U => boltzmannWeight G n d N β U plaq))
    (hhw_int : Integrable
        (fun U => h U * boltzmannWeight G n d N β U plaq)
        (productHaar G d N)) :
    ∫ σ, h σ * gibbsConditionalZ G n d N plaq β Λ σ
        ∂(productHaar G d N) =
    ∫ U, h U * boltzmannWeight G n d N β U plaq
        ∂(productHaar G d N) := by
  have hhw_meas : Measurable
      (fun U => h U * boltzmannWeight G n d N β U plaq) :=
    hh_meas.mul hw_meas
  have hsplit := integral_glue_split_eq G d N Λ
    (fun U => h U * boltzmannWeight G n d N β U plaq)
    hhw_meas hhw_int
  -- LHS via split: outer σ integral of inner `h · w` through glue.
  -- The integrand `h(glue uΛ σ) · w(glue uΛ σ) = h(σ) · w(glue uΛ σ)`
  -- since h is constant along glue fibres.
  -- Key step: for fixed σ, the inner integral equals h(σ) · Z_Λ(σ).
  have hrewrite :
      ∀ σ : GaugeConnection G d N,
        (∫ uΛ, h (gluedConfig G d N Λ uΛ σ)
                * boltzmannWeight G n d N β (gluedConfig G d N Λ uΛ σ) plaq
              ∂(productHaar G d N))
        = h σ * gibbsConditionalZ G n d N plaq β Λ σ := by
    intro σ
    -- Substitute h(glue _ σ) = h(σ) inside the integrand via integral_congr.
    have heq :
        ∫ uΛ, h (gluedConfig G d N Λ uΛ σ)
                * boltzmannWeight G n d N β (gluedConfig G d N Λ uΛ σ) plaq
            ∂(productHaar G d N) =
        ∫ uΛ, h σ
                * boltzmannWeight G n d N β (gluedConfig G d N Λ uΛ σ) plaq
            ∂(productHaar G d N) := by
      refine integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro uΛ
      show h (gluedConfig G d N Λ uΛ σ)
              * boltzmannWeight G n d N β (gluedConfig G d N Λ uΛ σ) plaq
            = h σ
              * boltzmannWeight G n d N β (gluedConfig G d N Λ uΛ σ) plaq
      rw [hh_outside uΛ σ]
    rw [heq, MeasureTheory.integral_const_mul]
    rfl
  calc ∫ σ, h σ * gibbsConditionalZ G n d N plaq β Λ σ
          ∂(productHaar G d N)
      = ∫ σ, (∫ uΛ, h (gluedConfig G d N Λ uΛ σ)
                    * boltzmannWeight G n d N β
                        (gluedConfig G d N Λ uΛ σ) plaq
                  ∂(productHaar G d N)) ∂(productHaar G d N) := by
        refine integral_congr_ae (Filter.Eventually.of_forall ?_)
        intro σ; exact (hrewrite σ).symm
    _ = ∫ U, h U * boltzmannWeight G n d N β U plaq
            ∂(productHaar G d N) := hsplit

/-- **S2 — Cancellation identity.** For any `h` that depends on
`σ` only through `σ|_Λᶜ`, the Boltzmann-density-normalized σ-average
collapses to the plain average:
```
∫ σ, h(σ) · w(σ) / Z_Λ(σ) ∂productHaar = ∫ σ, h(σ) ∂productHaar
```

Proof: apply Identity A with `h' := h / Z_Λ`. Then
`h'(σ) · Z_Λ(σ) = h(σ)` pointwise (when `Z_Λ > 0`), and
`h'(U) · w(U) = h(U) · w(U) / Z_Λ(U)`, giving the identity. -/
theorem cancellation_identity
    (β : ℝ) (Λ : Finset (LatticeLink d N))
    (h : GaugeConnection G d N → ℝ)
    (hh_outside : ∀ (uΛ : LatticeLink d N → G)
        (σ : GaugeConnection G d N),
        h (gluedConfig G d N Λ uΛ σ) = h σ)
    (hh_meas : Measurable h)
    (hw_meas : Measurable (fun U => boltzmannWeight G n d N β U plaq))
    (hZ_pos : ∀ σ : GaugeConnection G d N,
        0 < gibbsConditionalZ G n d N plaq β Λ σ)
    (hZ_meas : Measurable (fun σ : GaugeConnection G d N =>
        gibbsConditionalZ G n d N plaq β Λ σ))
    (hhw_over_Z_int : Integrable
        (fun U : GaugeConnection G d N => h U / gibbsConditionalZ G n d N plaq β Λ U
              * boltzmannWeight G n d N β U plaq)
        (productHaar G d N)) :
    ∫ σ, h σ * boltzmannWeight G n d N β σ plaq
          / gibbsConditionalZ G n d N plaq β Λ σ
        ∂(productHaar G d N) =
    ∫ σ, h σ ∂(productHaar G d N) := by
  -- `h' := h / Z_Λ` respects `gluedConfig` since both `h` and `Z_Λ` do.
  have hh'_outside : ∀ (uΛ : LatticeLink d N → G)
      (σ : GaugeConnection G d N),
      (fun τ => h τ / gibbsConditionalZ G n d N plaq β Λ τ)
          (gluedConfig G d N Λ uΛ σ)
      = (fun τ => h τ / gibbsConditionalZ G n d N plaq β Λ τ) σ := by
    intro uΛ σ
    show h (gluedConfig G d N Λ uΛ σ) /
            gibbsConditionalZ G n d N plaq β Λ (gluedConfig G d N Λ uΛ σ)
        = h σ / gibbsConditionalZ G n d N plaq β Λ σ
    rw [hh_outside uΛ σ]
    congr 1
    exact gibbsConditionalZ_eq_of_agrees_outside G n d N plaq β Λ
      (gluedConfig G d N Λ uΛ σ) σ (fun e he =>
        gluedConfig_eq_outside G d N Λ uΛ σ e he)
  have hh'_meas :
      Measurable (fun σ : GaugeConnection G d N =>
        h σ / gibbsConditionalZ G n d N plaq β Λ σ) :=
    hh_meas.div hZ_meas
  -- Apply Identity A with h' = h/Z.
  have hA := integral_smul_condZ_eq_integral_smul_w G n d N plaq β Λ
    (fun σ => h σ / gibbsConditionalZ G n d N plaq β Λ σ)
    hh'_outside hh'_meas hw_meas hhw_over_Z_int
  -- Simplify the LHS of Identity A: (h/Z) · Z = h (since Z > 0).
  have hLHS_simp :
      ∫ σ, h σ / gibbsConditionalZ G n d N plaq β Λ σ
            * gibbsConditionalZ G n d N plaq β Λ σ
          ∂(productHaar G d N)
        = ∫ σ, h σ ∂(productHaar G d N) := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro σ
    field_simp [(hZ_pos σ).ne']
  rw [hLHS_simp] at hA
  -- Now hA : ∫ σ h σ = ∫ U (h U / Z U) · w U.
  -- Rewrite our goal's LHS to the shape `(h/Z) · w` matching hA's RHS.
  have hgoal :
      ∫ σ, h σ * boltzmannWeight G n d N β σ plaq
            / gibbsConditionalZ G n d N plaq β Λ σ
          ∂(productHaar G d N)
        = ∫ σ, h σ / gibbsConditionalZ G n d N plaq β Λ σ
              * boltzmannWeight G n d N β σ plaq
            ∂(productHaar G d N) := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro σ; ring
  rw [hgoal]
  exact hA.symm

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
    (A : Set (GaugeConnection G d N)) (hA : MeasurableSet A)
    (hw_meas : Measurable (fun U => boltzmannWeight G n d N β U plaq))
    (hFA_int : Integrable
        (Set.indicator A (fun U => boltzmannWeight G n d N β U plaq))
        (productHaar G d N)) :
    ∫ U, Set.indicator A (fun U => boltzmannWeight G n d N β U plaq) U
        ∂(productHaar G d N) =
    ∫ σ, (∫ uΛ,
        Set.indicator A
          (fun U => boltzmannWeight G n d N β U plaq)
          (gluedConfig G d N Λ uΛ σ)
        ∂(Measure.pi (fun _ : LatticeLink d N => haarG G)))
      ∂(productHaar G d N) := by
  have hFA_meas : Measurable
      (Set.indicator A (fun U => boltzmannWeight G n d N β U plaq)) :=
    (hw_meas.indicator hA)
  exact (integral_glue_split_eq G d N Λ
    (Set.indicator A (fun U => boltzmannWeight G n d N β U plaq))
    hFA_meas hFA_int).symm

/-- Reformulation of `(ymMeasure A).toReal` as an explicit
`(1/Z)·∫ 1_A · w dph` integral. Follows from
`ymExpect_eq_integral_ymMeasure` applied to the indicator `1_A`. -/
theorem ymMeasure_apply_toReal
    (β : ℝ) (hβ : 0 ≤ β)
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hIntegrable_w : Integrable (fun U => boltzmannWeight G n d N β U plaq)
        (productHaar G d N))
    (hw_meas : Measurable (fun U => boltzmannWeight G n d N β U plaq))
    (A : Set (GaugeConnection G d N)) (hA : MeasurableSet A) :
    ((ymMeasure G n d N β plaq) A).toReal =
      (∫ U, Set.indicator A
              (fun U => boltzmannWeight G n d N β U plaq) U
          ∂(productHaar G d N))
        / partitionFn G n d N β plaq := by
  haveI : IsProbabilityMeasure (ymMeasure G n d N β plaq) :=
    ymMeasure_isProbabilityMeasure G n d N β hβ plaq
      hTrace_upper hTrace_lower hIntegrable_w hw_meas
  -- (ymMeasure A).toReal = ∫ 1_A ∂ymMeasure.
  have h1 : ((ymMeasure G n d N β plaq) A).toReal
      = ∫ U, Set.indicator A (fun _ => (1 : ℝ)) U ∂(ymMeasure G n d N β plaq) := by
    rw [show (fun _ : GaugeConnection G d N => (1 : ℝ)) = (1 : GaugeConnection G d N → ℝ)
        from rfl,
      integral_indicator_one hA]
    rfl
  -- ∫ 1_A ∂ymMeasure = ymExpect 1_A via the bridge.
  have hind_meas : Measurable (Set.indicator A (fun _ : GaugeConnection G d N => (1 : ℝ))) :=
    measurable_const.indicator hA
  have hindw_int : Integrable
      (fun U : GaugeConnection G d N =>
        Set.indicator A (fun _ => (1 : ℝ)) U
        * boltzmannWeight G n d N β U plaq)
      (productHaar G d N) := by
    -- Bounded by |w| everywhere (indicator in [0,1]); reduce to hIntegrable_w.
    refine hIntegrable_w.mono (hind_meas.mul hw_meas).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall ?_
    intro U
    simp only [Real.norm_eq_abs]
    rw [abs_mul]
    refine mul_le_of_le_one_left (abs_nonneg _) ?_
    by_cases hU : U ∈ A
    · simp [Set.indicator_of_mem hU]
    · simp [Set.indicator_of_notMem hU]
  have h2 := ymExpect_eq_integral_ymMeasure G n d N β hβ plaq
    hTrace_upper hTrace_lower hIntegrable_w hw_meas
    (Set.indicator A (fun _ => (1 : ℝ))) hind_meas hindw_int
  -- ymExpect 1_A = (∫ 1_A · w dph) / Z by definition.
  unfold ymExpect at h2
  rw [h1, ← h2]
  -- The integrand `1_A · w` simplifies to Set.indicator A w.
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall ?_)
  intro U
  by_cases hU : U ∈ A
  · simp [Set.indicator_of_mem hU]
  · simp [Set.indicator_of_notMem hU]

/-- **Helper for DLR identity.** Explicit formula for `(gibbsCondMeasure Λ σ A).toReal`.

Unfolds `gibbsCondMeasure = ((ph).map (glue σ)).withDensity (ofReal (w/Z(σ)))`
through `withDensity_apply`, `Measure.restrict_map`, `lintegral_map`, and
`ofReal_integral_eq_lintegral_ofReal`. -/
theorem gibbsCondMeasure_apply_toReal
    (β : ℝ)
    (hw_meas : Measurable (fun U => boltzmannWeight G n d N β U plaq))
    (Λ : Finset (LatticeLink d N))
    (σ : GaugeConnection G d N)
    (hZ_pos : 0 < gibbsConditionalZ G n d N plaq β Λ σ)
    (hw_integrable_cond :
        Integrable (fun uΛ : LatticeLink d N → G =>
            gibbsConditionalWeight G n d N plaq β Λ σ uΛ)
          (Measure.pi (fun _ : LatticeLink d N => haarG G)))
    (A : Set (GaugeConnection G d N)) (hA : MeasurableSet A) :
    (gibbsCondMeasure G n d N plaq β Λ σ A).toReal =
      (∫ uΛ, Set.indicator A (fun U => boltzmannWeight G n d N β U plaq)
                (gluedConfig G d N Λ uΛ σ)
           ∂(productHaar G d N))
        / gibbsConditionalZ G n d N plaq β Λ σ := by
  set Z := gibbsConditionalZ G n d N plaq β Λ σ with hZ_def
  set glue : (LatticeLink d N → G) → GaugeConnection G d N :=
    fun uΛ => gluedConfig G d N Λ uΛ σ with hglue_def
  have hglue_meas : Measurable glue := measurable_gluedConfig G d N Λ σ
  have hZ_ne : Z ≠ 0 := hZ_pos.ne'
  have hZ_inv_nn : (0 : ℝ) ≤ 1 / Z := by positivity
  -- Step 1. Unfold gibbsCondMeasure and apply withDensity_apply.
  have hstep1 :
      gibbsCondMeasure G n d N plaq β Λ σ A =
        ∫⁻ U in A, ENNReal.ofReal
            (boltzmannWeight G n d N β U plaq / Z) ∂((productHaar G d N).map glue) := by
    unfold gibbsCondMeasure
    exact withDensity_apply _ hA
  -- Step 2. Turn ∫⁻ U in A, f U ∂((ph).map glue) into ∫⁻ uΛ in glue⁻¹ A, f (glue uΛ) ∂ph.
  have hf_meas : Measurable (fun U : GaugeConnection G d N =>
      ENNReal.ofReal (boltzmannWeight G n d N β U plaq / Z)) :=
    (hw_meas.div_const Z).ennreal_ofReal
  have hstep2 :
      (∫⁻ U in A, ENNReal.ofReal
            (boltzmannWeight G n d N β U plaq / Z) ∂((productHaar G d N).map glue))
        = ∫⁻ uΛ : LatticeLink d N → G in glue ⁻¹' A,
              ENNReal.ofReal (boltzmannWeight G n d N β (glue uΛ) plaq / Z)
            ∂(Measure.pi (fun _ : LatticeLink d N => haarG G)) := by
    exact setLIntegral_map hA hf_meas hglue_meas
  -- Step 3. Convert set-integral to indicator-integral.
  have hpre_meas : MeasurableSet (glue ⁻¹' A) := hglue_meas hA
  have hstep3 :
      (∫⁻ uΛ : LatticeLink d N → G in glue ⁻¹' A,
            ENNReal.ofReal (boltzmannWeight G n d N β (glue uΛ) plaq / Z)
          ∂(Measure.pi (fun _ : LatticeLink d N => haarG G)))
        = ∫⁻ uΛ : LatticeLink d N → G, Set.indicator (glue ⁻¹' A)
              (fun uΛ => ENNReal.ofReal
                  (boltzmannWeight G n d N β (glue uΛ) plaq / Z)) uΛ
            ∂(Measure.pi (fun _ : LatticeLink d N => haarG G)) := by
    rw [← lintegral_indicator hpre_meas]
  -- Step 4. The indicator of glue⁻¹ A through ofReal equals ofReal of the real indicator.
  have hstep4 :
      (fun uΛ => Set.indicator (glue ⁻¹' A)
            (fun uΛ => ENNReal.ofReal
                (boltzmannWeight G n d N β (glue uΛ) plaq / Z)) uΛ)
        = (fun uΛ => ENNReal.ofReal
            (Set.indicator A
              (fun U => boltzmannWeight G n d N β U plaq) (glue uΛ) / Z)) := by
    funext uΛ
    by_cases huΛ : uΛ ∈ glue ⁻¹' A
    · have hglueA : glue uΛ ∈ A := huΛ
      rw [Set.indicator_of_mem huΛ, Set.indicator_of_mem hglueA]
    · have hglueA : glue uΛ ∉ A := huΛ
      rw [Set.indicator_of_notMem huΛ, Set.indicator_of_notMem hglueA]
      simp [ENNReal.ofReal_zero]
  -- Step 5. Convert lintegral of ofReal to ofReal of integral.
  -- Prepare the real-valued integrand and its integrability/nonneg.
  let realInt : (LatticeLink d N → G) → ℝ := fun uΛ =>
    Set.indicator A (fun U => boltzmannWeight G n d N β U plaq) (glue uΛ) / Z
  have hreal_nn : ∀ uΛ, 0 ≤ realInt uΛ := by
    intro uΛ
    have hind_nn : 0 ≤ Set.indicator A
        (fun U => boltzmannWeight G n d N β U plaq) (glue uΛ) := by
      by_cases huΛ : glue uΛ ∈ A
      · rw [Set.indicator_of_mem huΛ]
        exact (boltzmannWeight_pos G n d N β _ plaq).le
      · rw [Set.indicator_of_notMem huΛ]
    exact div_nonneg hind_nn hZ_pos.le
  -- Integrability of realInt: bounded by w (glue uΛ)/Z = gibbsConditionalWeight/Z.
  have hind_meas : Measurable
      (fun U : GaugeConnection G d N =>
        Set.indicator A (fun U => boltzmannWeight G n d N β U plaq) U) :=
    hw_meas.indicator hA
  have hind_comp_meas : Measurable (fun uΛ : LatticeLink d N → G =>
      Set.indicator A (fun U => boltzmannWeight G n d N β U plaq) (glue uΛ)) :=
    hind_meas.comp hglue_meas
  have hrealInt_meas : Measurable realInt := hind_comp_meas.div_const _
  -- Integrability of `gibbsConditionalWeight/Z` on Measure.pi = productHaar.
  have hw_comp_int : Integrable (fun uΛ : LatticeLink d N → G =>
      gibbsConditionalWeight G n d N plaq β Λ σ uΛ) (productHaar G d N) := by
    unfold productHaar; exact hw_integrable_cond
  have hwZ_int : Integrable (fun uΛ : LatticeLink d N → G =>
      gibbsConditionalWeight G n d N plaq β Λ σ uΛ / Z) (productHaar G d N) :=
    hw_comp_int.div_const Z
  have hrealInt_int : Integrable realInt (productHaar G d N) := by
    refine hwZ_int.mono hrealInt_meas.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall ?_
    intro uΛ
    simp only [Real.norm_eq_abs, realInt]
    have hnonneg : 0 ≤ gibbsConditionalWeight G n d N plaq β Λ σ uΛ / Z := by
      unfold gibbsConditionalWeight
      exact div_nonneg (boltzmannWeight_pos G n d N β _ plaq).le hZ_pos.le
    rw [abs_of_nonneg hnonneg]
    have hind_bound :
        Set.indicator A (fun U => boltzmannWeight G n d N β U plaq) (glue uΛ)
          ≤ gibbsConditionalWeight G n d N plaq β Λ σ uΛ := by
      unfold gibbsConditionalWeight
      by_cases huΛ : glue uΛ ∈ A
      · rw [Set.indicator_of_mem huΛ]
      · rw [Set.indicator_of_notMem huΛ]
        exact (boltzmannWeight_pos G n d N β _ plaq).le
    have hind_nn : 0 ≤ Set.indicator A
        (fun U => boltzmannWeight G n d N β U plaq) (glue uΛ) := by
      by_cases huΛ : glue uΛ ∈ A
      · rw [Set.indicator_of_mem huΛ]
        exact (boltzmannWeight_pos G n d N β _ plaq).le
      · rw [Set.indicator_of_notMem huΛ]
    rw [abs_of_nonneg (div_nonneg hind_nn hZ_pos.le)]
    exact div_le_div_of_nonneg_right hind_bound hZ_pos.le
  -- Now apply ofReal_integral_eq_lintegral_ofReal (backward).
  have hstep5 :
      (∫⁻ uΛ, ENNReal.ofReal (realInt uΛ) ∂(productHaar G d N))
        = ENNReal.ofReal (∫ uΛ, realInt uΛ ∂(productHaar G d N)) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hrealInt_int
      (Filter.Eventually.of_forall hreal_nn)).symm
  -- Chain the steps and take toReal.
  rw [hstep1, hstep2, hstep3, hstep4]
  change
    (∫⁻ uΛ, ENNReal.ofReal (realInt uΛ) ∂(productHaar G d N)).toReal = _
  rw [hstep5]
  rw [ENNReal.toReal_ofReal (by
    -- ∫ realInt ≥ 0.
    exact integral_nonneg hreal_nn)]
  -- Finally divide out the constant 1/Z (or Z).
  show (∫ uΛ, realInt uΛ ∂(productHaar G d N)) = _
  show (∫ uΛ, Set.indicator A
            (fun U => boltzmannWeight G n d N β U plaq) (glue uΛ) / Z
          ∂(productHaar G d N)) = _
  rw [integral_div]

/-- **Main DLR identity: `ymMeasure` satisfies DLR for `ymGibbsSpec`.**

For every finite `Λ` and measurable `A`:
`(ymMeasure A).toReal = ∫ σ, (gibbsCondMeasure Λ σ A).toReal ∂ymMeasure`.

### Proof strategy

LHS: unfold `ymMeasure = ph.withDensity (ofReal (w/Z))` using
`integral_withDensity_eq_integral_toReal_smul`:
  `(ymMeasure A).toReal = ∫ U, 1_A(U) · (w(U)/Z) ∂ph
                       = (1/Z) · ∫ U, 1_A(U) · w(U) ∂ph`

RHS: unfold `gibbsCondMeasure Λ σ = (ph.map (glue Λ · σ)).withDensity
(ofReal (w/Z(σ)))` using `withDensity_apply` + `lintegral_map`:
  `(gibbsCondMeasure Λ σ A).toReal
    = (1/Z(σ)) · ∫ uΛ, 1_A(glue Λ uΛ σ) · w(glue Λ uΛ σ) ∂ph`

Outer σ integral under `ymMeasure = ph.withDensity (w/Z)`:
  `∫ σ (ν_σ A).toReal ∂ymMeasure
    = (1/Z) · ∫ σ, (w(σ)/Z(σ)) · [inner(σ)] ∂ph`
where `inner(σ) := ∫ uΛ, 1_A(glue Λ uΛ σ) · w(glue Λ uΛ σ) ∂ph`.

Reducing LHS = RHS then reduces to the **cancellation identity**:
  `∫ σ, (w(σ)/Z(σ)) · inner(σ) ∂ph = ∫ σ, inner(σ) ∂ph`
since RHS via `integral_indicator_w_fubini_link_split` equals
`∫ U 1_A(U)·w(U) ∂ph`.

### Assembly

- `ymMeasure_apply_toReal`: `(ymMeasure A).toReal = (1/Z) · ∫ U 1_A·w ∂ph`.
- `gibbsCondMeasure_apply_toReal`: same for `(ν_σ A).toReal` via
  `withDensity_apply` + `lintegral_map` + `ofReal_integral_eq_lintegral_ofReal`.
- `ymExpect_eq_integral_ymMeasure` converts the σ-outer integral
  against `ymMeasure` into the quotient form.
- `cancellation_identity` (with `h := inner`) collapses the
  `w(σ)/Z_Λ(σ)` factor.
- `integral_indicator_w_fubini_link_split` matches the two sides.

Hypotheses:
- `hβ`, `hTrace_lower`, `hTrace_upper` — for `Z > 0` and trace bounds
- `hIntegrable_w`, `hw_meas` — integrability/measurability of `w`
- `hZcond_pos` — conditional partition functions are positive
- `hw_integrable_cond` — conditional Boltzmann weight integrability
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
    (hZ_meas : Measurable (fun σ : GaugeConnection G d N =>
        gibbsConditionalZ G n d N plaq β Λ σ))
    (hinner_meas : ∀ (A : Set (GaugeConnection G d N)), MeasurableSet A →
        Measurable (fun σ : GaugeConnection G d N =>
          ∫ uΛ, Set.indicator A
              (fun U => boltzmannWeight G n d N β U plaq)
              (gluedConfig G d N Λ uΛ σ) ∂(productHaar G d N)))
    (hindA_fub_int : ∀ (A : Set (GaugeConnection G d N)), MeasurableSet A →
        Integrable
          (Set.indicator A (fun U => boltzmannWeight G n d N β U plaq))
          (productHaar G d N))
    (hinner_w_over_Z_int : ∀ (A : Set (GaugeConnection G d N)), MeasurableSet A →
        Integrable (fun σ : GaugeConnection G d N =>
            (∫ uΛ, Set.indicator A
                (fun U => boltzmannWeight G n d N β U plaq)
                (gluedConfig G d N Λ uΛ σ) ∂(productHaar G d N))
              / gibbsConditionalZ G n d N plaq β Λ σ
            * boltzmannWeight G n d N β σ plaq)
          (productHaar G d N))
    (A : Set (GaugeConnection G d N)) (hA : MeasurableSet A) :
    ((ymMeasure G n d N β plaq) A).toReal =
      ∫ σ, (gibbsCondMeasure G n d N plaq β Λ σ A).toReal
        ∂(ymMeasure G n d N β plaq) := by
  classical
  -- Setup common abbreviations.
  set w : GaugeConnection G d N → ℝ :=
    fun U => boltzmannWeight G n d N β U plaq with hw_def
  set Z : ℝ := partitionFn G n d N β plaq with hZ_def
  set Zσ : GaugeConnection G d N → ℝ :=
    fun σ => gibbsConditionalZ G n d N plaq β Λ σ with hZσ_def
  set indA : GaugeConnection G d N → ℝ :=
    fun U => Set.indicator A w U with hindA_def
  set inner : GaugeConnection G d N → ℝ :=
    fun σ => ∫ uΛ, indA (gluedConfig G d N Λ uΛ σ) ∂(productHaar G d N)
    with hinner_def
  have hZ_pos : 0 < Z :=
    partitionFn_pos G n d N β hβ plaq hTrace_upper hTrace_lower hIntegrable_w
  have hZ_ne : Z ≠ 0 := hZ_pos.ne'
  have hZσ_pos : ∀ σ, 0 < Zσ σ := fun σ => hZcond_pos Λ σ
  -- Step A. LHS = (∫ U indA U ∂ph) / Z.
  have hLHS :
      ((ymMeasure G n d N β plaq) A).toReal =
        (∫ U, indA U ∂(productHaar G d N)) / Z := by
    exact ymMeasure_apply_toReal G n d N plaq β hβ hTrace_upper hTrace_lower
      hIntegrable_w hw_meas A hA
  -- Step B. Pointwise: (gibbsCondMeasure Λ σ A).toReal = inner σ / Zσ σ.
  have hpointwise : ∀ σ,
      (gibbsCondMeasure G n d N plaq β Λ σ A).toReal = inner σ / Zσ σ := by
    intro σ
    have := gibbsCondMeasure_apply_toReal G n d N plaq β hw_meas Λ σ
      (hZcond_pos Λ σ) (hw_integrable_cond Λ σ) A hA
    simpa [inner, indA, w, Zσ] using this
  -- Step C. Rewrite the RHS integrand.
  have hRHS_rewrite :
      (∫ σ, (gibbsCondMeasure G n d N plaq β Λ σ A).toReal
          ∂(ymMeasure G n d N β plaq))
        = ∫ σ, inner σ / Zσ σ ∂(ymMeasure G n d N β plaq) := by
    refine integral_congr_ae ?_
    exact Filter.Eventually.of_forall hpointwise
  -- Step D. Convert ymMeasure-integral to productHaar-integral via ymExpect.
  -- Set up measurability/integrability.
  have hZσ_meas : Measurable Zσ := hZ_meas
  have hZσ_ne : ∀ σ, Zσ σ ≠ 0 := fun σ => (hZσ_pos σ).ne'
  have hinner_meas' : Measurable inner := hinner_meas A hA
  have hinner_over_Zσ_meas : Measurable (fun σ => inner σ / Zσ σ) :=
    hinner_meas'.div hZσ_meas
  -- Integrability of (inner / Zσ) * w given as hypothesis.
  have hfw_int : Integrable
      (fun σ => (inner σ / Zσ σ) * w σ) (productHaar G d N) := by
    have := hinner_w_over_Z_int A hA
    simpa [inner, indA, w, Zσ] using this
  -- Apply ymExpect_eq_integral_ymMeasure.
  have hymExp :
      ymExpect G n d N β plaq (fun σ => inner σ / Zσ σ)
        = ∫ σ, inner σ / Zσ σ ∂(ymMeasure G n d N β plaq) :=
    ymExpect_eq_integral_ymMeasure G n d N β hβ plaq
      hTrace_upper hTrace_lower hIntegrable_w hw_meas
      (fun σ => inner σ / Zσ σ) hinner_over_Zσ_meas hfw_int
  -- Unfold ymExpect.
  have hRHS_unfold :
      (∫ σ, inner σ / Zσ σ ∂(ymMeasure G n d N β plaq))
        = (∫ σ, (inner σ / Zσ σ) * w σ ∂(productHaar G d N)) / Z := by
    rw [← hymExp]
    unfold ymExpect
    rfl
  -- Step E. Apply cancellation_identity with h := inner.
  -- inner respects glue: glue uΛ (glue vΛ σ) = glue ... with σ|_Λᶜ unchanged.
  have hinner_outside : ∀ (uΛ : LatticeLink d N → G) (σ : GaugeConnection G d N),
      inner (gluedConfig G d N Λ uΛ σ) = inner σ := by
    intro uΛ σ
    -- inner σ = ∫ vΛ, indA (glue vΛ σ) ∂ph.
    -- For any uΛ, gluedConfig Λ vΛ (gluedConfig Λ uΛ σ) = gluedConfig Λ vΛ σ
    -- because the inner glue is overwritten on Λ.
    have hglue_idemp : ∀ vΛ : LatticeLink d N → G,
        gluedConfig G d N Λ vΛ (gluedConfig G d N Λ uΛ σ)
          = gluedConfig G d N Λ vΛ σ := by
      intro vΛ
      funext e
      by_cases he : e ∈ Λ
      · simp [gluedConfig, he]
      · simp [gluedConfig, he]
    show (∫ vΛ, indA (gluedConfig G d N Λ vΛ (gluedConfig G d N Λ uΛ σ))
          ∂(productHaar G d N))
        = ∫ vΛ, indA (gluedConfig G d N Λ vΛ σ) ∂(productHaar G d N)
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro vΛ
    show indA (gluedConfig G d N Λ vΛ (gluedConfig G d N Λ uΛ σ))
        = indA (gluedConfig G d N Λ vΛ σ)
    rw [hglue_idemp vΛ]
  -- Rewrite hfw_int to shape `h · w / Z`.
  have hfw_int' : Integrable
      (fun U : GaugeConnection G d N =>
        inner U / gibbsConditionalZ G n d N plaq β Λ U
          * boltzmannWeight G n d N β U plaq)
      (productHaar G d N) := by
    simpa [Zσ, w] using hfw_int
  have hcanc :=
    cancellation_identity G n d N plaq β Λ inner hinner_outside hinner_meas'
      hw_meas (fun σ => hZσ_pos σ) hZσ_meas hfw_int'
  -- hcanc : ∫ σ, inner σ * w σ / Zσ σ ∂ph = ∫ σ, inner σ ∂ph.
  -- Massage: ∫ (inner σ / Zσ σ) * w σ = ∫ inner σ * w σ / Zσ σ.
  have hshape :
      (∫ σ, (inner σ / Zσ σ) * w σ ∂(productHaar G d N))
        = ∫ σ, inner σ * w σ / Zσ σ ∂(productHaar G d N) := by
    refine integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro σ; ring
  -- Step F. Apply integral_indicator_w_fubini_link_split.
  have hfubA :
      (∫ U, indA U ∂(productHaar G d N))
        = ∫ σ, (∫ uΛ, indA (gluedConfig G d N Λ uΛ σ)
                  ∂(Measure.pi (fun _ : LatticeLink d N => haarG G)))
              ∂(productHaar G d N) :=
    integral_indicator_w_fubini_link_split G n d N plaq β Λ A hA hw_meas
      (hindA_fub_int A hA)
  -- Assemble.
  rw [hRHS_rewrite, hRHS_unfold, hshape, hcanc]
  -- Goal: LHS_toReal = (∫ σ inner σ ∂ph) / Z.
  -- Via integral_indicator_w_fubini_link_split and inner's definition.
  rw [hLHS]
  -- Split the `/Z` and reduce to equality of integrals.
  have hinnerInt :
      (∫ σ, inner σ ∂(productHaar G d N))
        = ∫ U, indA U ∂(productHaar G d N) := by
    have hrewr :
        (fun σ : GaugeConnection G d N => inner σ)
          = fun σ : GaugeConnection G d N =>
              ∫ uΛ : LatticeLink d N → G,
                indA (gluedConfig G d N Λ uΛ σ)
                ∂(Measure.pi (fun _ : LatticeLink d N => haarG G)) := by
      funext σ; rfl
    -- Use hrewr on inner's shape, match hfubA.
    calc (∫ σ, inner σ ∂(productHaar G d N))
        = ∫ σ, (∫ uΛ : LatticeLink d N → G,
                  indA (gluedConfig G d N Λ uΛ σ)
                  ∂(Measure.pi (fun _ : LatticeLink d N => haarG G)))
              ∂(productHaar G d N) := by rw [hrewr]
      _ = ∫ U, indA U ∂(productHaar G d N) := hfubA.symm
  rw [hinnerInt]

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
    (hZcond_meas : ∀ Λ : Finset (LatticeLink d N),
        Measurable (fun σ : GaugeConnection G d N =>
          gibbsConditionalZ G n d N plaq β Λ σ))
    (hinner_meas : ∀ (Λ : Finset (LatticeLink d N))
        (A : Set (GaugeConnection G d N)), MeasurableSet A →
        Measurable (fun σ : GaugeConnection G d N =>
          ∫ uΛ, Set.indicator A
              (fun U => boltzmannWeight G n d N β U plaq)
              (gluedConfig G d N Λ uΛ σ) ∂(productHaar G d N)))
    (hindA_fub_int : ∀ (A : Set (GaugeConnection G d N)), MeasurableSet A →
        Integrable
          (Set.indicator A (fun U => boltzmannWeight G n d N β U plaq))
          (productHaar G d N))
    (hinner_w_over_Z_int : ∀ (Λ : Finset (LatticeLink d N))
        (A : Set (GaugeConnection G d N)), MeasurableSet A →
        Integrable (fun σ : GaugeConnection G d N =>
            (∫ uΛ, Set.indicator A
                (fun U => boltzmannWeight G n d N β U plaq)
                (gluedConfig G d N Λ uΛ σ) ∂(productHaar G d N))
              / gibbsConditionalZ G n d N plaq β Λ σ
            * boltzmannWeight G n d N β σ plaq)
          (productHaar G d N))
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
        hIntegrable_w hw_meas hZcond_pos hw_integrable_cond Λ
        (hZcond_meas Λ) (hinner_meas Λ) hindA_fub_int
        (hinner_w_over_Z_int Λ) A hA)

end
