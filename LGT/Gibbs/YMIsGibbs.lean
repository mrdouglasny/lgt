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

/-! ## Core Fubini helper for `gluedConfig`

Both `partitionFn_eq_integral_gibbsConditionalZ` and
`integral_indicator_w_fubini_link_split` are special cases of
the following identity: integrating any integrable function
`F` against the double `(productHaar × productHaar)`-measure
through `gluedConfig` equals integrating `F` against
`productHaar` directly.

Proof idea: the measurable map
`γ : (L → G) × (L → G) → (L → G)`,
`γ(uΛ, σ) := gluedConfig Λ uΛ σ` pushes
`productHaar ×ˢ productHaar` forward to `productHaar`.
Indeed, factoring `γ` through
`Φ := piEquivPiSubtypeProd (· ∈ Λ)` gives
`Φ ∘ γ = (u ↦ u|_Λ) × (σ ↦ σ|_Λᶜ)`, which pushes
`productHaar × productHaar` to `μΛ × μΛᶜ = Φ_* productHaar`.
Hence `γ_* (productHaar × productHaar) = productHaar`.

The proof is left as a sorry; the Lean realization requires
`Measure.pi_eq` or a chain of `MeasurePreserving.integral_comp'`
applications. -/
/-- The pushforward of `productHaar × productHaar` under
`(uΛ, σ) ↦ gluedConfig Λ uΛ σ` is `productHaar`.

Proof idea: factor `γ(u, σ) := glue Λ u σ` through the pi-split
equivalence `Φ := piEquivPiSubtypeProd (· ∈ Λ)`. Then
`Φ ∘ γ = (u, σ) ↦ (u|_Λ, σ|_Λᶜ)`. This "parallel projection"
pushes `ph × ph` to `μΛ × μΛᶜ = Φ_* ph`, hence γ_* (ph × ph) =
Φ⁻¹_* (μΛ × μΛᶜ) = ph.

Left as a sorry; the Lean realization requires either
`Measure.pi_eq` on boxes or a chain of `MeasurePreserving`
compositions through `piEquivPiSubtypeProd`. -/
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

### Required sub-lemmas (not yet proved)

**S1** (Fubini reduction of gibbsConditionalZ).
`gibbsConditionalZ Λ σ = ∫ σΛ : {e // e ∈ Λ} → G,
    w(Φ.symm (σΛ, σ|_Λᶜ)) dμΛ`
where `Φ := piEquivPiSubtypeProd (· ∈ Λ)`. Proof: `integral_glue_split_eq`
style, with `F = w` and integrating the σΛᶜ coordinate against μΛᶜ
(probability, so integrates to 1).

**S2** (Cancellation identity).
For any integrable `h : GaugeConnection → ℝ` depending only on σ|_Λᶜ:
`∫ σ, (w(σ)/gibbsConditionalZ Λ σ) · h(σ) ∂ph = ∫ σ, h(σ) ∂ph`.
Proof via `piEquivPiSubtypeProd` on σ + Fubini + S1.

**S3** (DLR assembly).
Combine S2 (with `h := inner`) and
`integral_indicator_w_fubini_link_split` to finish.

### Status

Left as a single sorry; the sub-lemmas S1/S2 would each add ~50
lines and can be written following the exact pattern of
`integral_glue_split_eq` / `glue_measurePreserving`.

Assumes:
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
    (A : Set (GaugeConnection G d N)) (hA : MeasurableSet A) :
    ((ymMeasure G n d N β plaq) A).toReal =
      ∫ σ, (gibbsCondMeasure G n d N plaq β Λ σ A).toReal
        ∂(ymMeasure G n d N β plaq) := by
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
