/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Yang-Mills as a Gibbs Specification

Encodes the (unfixed) Wilson lattice gauge theory as a
`MarkovSemigroups.Dobrushin.GibbsSpec` with sites = links and
spin space = compact gauge group G.

This bridges the lgt-specific definitions (GaugeConnection, Wilson
action) to the abstract Dobrushin uniqueness machinery, enabling
the d ≥ 3 mass gap proof.

Note: The measure uses the full product Haar on all links (no gauge
fixing applied to the Gibbs spec itself). Dobrushin's uniqueness
works directly for the unfixed measure at strong coupling. Gauge
invariance of the action ensures gauge-invariant observables have
well-defined expectations.

## Architecture

- Sites: `LatticeLink d N` (finite type)
- Spin space: G (compact gauge group with Haar measure)
- Configurations: `LatticeLink d N → G` ≡ `GaugeConnection G d N`

## Conditional distribution

For Λ ⊂ links and boundary σ:
  γ(Λ, σ)(A) = (1/Z_Λ(σ)) ∫_{U|_Λ} 𝟙_A(U) · exp(-S(U)) dHaar^Λ(U|_Λ)

where U agrees with σ outside Λ, integrated against product Haar
on Λ. The action S sums over plaquettes touching Λ.

## References

- Chatterjee (2026), §16.3
- markov-semigroups/Dobrushin/Specification.lean
-/

import LGT.MassGap.YMMeasure
import LGT.WilsonAction.GaugeInvariance
import MarkovSemigroups.Dobrushin.Specification

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open MeasureTheory

noncomputable section

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
variable [HasHaarProbability G]
variable (n d N : ℕ) [HasGaugeTrace G n] [Fintype (LatticeLink d N)]
variable [DecidableEq (LatticeLink d N)]

/-! ## Gluing configurations on Λ and Λᶜ -/

/-- Glue a Λ-config and a boundary σ into a full config. -/
def gluedConfig (Λ : Finset (LatticeLink d N))
    (uΛ : LatticeLink d N → G) (σ : GaugeConnection G d N) :
    GaugeConnection G d N :=
  fun e => if e ∈ Λ then uΛ e else σ e

/-- The glued config agrees with σ outside Λ. -/
theorem gluedConfig_eq_outside (Λ : Finset (LatticeLink d N))
    (uΛ : LatticeLink d N → G) (σ : GaugeConnection G d N)
    (e : LatticeLink d N) (he : e ∉ Λ) :
    gluedConfig G d N Λ uΛ σ e = σ e := by
  simp [gluedConfig, he]

/-- The glued config equals uΛ on Λ. -/
theorem gluedConfig_eq_inside (Λ : Finset (LatticeLink d N))
    (uΛ : LatticeLink d N → G) (σ : GaugeConnection G d N)
    (e : LatticeLink d N) (he : e ∈ Λ) :
    gluedConfig G d N Λ uΛ σ e = uΛ e := by
  simp [gluedConfig, he]

/-- The gluing map `uΛ ↦ gluedConfig Λ uΛ σ` is measurable.

On the product measurable space, the map is the pointwise if-then-else
between a (measurable) projection `uΛ ↦ uΛ e` and a constant `σ e`. -/
theorem measurable_gluedConfig (Λ : Finset (LatticeLink d N))
    (σ : GaugeConnection G d N) :
    Measurable (fun uΛ : LatticeLink d N → G => gluedConfig G d N Λ uΛ σ) := by
  refine measurable_pi_iff.2 (fun e => ?_)
  by_cases he : e ∈ Λ
  · -- For e ∈ Λ, the projection is `uΛ ↦ uΛ e`.
    have : (fun uΛ : LatticeLink d N → G => gluedConfig G d N Λ uΛ σ e) =
        (fun uΛ : LatticeLink d N → G => uΛ e) := by
      funext uΛ
      simp [gluedConfig, he]
    rw [this]
    exact measurable_pi_apply e
  · -- For e ∉ Λ, the projection is constant (equal to `σ e`).
    have : (fun uΛ : LatticeLink d N → G => gluedConfig G d N Λ uΛ σ e) =
        (fun _ : LatticeLink d N → G => σ e) := by
      funext uΛ
      simp [gluedConfig, he]
    rw [this]
    exact measurable_const

/-! ## Conditional Boltzmann weight and partition function

The conditional weight integrates the full Wilson Boltzmann weight
over Λ-configurations, with boundary fixed to σ on Λᶜ. -/

variable (plaq : Finset (LatticePlaquette d N))

/-- The conditional Boltzmann weight for a Λ-config given boundary σ.
This is exp(-S(U)) where U = glue(uΛ, σ). -/
def gibbsConditionalWeight (β : ℝ)
    (Λ : Finset (LatticeLink d N))
    (σ : GaugeConnection G d N)
    (uΛ : LatticeLink d N → G) : ℝ :=
  boltzmannWeight G n d N β (gluedConfig G d N Λ uΛ σ) plaq

/-- Conditional partition function: integrates the weight over Λ-configs. -/
def gibbsConditionalZ (β : ℝ)
    (Λ : Finset (LatticeLink d N))
    (σ : GaugeConnection G d N) : ℝ :=
  ∫ uΛ : LatticeLink d N → G,
    gibbsConditionalWeight G n d N plaq β Λ σ uΛ
    ∂(Measure.pi (fun _ : LatticeLink d N => haarG G))

/-! ## The YM Gibbs specification

The conditional distribution γ(Λ, σ) is obtained by:
1. taking the product Haar measure on `LatticeLink d N → G`,
2. pushing it forward through `glue σ : uΛ ↦ gluedConfig Λ uΛ σ`
   (so the resulting measure is supported on configurations
   agreeing with σ outside Λ),
3. reweighting by the normalized Boltzmann density
   `exp(-S(U)) / Z_Λ(σ)`.

This gives the DLR conditional Boltzmann distribution for Wilson
gauge theory restricted to the finite region Λ with boundary σ.

### Conditional probability measure

The structure axioms require:

- `isProb`: ∫ (w/Z) d(pushforward) = 1, i.e. Z/Z = 1.
- `consistent`: `gluedConfig Λ uΛ σ` only reads σ on `Λᶜ`, so the
  pushforward (and Boltzmann weight through it) depends on σ only
  outside Λ.
- `proper`: every point in the image of `glue σ` agrees with σ
  outside Λ, so the pushforward is concentrated on that set.
- `measurable_condDist`: σ ↦ γ(Λ,σ)(A) is measurable via
  measurability of the product-measure integral and Z(σ). -/

/-- The conditional Boltzmann measure on full configurations for region Λ
with boundary σ.

`((productHaar).map (glue σ)).withDensity (ENNReal.ofReal (w/Z))`.

The pushforward through `glue σ` places the measure on configurations
that agree with σ outside Λ; reweighting by `exp(-S)/Z` gives the
Boltzmann conditional. -/
def gibbsCondMeasure (β : ℝ)
    (Λ : Finset (LatticeLink d N))
    (σ : GaugeConnection G d N) : Measure (GaugeConnection G d N) :=
  ((productHaar G d N).map
      (fun uΛ : LatticeLink d N → G => gluedConfig G d N Λ uΛ σ)).withDensity
    (fun U => ENNReal.ofReal
      (boltzmannWeight G n d N β U plaq /
        gibbsConditionalZ G n d N plaq β Λ σ))

/-- The "boundary-consistent" set `{τ | ∀ x ∉ Λ, τ x = σ x}` is measurable.

It is a finite intersection (over `x ∈ Λᶜ` inside the finite index type
`LatticeLink d N`) of preimages of singletons under measurable projections. -/
theorem measurableSet_agreesOutside (Λ : Finset (LatticeLink d N))
    (σ : GaugeConnection G d N) :
    MeasurableSet {τ : GaugeConnection G d N | ∀ x, x ∉ Λ → τ x = σ x} := by
  -- Rewrite as a finite intersection over x ∉ Λ.
  have hrewrite :
      {τ : GaugeConnection G d N | ∀ x, x ∉ Λ → τ x = σ x}
        = ⋂ x ∈ (Finset.univ \ Λ : Finset (LatticeLink d N)),
            {τ : GaugeConnection G d N | τ x = σ x} := by
    ext τ
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_sdiff,
      Finset.mem_univ, true_and, Finset.mem_coe]
  rw [hrewrite]
  refine MeasurableSet.biInter (Finset.univ \ Λ).countable_toSet ?_
  intro x _
  -- `{τ | τ x = σ x} = (eval x)⁻¹' {σ x}` is measurable since eval is
  -- measurable and `{σ x}` is closed (hence Borel-measurable) in T2 G.
  have hpre : {τ : GaugeConnection G d N | τ x = σ x}
      = (fun τ : GaugeConnection G d N => τ x) ⁻¹' {σ x} := by
    ext τ; simp
  rw [hpre]
  exact (measurable_pi_apply x) (measurableSet_singleton _)

/-- Auxiliary: under the pushforward `(productHaar).map (glue σ)`,
the complement of the "agrees with σ outside Λ" set has measure zero.

Indeed the preimage of that complement under `glue σ` is empty. -/
theorem map_glue_compl_eq_zero
    (Λ : Finset (LatticeLink d N))
    (σ : GaugeConnection G d N) :
    ((productHaar G d N).map
        (fun uΛ : LatticeLink d N → G => gluedConfig G d N Λ uΛ σ))
      {τ : GaugeConnection G d N | ∀ x, x ∉ Λ → τ x = σ x}ᶜ = 0 := by
  have hmeas := measurableSet_agreesOutside G d N Λ σ
  rw [Measure.map_apply (measurable_gluedConfig G d N Λ σ) hmeas.compl]
  -- The preimage is empty.
  have hpre : (fun uΛ : LatticeLink d N → G => gluedConfig G d N Λ uΛ σ) ⁻¹'
      {τ : GaugeConnection G d N | ∀ x, x ∉ Λ → τ x = σ x}ᶜ = ∅ := by
    ext uΛ
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq,
      Set.mem_empty_iff_false, iff_false, not_forall, not_not]
    intro ⟨x, hx, hne⟩
    exact hne (gluedConfig_eq_outside G d N Λ uΛ σ x hx)
  rw [hpre]; exact measure_empty

/-- Properness reduces to being a probability measure.

The pushforward `(productHaar).map (glue σ)` is concentrated on
`{τ | ∀ x ∉ Λ, τ x = σ x}` (its complement has measure 0, by
`map_glue_compl_eq_zero`), and `withDensity` is absolutely continuous
with respect to its base measure. So the complement of the set has
measure 0, and the measure of the set itself equals the total mass. -/
theorem gibbsCondMeasure_proper_of_total (β : ℝ)
    (Λ : Finset (LatticeLink d N))
    (σ : GaugeConnection G d N)
    (htot : gibbsCondMeasure G n d N plaq β Λ σ Set.univ = 1) :
    gibbsCondMeasure G n d N plaq β Λ σ
        {τ | ∀ x, x ∉ Λ → τ x = σ x} = 1 := by
  set S : Set (GaugeConnection G d N) := {τ | ∀ x, x ∉ Λ → τ x = σ x}
  have hS : MeasurableSet S := measurableSet_agreesOutside G d N Λ σ
  -- `(gibbsCondMeasure)(Sᶜ) = ∫⁻ a in Sᶜ, fdens a ∂(map glue)`.
  have hSc_zero : gibbsCondMeasure G n d N plaq β Λ σ Sᶜ = 0 := by
    unfold gibbsCondMeasure
    rw [withDensity_apply _ hS.compl]
    -- Integrate a nonneg function over a set of measure 0.
    have hμmap_Sc :
        ((productHaar G d N).map
            (fun uΛ : LatticeLink d N → G => gluedConfig G d N Λ uΛ σ)) Sᶜ = 0 :=
      map_glue_compl_eq_zero G d N Λ σ
    -- lintegral over a null set is 0.
    have hrest :
        ((productHaar G d N).map
            (fun uΛ : LatticeLink d N → G => gluedConfig G d N Λ uΛ σ)).restrict Sᶜ = 0 := by
      rw [Measure.restrict_eq_zero]; exact hμmap_Sc
    rw [hrest, lintegral_zero_measure]
  -- Total mass: `S ∪ Sᶜ = univ`, disjoint, so `measure univ = measure S + measure Sᶜ`.
  have hunion : S ∪ Sᶜ = Set.univ := Set.union_compl_self S
  have hdisj : Disjoint S Sᶜ := disjoint_compl_right
  have hmeas_union :
      gibbsCondMeasure G n d N plaq β Λ σ Set.univ
        = gibbsCondMeasure G n d N plaq β Λ σ S
          + gibbsCondMeasure G n d N plaq β Λ σ Sᶜ := by
    rw [← hunion, measure_union hdisj hS.compl]
  rw [htot, hSc_zero, add_zero] at hmeas_union
  exact hmeas_union.symm

/-- Consistency of the conditional measure: if σ and τ agree
outside Λ, the conditional measures coincide.

Proof: `gluedConfig Λ uΛ σ e = uΛ e` if `e ∈ Λ`, else `σ e`; since
σ and τ agree on `Λᶜ`, `gluedConfig Λ uΛ σ = gluedConfig Λ uΛ τ`
pointwise, hence as functions, so the pushforward and density agree. -/
theorem gibbsCondMeasure_consistent (β : ℝ)
    (Λ : Finset (LatticeLink d N))
    (σ τ : GaugeConnection G d N)
    (h : ∀ x, x ∉ Λ → σ x = τ x) :
    gibbsCondMeasure G n d N plaq β Λ σ =
      gibbsCondMeasure G n d N plaq β Λ τ := by
  have hglue : (fun uΛ : LatticeLink d N → G => gluedConfig G d N Λ uΛ σ) =
      (fun uΛ : LatticeLink d N → G => gluedConfig G d N Λ uΛ τ) := by
    funext uΛ
    funext e
    by_cases he : e ∈ Λ
    · simp [gluedConfig, he]
    · simp [gluedConfig, he, h e he]
  have hglue_pt : ∀ uΛ : LatticeLink d N → G,
      gluedConfig G d N Λ uΛ σ = gluedConfig G d N Λ uΛ τ := by
    intro uΛ
    funext e
    by_cases he : e ∈ Λ
    · simp [gluedConfig, he]
    · simp [gluedConfig, he, h e he]
  have hZ : gibbsConditionalZ G n d N plaq β Λ σ =
      gibbsConditionalZ G n d N plaq β Λ τ := by
    unfold gibbsConditionalZ gibbsConditionalWeight
    congr 1
    funext uΛ
    rw [hglue_pt uΛ]
  unfold gibbsCondMeasure
  rw [hglue, hZ]

/-- Normalization: total mass of `gibbsCondMeasure` is 1, given
positivity of the partition function and measurability of the
Boltzmann weight.

This is the analytic content of `isProb`:

1. Total mass = `(withDensity (w/Z)) (univ) = ∫⁻ U, (w(U)/Z) ∂(map glue)`.
2. By `lintegral_map`, this equals `∫⁻ uΛ, (w(glue uΛ σ)/Z) ∂productHaar`
   (using that the density is measurable).
3. Since `Z > 0`, we factor `1/Z` out of the integral:
   `(1/Z) · ∫⁻ uΛ, w(glue uΛ σ) ∂productHaar`.
4. The remaining integral is exactly `Z = gibbsConditionalZ`
   (as an lintegral of a nonneg real function), so the ratio is 1. -/
theorem gibbsCondMeasure_total
    (β : ℝ) (Λ : Finset (LatticeLink d N))
    (σ : GaugeConnection G d N)
    (hZ_pos : 0 < gibbsConditionalZ G n d N plaq β Λ σ)
    (hw_meas : Measurable
        (fun U : GaugeConnection G d N =>
          boltzmannWeight G n d N β U plaq))
    (hw_integrable :
        Integrable (fun uΛ : LatticeLink d N → G =>
            gibbsConditionalWeight G n d N plaq β Λ σ uΛ)
          (Measure.pi (fun _ : LatticeLink d N => haarG G))) :
    gibbsCondMeasure G n d N plaq β Λ σ Set.univ = 1 := by
  unfold gibbsCondMeasure
  set μ := Measure.pi (fun _ : LatticeLink d N => haarG G)
    with hμ_def
  set glue : (LatticeLink d N → G) → GaugeConnection G d N :=
    fun uΛ => gluedConfig G d N Λ uΛ σ
  set Z := gibbsConditionalZ G n d N plaq β Λ σ with hZ_def
  have hglue_meas : Measurable glue := measurable_gluedConfig G d N Λ σ
  have hZne : (Z : ℝ) ≠ 0 := ne_of_gt hZ_pos
  -- Density function as a measurable ℝ≥0∞-valued function.
  let fdens : GaugeConnection G d N → ENNReal := fun U => ENNReal.ofReal
      (boltzmannWeight G n d N β U plaq / Z)
  have hfdens_meas : Measurable fdens :=
    (hw_meas.div_const Z).ennreal_ofReal
  -- Step 1: Apply withDensity on univ.
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  -- Step 2: Change of variables through `map glue`.
  -- ∫⁻ U, fdens U ∂(map glue μ) = ∫⁻ uΛ, fdens (glue uΛ) ∂μ.
  have hmap_eq : (productHaar G d N).map glue = μ.map glue := by
    rfl
  rw [hmap_eq, lintegral_map hfdens_meas hglue_meas]
  -- Step 3: Rewrite the integrand using boltzmannWeight of glued config.
  -- `fdens (glue uΛ) = ENNReal.ofReal (w(glue uΛ σ) / Z)`, and
  -- `w(glue uΛ σ) = gibbsConditionalWeight β Λ σ uΛ` by definition.
  have hrewrite :
      (fun uΛ => fdens (glue uΛ))
        = fun uΛ : LatticeLink d N → G => ENNReal.ofReal
            (gibbsConditionalWeight G n d N plaq β Λ σ uΛ / Z) := by
    funext uΛ; rfl
  rw [hrewrite]
  -- Step 4: Factor out 1/Z from the integrand.
  have hw_nonneg : ∀ uΛ, 0 ≤ gibbsConditionalWeight G n d N plaq β Λ σ uΛ :=
    fun uΛ => (boltzmannWeight_pos G n d N β _ plaq).le
  have hZ_inv_nn : (0 : ℝ) ≤ 1 / Z := by positivity
  have hw_comp_meas : Measurable (fun uΛ : LatticeLink d N → G =>
      gibbsConditionalWeight G n d N plaq β Λ σ uΛ) := by
    unfold gibbsConditionalWeight
    exact hw_meas.comp hglue_meas
  have hdiv :
      (fun uΛ : LatticeLink d N → G =>
          ENNReal.ofReal (gibbsConditionalWeight G n d N plaq β Λ σ uΛ / Z))
        = fun uΛ => ENNReal.ofReal (1 / Z) *
            ENNReal.ofReal (gibbsConditionalWeight G n d N plaq β Λ σ uΛ) := by
    funext uΛ
    rw [← ENNReal.ofReal_mul hZ_inv_nn]
    congr 1
    field_simp
  rw [hdiv]
  rw [lintegral_const_mul _ hw_comp_meas.ennreal_ofReal]
  -- Step 5: Identify the remaining integral with Z.
  have hZ_integral :
      (∫⁻ uΛ : LatticeLink d N → G,
          ENNReal.ofReal (gibbsConditionalWeight G n d N plaq β Λ σ uΛ) ∂μ)
        = ENNReal.ofReal Z := by
    rw [hZ_def]
    unfold gibbsConditionalZ
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hw_integrable
      (Filter.Eventually.of_forall hw_nonneg)]
  rw [hZ_integral]
  -- Step 6: (1/Z) · Z = 1 in ENNReal.
  rw [← ENNReal.ofReal_mul hZ_inv_nn,
    one_div_mul_cancel hZne, ENNReal.ofReal_one]

/-- **The YM Gibbs specification on the link lattice.**

The conditional distribution γ(Λ, σ) is the conditional Boltzmann
measure `gibbsCondMeasure Λ σ`, obtained by pushing product Haar
through the `glue σ` map and reweighting by the Boltzmann density.

The four structure axioms are:

- `isProb`: normalization `∫ w/Z d(pushforward) = Z/Z = 1`. Proved by
  `gibbsCondMeasure_total`, given `Z > 0` and measurability/integrability
  of the Boltzmann weight (provided as hypotheses).
- `consistent`: `gibbsCondMeasure_consistent`.
- `proper`: `gibbsCondMeasure_proper_of_total`, reduced to `isProb`.
- `measurable_condDist`: σ ↦ (γ(Λ,σ) A).toReal is measurable. The full
  analytic argument (parametrized lintegral + ratio + Fubini-Tonelli)
  is provided as a hypothesis `hmeas_condDist`, which we do not prove
  here; a fully unconditional proof requires substantial extra
  measure-theoretic infrastructure (see the detailed sketch below). -/
def ymGibbsSpec (β : ℝ)
    (hZ_pos : ∀ (Λ : Finset (LatticeLink d N)) (σ : GaugeConnection G d N),
      0 < gibbsConditionalZ G n d N plaq β Λ σ)
    (hw_meas : Measurable
        (fun U : GaugeConnection G d N =>
          boltzmannWeight G n d N β U plaq))
    (hw_integrable : ∀ (Λ : Finset (LatticeLink d N))
        (σ : GaugeConnection G d N),
        Integrable (fun uΛ : LatticeLink d N → G =>
            gibbsConditionalWeight G n d N plaq β Λ σ uΛ)
          (Measure.pi (fun _ : LatticeLink d N => haarG G)))
    (hmeas_condDist : ∀ (Λ : Finset (LatticeLink d N))
        (A : Set (GaugeConnection G d N)),
        MeasurableSet A →
        Measurable (fun σ : GaugeConnection G d N =>
          (gibbsCondMeasure G n d N plaq β Λ σ A).toReal)) :
    GibbsSpec (LatticeLink d N) G where
  condDist := fun Λ σ => gibbsCondMeasure G n d N plaq β Λ σ
  isProb := by
    intro Λ σ
    -- `gibbsCondMeasure Λ σ Set.univ = 1` via `gibbsCondMeasure_total`.
    refine ⟨?_⟩
    exact gibbsCondMeasure_total G n d N plaq β Λ σ
      (hZ_pos Λ σ) hw_meas (hw_integrable Λ σ)
  consistent := gibbsCondMeasure_consistent G n d N plaq β
  proper := by
    intro Λ σ
    -- Proper follows from `isProb` via `gibbsCondMeasure_proper_of_total`.
    refine gibbsCondMeasure_proper_of_total G n d N plaq β Λ σ ?_
    exact gibbsCondMeasure_total G n d N plaq β Λ σ
      (hZ_pos Λ σ) hw_meas (hw_integrable Λ σ)
  measurable_condDist := hmeas_condDist

/-! ## Sketch of `measurable_condDist` proof

The measurability of `σ ↦ (gibbsCondMeasure Λ σ A).toReal` decomposes as
follows. Expanding definitions,

  `(gibbsCondMeasure Λ σ A).toReal
    = ((productHaar).map (glue σ)).withDensity (w/Z(σ)) A`
    = (1/Z(σ)) · (∫⁻ uΛ in preimage, w(glue uΛ σ) ∂productHaar).toReal`

where the preimage is `glue⁻¹(A) ∩ ...`. Each piece is measurable in σ:

  (i)   σ ↦ glue Λ uΛ σ is measurable on each slice (identity on Λᶜ,
        constant on Λ), hence jointly measurable.
  (ii)  σ ↦ Z(σ) = ∫ w(glue uΛ σ) ∂productHaar is measurable as a
        parametrized Bochner integral (continuous dependence + Fubini).
  (iii) σ ↦ ∫⁻ 𝟙_A(glue uΛ σ) · w(glue uΛ σ) ∂productHaar is measurable
        for the same reason.
  (iv)  The ratio of (iii) to (ii) is measurable since Z(σ) > 0 is
        bounded away from 0 (via `partitionFn_pos`-style estimate).

A full formalization requires: (a) `Measurable.lintegral_prod_right` /
`MeasureTheory.stronglyMeasurable_integral`, (b) `Measurable.div`,
(c) joint measurability of `(σ, uΛ) ↦ glue Λ uΛ σ` on the product
measurable space. This is genuine measure-theoretic work; we leave it
as a hypothesis `hmeas_condDist` to the specification constructor. -/

end
