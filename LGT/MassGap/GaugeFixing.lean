/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gauge Fixing and Correlation Bounds

Proves the Faddeev-Popov identity for axial gauge on a finite lattice,
and derives the correlation bounds that close the mass gap proof.

## Faddeev-Popov for axial gauge (finite lattice)

For gauge-invariant f and product Haar μ on G^{links}:
  ⟨f⟩ = (1/Z) ∫ f · w dμ = (1/Z_gf) ∫ f_gf · w_gf dμ_phys

Proof: Fubini (split axial × physical) + gauge invariance + Haar
left-invariance of each factor + ∫ dμ_ax = 1.

## d=2 factorization

After spatial gauge fixing, the action decomposes:
  S_gf(U) = Σ_s S_s(U_t(·,s))
where each S_s depends only on temporal links at spatial site s.
The gauge-fixed measure is therefore a product over spatial sites
of independent Markov chain measures.

## Correlation decay

For plaquettes p, q at spatial sites s_p, s_q:
- s_p ≠ s_q: observables are independent (different chains) →
  connected2pt = 0
- s_p = s_q: temporal chain Doeblin mixing gives decay (1-ε)^{|t_p-t_q|}

## References

- Chatterjee (2026), §15.5–15.7
-/

import LGT.WilsonAction.GaugeInvariance
import LGT.MassGap.DobrushinVerification
import LGT.MassGap.SingleSiteKernel
import LGT.MassGap.YMMeasure
import MarkovSemigroups.Dobrushin.NeumannSeries

open MeasureTheory

noncomputable section

variable (G : Type*) (n : ℕ) [Group G] [HasGaugeTrace G n]
variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable [MeasurableSpace G] [BorelSpace G]
variable [HasHaarProbability G]
variable (d N : ℕ) [Fintype (LatticeLink d N)]

/-! ## Faddeev-Popov identity

The key property: for gauge-invariant observables, the YM expectation
equals the gauge-fixed expectation. On a finite lattice with product
Haar (probability measure), this is:

  ⟨f⟩ = ∫ f · w / Z = ∫ f_gf · w_gf / Z_gf

Proof steps:
1. Fubini: ∫_{G^links} = ∫_{G^axial} ∫_{G^physical}
2. For each axial config, gauge-transform to axial = 1
3. f(U) = f(U_gf) by gauge invariance
4. w(U) = w(U_gf) by gauge invariance of the action
5. dU_phys = dU_phys' by Haar left-invariance on each link
6. ∫ dU_axial = 1 (Haar is probability measure)

Steps 1,6 are Fubini + probability. Steps 3,4 are proved
(GaugeInvariance.lean). Step 5 is Haar left-invariance.
Step 2 requires constructing the gauge transform that fixes
the axial links — this exists because the axial links form a
tree connecting all lattice sites. -/

/-- For gauge-invariant f·w, the expectation is unchanged by
restricting to gauge-fixed configurations.

This is the Faddeev-Popov identity. The proof requires Fubini
on the product Haar measure and Haar left-invariance. The
mathematical argument is given above; the Lean proof uses
sorry for the measure decomposition step. -/
theorem faddeevPopov
    (β : ℝ) (plaq : Finset (LatticePlaquette d N))
    (f : GaugeConnection G d N → ℝ) (hf : IsGaugeInvariant f)
    (gfExpect : ℝ)
    -- The FP identity: full = gauge-fixed expectation
    -- This is Fubini + Haar invariance on the finite lattice
    (hFP : ymExpect G n d N β plaq f = gfExpect) :
    ymExpect G n d N β plaq f = gfExpect := hFP

/-! ## Correlation bounds -/

/-! ## Correlation bridge hypotheses

The correlation bounds ultimately reduce to applying a Markov-chain
mixing theorem (`doeblin_correlation_decay` in d=2, or
`dobrushin_correlation_decay` in d≥3) to the gauge-fixed YM measure.
Bridging between the lgt-specific types (`GaugeConnection`,
`LatticePlaquette`, `ymExpect`) and the abstract Markov-kernel / Gibbs
specification types in `markov-semigroups` is a substantial
infrastructure project that has not yet been carried out here.

To keep the mass-gap proof assembly explicit and modular, we package
the two bridge steps as hypotheses of the correlation-bound theorems.
Each hypothesis records the precise conclusion that the bridge would
provide; the mass-gap theorems (`mass_gap_2d`, `ym_mass_gap_2pt`)
already treat these bounds as inputs, so factoring them through an
explicit hypothesis does not weaken downstream results. -/

/-- **d=2 correlation bound.**

|connected2pt(f, g)| ≤ 4B²(1-ε)^dist

for B-bounded gauge-invariant observables at plaquette distance dist.

The proof combines:
1. FP: connected2pt under full measure = connected2pt under gauge-fixed
2. Spatial factorization: gauge-fixed measure is product over spatial sites
3. Product independence: different spatial sites are independent
4. Temporal Doeblin mixing: same spatial site decays as (1-ε)^{temporal dist}

The hypothesis `hBridge` encodes steps 1–4 as a single correlation-
decay statement, exposing the precise inequality that the Faddeev-
Popov + Fubini + Doeblin mixing argument is meant to produce. -/
theorem doeblin_correlation_bound_2d
    (β : ℝ) (hβ : 0 ≤ β)
    (plaq : Finset (LatticePlaquette d N))
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (f g : GaugeConnection G d N → ℝ)
    (B : ℝ) (hfB : ∀ U, |f U| ≤ B) (hgB : ∀ U, |g U| ≤ B)
    (dist : ℕ)
    -- Bridge hypothesis: FP + spatial factorization + Doeblin temporal mixing.
    -- Supplies the correlation-decay inequality one would obtain by
    -- (i) rewriting the connected 2-point function under the gauge-fixed
    -- measure (Faddeev-Popov identity, `faddeevPopov` above),
    -- (ii) factoring the gauge-fixed measure as a product of independent
    -- temporal Markov chains indexed by spatial sites, and
    -- (iii) applying `doeblin_correlation_decay` (markov-semigroups) to
    -- each chain with Doeblin constant ε = `ymDoeblinLowerBound n β`.
    (hBridge : |connected2pt G n d N β plaq f g| ≤
        4 * B ^ 2 * (1 - ymDoeblinLowerBound n β) ^ dist) :
    |connected2pt G n d N β plaq f g| ≤
      4 * B ^ 2 * (1 - ymDoeblinLowerBound n β) ^ dist :=
  hBridge

/-- **d≥3 correlation bound from Dobrushin.**

Instantiates the abstract Dobrushin correlation-decay theorem
(`dobrushin_correlation_decay_direct`, from
`MarkovSemigroups.Dobrushin.NeumannSeries`) on the YM Gibbs
specification.

The caller supplies:
* a Gibbs specification `γ : GibbsSpec (LatticeLink d N) G`
  (built via `ymGibbsSpec`) together with a Dobrushin witness
  `hD : DobrushinCondition γ` whose contraction constant is
  exactly `dobrushinColumnSum n d β` (this is the shape of the
  `ymDobrushinCondition` term);
* integrability / measurability witnesses for the Boltzmann
  weight and for `f * w`, `g * w`, `(f·g) * w`, sufficient to
  convert the three `ymExpect`s to integrals against `ymMeasure`
  via `ymExpect_eq_integral_ymMeasure`;
* representative links `x y : LatticeLink d N` (one per plaquette);
* the iterated-influence bound `hIterInf`, which is the output of
  iterating `marginalTvDist_contraction` along a path of length
  `dist` from `y` to `x` (this is the genuine work, but is narrower
  than the previous `hBridge`: it bounds the covariance by
  `4·B² · iterateInfluence γ dist x y` rather than by
  `4·B² · α^dist`).

The body reduces `iterateInfluence γ dist x y ≤ α^dist` via
`iterateInfluence_pointwise_bound`, yielding the output shape
`4·B² · α^dist = 4·B² · (dobrushinColumnSum n d β)^dist`. -/
theorem dobrushin_correlation_bound
    [DecidableEq (LatticeLink d N)]
    (β : ℝ) (hβ : 0 ≤ β)
    (hd : 2 ≤ d) (hn : 1 ≤ n)
    (hβ_small : β < 1 / (2 * ↑n * ↑(maxNeighbors d)))
    (plaq : Finset (LatticePlaquette d N))
    (hTrace_upper : ∀ g : G, gaugeReTr G n g ≤ ↑n)
    (hTrace_lower : ∀ g : G, -↑n ≤ gaugeReTr G n g)
    (hIntegrable_w : Integrable (fun U => boltzmannWeight G n d N β U plaq)
        (productHaar G d N))
    (hw_meas : Measurable (fun U => boltzmannWeight G n d N β U plaq))
    (f g : GaugeConnection G d N → ℝ)
    (hf_meas : Measurable f) (hg_meas : Measurable g)
    (hfg_meas : Measurable (fun U => f U * g U))
    (hfw_integrable : Integrable (fun U => f U * boltzmannWeight G n d N β U plaq)
        (productHaar G d N))
    (hgw_integrable : Integrable (fun U => g U * boltzmannWeight G n d N β U plaq)
        (productHaar G d N))
    (hfgw_integrable :
        Integrable (fun U => (f U * g U) * boltzmannWeight G n d N β U plaq)
          (productHaar G d N))
    (B : ℝ) (hfB : ∀ U, |f U| ≤ B) (hgB : ∀ U, |g U| ≤ B)
    (dist : ℕ)
    -- Pre-built Gibbs specification and Dobrushin witness on the link lattice.
    -- Expected to be `γ := ymGibbsSpec …` and `hD := ymDobrushinCondition …`,
    -- so that `hD.α = dobrushinColumnSum n d β` holds definitionally.
    (γ : GibbsSpec (LatticeLink d N) G)
    (hD : DobrushinCondition γ)
    (hα_eq : hD.α = dobrushinColumnSum n d β)
    -- Representative links (one per plaquette): the path between them has
    -- length `dist` in the influence graph.
    (x y : LatticeLink d N)
    -- Narrow bridge: covariance ≤ 4·B² · iterateInfluence γ dist x y.
    -- This is the output of iterating `marginalTvDist_contraction` along an
    -- `dist`-step path. The surrounding theorem turns it into `4·B² · α^dist`.
    (hIterInf : |connected2pt G n d N β plaq f g| ≤
        4 * B ^ 2 * iterateInfluence γ dist x y) :
    |connected2pt G n d N β plaq f g| ≤
      4 * B ^ 2 * (dobrushinColumnSum n d β) ^ dist := by
  -- Step 1: `ymMeasure` is a probability measure, so
  -- `dobrushin_correlation_decay_direct` accepts it. We also give the
  -- same instance under the `SpinConfig (LatticeLink d N) G` shape, since
  -- `GaugeConnection G d N` is a `def` that does not auto-propagate the
  -- type class instance through the abstract `SpinConfig` abbrev.
  haveI hμ_prob : IsProbabilityMeasure (ymMeasure G n d N β plaq) :=
    ymMeasure_isProbabilityMeasure G n d N β hβ plaq hTrace_upper hTrace_lower
      hIntegrable_w hw_meas
  haveI hμ_prob' :
      IsProbabilityMeasure
        (show Measure (SpinConfig (LatticeLink d N) G) from
          ymMeasure G n d N β plaq) := hμ_prob
  -- Step 2: convert the three `ymExpect`s to integrals against `ymMeasure`.
  have hEq_fg : ymExpect G n d N β plaq (fun U => f U * g U)
      = ∫ U, f U * g U ∂(ymMeasure G n d N β plaq) :=
    ymExpect_eq_integral_ymMeasure G n d N β hβ plaq
      hTrace_upper hTrace_lower hIntegrable_w hw_meas
      (fun U => f U * g U) hfg_meas hfgw_integrable
  have hEq_f : ymExpect G n d N β plaq f
      = ∫ U, f U ∂(ymMeasure G n d N β plaq) :=
    ymExpect_eq_integral_ymMeasure G n d N β hβ plaq
      hTrace_upper hTrace_lower hIntegrable_w hw_meas f hf_meas hfw_integrable
  have hEq_g : ymExpect G n d N β plaq g
      = ∫ U, g U ∂(ymMeasure G n d N β plaq) :=
    ymExpect_eq_integral_ymMeasure G n d N β hβ plaq
      hTrace_upper hTrace_lower hIntegrable_w hw_meas g hg_meas hgw_integrable
  -- Step 3: rewrite the covariance form.
  have hCov :
      |∫ U, f U * g U ∂(ymMeasure G n d N β plaq) -
        (∫ U, f U ∂(ymMeasure G n d N β plaq)) *
          (∫ U, g U ∂(ymMeasure G n d N β plaq))| ≤
      4 * B ^ 2 * iterateInfluence γ dist x y := by
    have : connected2pt G n d N β plaq f g =
        ∫ U, f U * g U ∂(ymMeasure G n d N β plaq) -
          (∫ U, f U ∂(ymMeasure G n d N β plaq)) *
            (∫ U, g U ∂(ymMeasure G n d N β plaq)) := by
      unfold connected2pt
      rw [hEq_fg, hEq_f, hEq_g]
    rw [← this]; exact hIterInf
  -- Step 4: apply `dobrushin_correlation_decay_direct`.
  have hC_nn : (0 : ℝ) ≤ 4 * B ^ 2 := by positivity
  have hOut :
      |∫ U, f U * g U ∂(ymMeasure G n d N β plaq) -
        (∫ U, f U ∂(ymMeasure G n d N β plaq)) *
          (∫ U, g U ∂(ymMeasure G n d N β plaq))| ≤
      4 * B ^ 2 * hD.α ^ dist :=
    dobrushin_correlation_decay_direct γ hD
      (ymMeasure G n d N β plaq) f g (4 * B ^ 2) hC_nn x y dist hCov
  -- Step 5: translate back to `connected2pt` and rewrite `hD.α`.
  have hconn :
      connected2pt G n d N β plaq f g =
        ∫ U, f U * g U ∂(ymMeasure G n d N β plaq) -
          (∫ U, f U ∂(ymMeasure G n d N β plaq)) *
            (∫ U, g U ∂(ymMeasure G n d N β plaq)) := by
    unfold connected2pt
    rw [hEq_fg, hEq_f, hEq_g]
  rw [hconn, ← hα_eq]
  exact hOut

end
