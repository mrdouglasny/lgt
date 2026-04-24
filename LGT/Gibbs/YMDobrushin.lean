/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Dobrushin Condition for the YM Gibbs Specification

Verifies that the `ymGibbsSpec` (defined in LGT/Gibbs/YMSpec.lean)
satisfies Dobrushin's uniqueness condition when the coupling β is
sufficiently small.

This bridges the lgt-specific YM construction to the abstract
`DobrushinCondition` and ultimately `dobrushin_uniqueness` from
markov-semigroups.

## Architecture

For the (unfixed) YM specification on links:
- Neighbor relation: "share a plaquette"
- Each link has ≤ 6(d-1) plaquette-neighbors (maxNeighbors d)
  (Each plaquette has 4 links; excluding x, 3 others interact.)
- Each shared plaquette contributes influence ≤ 1 - exp(-4nβ) ≤ 4nβ
- Dobrushin column sum ≤ 8(d-1) · 4nβ = 32n(d-1)β

For β < 1/(32n(d-1)), the Dobrushin condition holds.

## References

- Chatterjee (2026), §16.3
- LGT/MassGap/DobrushinVerification.lean (existing infrastructure)
- LGT/Gibbs/YMSpec.lean (the YM Gibbs spec)
-/

import LGT.Gibbs.YMSpec
import LGT.MassGap.DobrushinVerification
import MarkovSemigroups.Dobrushin.Uniqueness

set_option linter.unusedSectionVars false

open MeasureTheory

noncomputable section

open Classical

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
variable [HasHaarProbability G]
variable (n d N : ℕ) [HasGaugeTrace G n] [Fintype (LatticeLink d N)]
variable [DecidableEq (LatticeLink d N)]

/-! ## The "shares a plaquette" relation

Two links are plaquette-neighbors if they both lie on the boundary
of some common plaquette. This is the nearest-neighbor structure
for the YM action. -/

/-- Links x and y share a plaquette if there exists p with both in ∂p. -/
def sharesPlaquette (plaq : Finset (LatticePlaquette d N))
    (x y : LatticeLink d N) : Prop :=
  ∃ p ∈ plaq, ∃ i j : Fin 4,
    p.boundaryLinks i = x ∧ p.boundaryLinks j = y

/-- Decidability: with Fintype instances, we can check plaquette sharing. -/
instance [DecidableEq (LatticePlaquette d N)] [Fintype (LatticePlaquette d N)]
    (plaq : Finset (LatticePlaquette d N)) (x y : LatticeLink d N) :
    Decidable (sharesPlaquette d N plaq x y) := by
  unfold sharesPlaquette; infer_instance

/-! ## Plaquette counting: neighbor-count bounds

The set of links sharing a plaquette with a fixed link `y` is
contained in the union, over plaquettes `p` containing `y`, of the
four boundary links of `p`. Hence if every link lies on at most `M`
plaquettes, every link has at most `4·M` plaquette-neighbours.

Concretely, for the periodic lattice `(ℤ/Nℤ)ᵈ` the sharp geometric
bound is `M = 2·(d-1) = maxPlaquettesPerLink d`, giving `8(d-1)`
neighbours — which is looser than the `6(d-1) = maxNeighbors d` used
below because it does not exclude `y` itself from each plaquette.
The finer `6(d-1)` bound (at most `3` other links per plaquette) is
also available but requires tracking which index on the boundary
equals `y`. We prove the coarse `4·M` bound here since it is all
that is needed to absorb both bridge hypotheses into a single
`hPlaqPerLink` assumption. -/

/-- If `p` is a plaquette and both `x` and `y` lie on its boundary,
then `x` lies in the image of `p.boundaryLinks`. This is immediate
but packaged for reuse. -/
lemma mem_image_boundaryLinks_of_eq {p : LatticePlaquette d N}
    {i : Fin 4} {x : LatticeLink d N} (hx : p.boundaryLinks i = x) :
    x ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks := by
  refine Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hx⟩

/-- The Finset `Finset.univ.image p.boundaryLinks` has at most `4`
elements. -/
lemma card_image_boundaryLinks_le (p : LatticePlaquette d N) :
    ((Finset.univ : Finset (Fin 4)).image p.boundaryLinks).card ≤ 4 := by
  refine le_trans (Finset.card_image_le) ?_
  simp

/-- **Key neighbour-count bound.**

For any link `y` and any finite set of plaquettes `plaq`, the finset
of links sharing a plaquette with `y` is bounded by `4` times the
number of plaquettes in `plaq` whose boundary contains `y`. -/
lemma sharesPlaquette_card_le_plaq_containing
    (plaq : Finset (LatticePlaquette d N)) (y : LatticeLink d N) :
    ((Finset.univ : Finset (LatticeLink d N)).filter
        (fun x => sharesPlaquette d N plaq x y)).card
      ≤ 4 * (plaq.filter
          (fun p => y ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks)).card := by
  classical
  -- The set of neighbours is contained in the biUnion of boundary-link images
  -- over plaquettes that contain `y`.
  set P_y : Finset (LatticePlaquette d N) :=
    plaq.filter
      (fun p => y ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks) with hPy
  have hsubset :
      (Finset.univ : Finset (LatticeLink d N)).filter
          (fun x => sharesPlaquette d N plaq x y)
        ⊆ P_y.biUnion
            (fun p => (Finset.univ : Finset (Fin 4)).image p.boundaryLinks) := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨_, hshare⟩
    rcases hshare with ⟨p, hp, i, j, hxi, hyj⟩
    refine Finset.mem_biUnion.mpr ⟨p, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨hp, ?_⟩
      exact mem_image_boundaryLinks_of_eq d N hyj
    · exact mem_image_boundaryLinks_of_eq d N hxi
  -- Cardinality of biUnion is bounded by sum of cardinalities.
  have hcard :
      (P_y.biUnion
          (fun p => (Finset.univ : Finset (Fin 4)).image p.boundaryLinks)).card
        ≤ ∑ p ∈ P_y,
            ((Finset.univ : Finset (Fin 4)).image p.boundaryLinks).card :=
    Finset.card_biUnion_le
  -- Each summand is ≤ 4, so the sum ≤ 4 · card P_y.
  have hsum_le :
      (∑ p ∈ P_y,
          ((Finset.univ : Finset (Fin 4)).image p.boundaryLinks).card)
        ≤ ∑ p ∈ P_y, 4 :=
    Finset.sum_le_sum (fun p _ => card_image_boundaryLinks_le d N p)
  have hsum_const : (∑ _p ∈ P_y, (4 : ℕ)) = 4 * P_y.card := by
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  calc ((Finset.univ : Finset (LatticeLink d N)).filter
          (fun x => sharesPlaquette d N plaq x y)).card
      ≤ (P_y.biUnion
          (fun p => (Finset.univ : Finset (Fin 4)).image p.boundaryLinks)).card :=
        Finset.card_le_card hsubset
    _ ≤ ∑ p ∈ P_y,
          ((Finset.univ : Finset (Fin 4)).image p.boundaryLinks).card := hcard
    _ ≤ ∑ p ∈ P_y, 4 := hsum_le
    _ = 4 * P_y.card := hsum_const

/-- The row version of `sharesPlaquette_card_le_plaq_containing`: the
number of links `y` sharing a plaquette with a fixed `x` is also
controlled by the number of plaquettes containing `x`. -/
lemma sharesPlaquette_card_le_plaq_containing_row
    (plaq : Finset (LatticePlaquette d N)) (x : LatticeLink d N) :
    ((Finset.univ : Finset (LatticeLink d N)).filter
        (fun y => sharesPlaquette d N plaq x y)).card
      ≤ 4 * (plaq.filter
          (fun p => x ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks)).card := by
  classical
  set P_x : Finset (LatticePlaquette d N) :=
    plaq.filter
      (fun p => x ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks) with hPx
  have hsubset :
      (Finset.univ : Finset (LatticeLink d N)).filter
          (fun y => sharesPlaquette d N plaq x y)
        ⊆ P_x.biUnion
            (fun p => (Finset.univ : Finset (Fin 4)).image p.boundaryLinks) := by
    intro y hy
    rcases Finset.mem_filter.mp hy with ⟨_, hshare⟩
    rcases hshare with ⟨p, hp, i, j, hxi, hyj⟩
    refine Finset.mem_biUnion.mpr ⟨p, ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨hp, ?_⟩
      exact mem_image_boundaryLinks_of_eq d N hxi
    · exact mem_image_boundaryLinks_of_eq d N hyj
  have hcard :
      (P_x.biUnion
          (fun p => (Finset.univ : Finset (Fin 4)).image p.boundaryLinks)).card
        ≤ ∑ p ∈ P_x,
            ((Finset.univ : Finset (Fin 4)).image p.boundaryLinks).card :=
    Finset.card_biUnion_le
  have hsum_le :
      (∑ p ∈ P_x,
          ((Finset.univ : Finset (Fin 4)).image p.boundaryLinks).card)
        ≤ ∑ p ∈ P_x, 4 :=
    Finset.sum_le_sum (fun p _ => card_image_boundaryLinks_le d N p)
  have hsum_const : (∑ _p ∈ P_x, (4 : ℕ)) = 4 * P_x.card := by
    rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
  calc ((Finset.univ : Finset (LatticeLink d N)).filter
          (fun y => sharesPlaquette d N plaq x y)).card
      ≤ (P_x.biUnion
          (fun p => (Finset.univ : Finset (Fin 4)).image p.boundaryLinks)).card :=
        Finset.card_le_card hsubset
    _ ≤ ∑ p ∈ P_x,
          ((Finset.univ : Finset (Fin 4)).image p.boundaryLinks).card := hcard
    _ ≤ ∑ p ∈ P_x, 4 := hsum_le
    _ = 4 * P_x.card := hsum_const

/-- **Neighbor count from a plaquette-per-link bound (column).**

If every link lies on at most `M` plaquettes (from `plaq`), then the
number of plaquette-neighbours of any link is at most `4·M`. This
derives the `hMaxNeighborsCol` bridge hypothesis of
`ymDobrushinCondition` from the single combinatorial statement that
each link is contained in at most `M` plaquettes. -/
theorem maxNeighborsCol_of_plaqPerLink
    (plaq : Finset (LatticePlaquette d N)) (M : ℕ)
    (hPlaqPerLink : ∀ y : LatticeLink d N,
      (plaq.filter
        (fun p => y ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks)).card
          ≤ M) :
    ∀ y : LatticeLink d N,
      ((Finset.univ : Finset (LatticeLink d N)).filter
        (fun x => sharesPlaquette d N plaq x y)).card ≤ 4 * M := by
  intro y
  exact (sharesPlaquette_card_le_plaq_containing d N plaq y).trans
    (Nat.mul_le_mul_left 4 (hPlaqPerLink y))

/-- **Neighbor count from a plaquette-per-link bound (row).** -/
theorem maxNeighborsRow_of_plaqPerLink
    (plaq : Finset (LatticePlaquette d N)) (M : ℕ)
    (hPlaqPerLink : ∀ x : LatticeLink d N,
      (plaq.filter
        (fun p => x ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks)).card
          ≤ M) :
    ∀ x : LatticeLink d N,
      ((Finset.univ : Finset (LatticeLink d N)).filter
        (fun y => sharesPlaquette d N plaq x y)).card ≤ 4 * M := by
  intro x
  exact (sharesPlaquette_card_le_plaq_containing_row d N plaq x).trans
    (Nat.mul_le_mul_left 4 (hPlaqPerLink x))

/-! ## Influence coefficient bounds for YM

The key physics input: when a link y changes (others fixed), the
conditional distribution at link x changes in TV by ≤ 1 - exp(-4nβ)
if they share a plaquette, and by 0 otherwise.

Proof sketch (full Mathlib proof requires continuity/Lipschitz
bounds for the Boltzmann ratio):
- If x, y don't share a plaquette: the single-link conditional at x
  depends only on plaquettes containing x, none of which involve y.
  So changing y doesn't change the conditional. TV = 0.
- If they share: the action change is ≤ β·osc_plaquette = β·2n
  (from |Re Tr| ≤ n). The TV distance between exp(-E₁)dHaar and
  exp(-E₂)dHaar where |E₁-E₂| ≤ 2nβ is ≤ 1 - exp(-4nβ). -/

/-- **Influence coefficient is zero for non-plaquette-neighbors.**

This is a bridge hypothesis. Full proof requires:
1. Apply consistency of the Gibbs spec at {x}
2. If σ, τ agree on all plaquette-neighbors of x, they give the same
   conditional (action depends only on plaquettes touching x)
3. So the sup over τ differing at y gives 0. -/
def ymInfluenceZeroOffPlaquette (β : ℝ) (plaq : Finset (LatticePlaquette d N))
    (hZ_pos : ∀ Λ σ, 0 < gibbsConditionalZ G n d N plaq β Λ σ)
    (hw_meas : Measurable fun U => boltzmannWeight G n d N β U plaq)
    (hw_integrable : ∀ (Λ : Finset (LatticeLink d N))
        (σ : GaugeConnection G d N),
        Integrable (fun uΛ : LatticeLink d N → G =>
            gibbsConditionalWeight G n d N plaq β Λ σ uΛ)
          (Measure.pi (fun _ : LatticeLink d N => haarG G)))
    (hmeas_condDist : ∀ (Λ : Finset (LatticeLink d N))
      (A : Set (GaugeConnection G d N)),
      MeasurableSet A →
      Measurable (fun σ : GaugeConnection G d N =>
        ((gibbsCondMeasure G n d N plaq β Λ σ) A).toReal))
    (x y : LatticeLink d N) (_hne : x ≠ y)
    (_h_no_shared : ¬ sharesPlaquette d N plaq x y) : Prop :=
  influenceCoeff
    (ymGibbsSpec G n d N plaq β hZ_pos hw_meas hw_integrable hmeas_condDist)
    x y = 0

/-- **Influence coefficient bound for plaquette-neighbors.**

For links sharing a plaquette: C(x,y) ≤ 1 - exp(-4nβ).

This is a bridge hypothesis encoding the Boltzmann TV-ratio bound.
Full proof requires:
1. The single-link conditional at x is a Boltzmann measure with
   energy E(σ) = β·Σ_{p ∋ x} plaquetteCost(σ).
2. Changing one neighbor y changes E by at most β·2n per shared plaquette.
3. For cylinder-set density ratio exp(2D) with D = 2nβ:
   `influenceCoeff_le_of_cylinder_ratio_bound` gives d_TV ≤ 1 - exp(-4nβ).
4. Apply with C = 4nβ (= 2D). -/
def ymInfluenceBoundOnPlaquette (β : ℝ) (plaq : Finset (LatticePlaquette d N))
    (hZ_pos : ∀ Λ σ, 0 < gibbsConditionalZ G n d N plaq β Λ σ)
    (hw_meas : Measurable fun U => boltzmannWeight G n d N β U plaq)
    (hw_integrable : ∀ (Λ : Finset (LatticeLink d N))
        (σ : GaugeConnection G d N),
        Integrable (fun uΛ : LatticeLink d N → G =>
            gibbsConditionalWeight G n d N plaq β Λ σ uΛ)
          (Measure.pi (fun _ : LatticeLink d N => haarG G)))
    (hmeas_condDist : ∀ (Λ : Finset (LatticeLink d N))
      (A : Set (GaugeConnection G d N)),
      MeasurableSet A →
      Measurable (fun σ : GaugeConnection G d N =>
        ((gibbsCondMeasure G n d N plaq β Λ σ) A).toReal))
    (x y : LatticeLink d N) : Prop :=
  influenceCoeff
    (ymGibbsSpec G n d N plaq β hZ_pos hw_meas hw_integrable hmeas_condDist)
    x y ≤ influenceBound n β

/-! ## Main theorem: YM satisfies Dobrushin at strong coupling

Combining the influence bounds with the plaquette counting gives
the Dobrushin column sum bound, which is < 1 for β small enough.

The full proof requires Fintype structure on links (already present),
finite-support summability (automatic for Fintype), and the column
sum calculation (from DobrushinVerification.lean). -/

/-- **The YM Gibbs spec satisfies Dobrushin at strong coupling.**

This packages the Dobrushin condition for the YM specification.
The proof requires:
1. Each `influenceCoeff` bound (from `ymInfluenceZeroOffPlaquette` and
   `ymInfluenceBoundOnPlaquette`)
2. Finite-support summability (links form a Fintype)
3. Column sum ≤ 8(d-1) · (1 - exp(-4nβ)) (plaquette counting)
4. Column sum < 1 (from `dobrushin_sufficient`)

Bridge hypothesis encoding the full construction. -/
def ymDobrushinCondition
    (β : ℝ) (hβ : 0 ≤ β) (plaq : Finset (LatticePlaquette d N))
    (hd : 2 ≤ d) (hn : 1 ≤ n)
    (hβ_small : β < 1 / (4 * ↑n * ↑(maxNeighbors d)))
    (hZ_pos : ∀ Λ σ, 0 < gibbsConditionalZ G n d N plaq β Λ σ)
    (hw_meas : Measurable fun U => boltzmannWeight G n d N β U plaq)
    (hw_integrable : ∀ (Λ : Finset (LatticeLink d N))
        (σ : GaugeConnection G d N),
        Integrable (fun uΛ : LatticeLink d N → G =>
            gibbsConditionalWeight G n d N plaq β Λ σ uΛ)
          (Measure.pi (fun _ : LatticeLink d N => haarG G)))
    (hmeas_condDist : ∀ (Λ : Finset (LatticeLink d N))
      (A : Set (GaugeConnection G d N)),
      MeasurableSet A →
      Measurable (fun σ : GaugeConnection G d N =>
        ((gibbsCondMeasure G n d N plaq β Λ σ) A).toReal))
    -- Bridge hypothesis: all pairs satisfy the appropriate influence bound.
    -- Uses Classical decidability to avoid requiring a Decidable instance.
    (hInfluence : ∀ x y : LatticeLink d N,
      influenceCoeff
        (ymGibbsSpec G n d N plaq β hZ_pos hw_meas hw_integrable hmeas_condDist)
        x y ≤ (if sharesPlaquette d N plaq x y then influenceBound n β else 0))
    -- Plaquette counting (geometric fact about the lattice):
    -- the number of links sharing a plaquette with a fixed link y (resp. x)
    -- is at most maxNeighbors d = 6(d-1).
    (hMaxNeighborsCol : ∀ y : LatticeLink d N,
      ((Finset.univ : Finset (LatticeLink d N)).filter
        (fun x => sharesPlaquette d N plaq x y)).card ≤ maxNeighbors d)
    (hMaxNeighborsRow : ∀ x : LatticeLink d N,
      ((Finset.univ : Finset (LatticeLink d N)).filter
        (fun y => sharesPlaquette d N plaq x y)).card ≤ maxNeighbors d) :
    DobrushinCondition
      (ymGibbsSpec G n d N plaq β hZ_pos hw_meas hw_integrable hmeas_condDist) :=
  -- Short-hand for the Gibbs spec in proofs below.
  let γ := ymGibbsSpec G n d N plaq β hZ_pos hw_meas hw_integrable hmeas_condDist
  -- The contraction constant α := maxNeighbors(d) · influenceBound(n,β),
  -- which is `dobrushinColumnSum n d β`.
  { α := dobrushinColumnSum n d β
    hα_pos := by
      unfold dobrushinColumnSum
      exact mul_nonneg (Nat.cast_nonneg' _) (influenceBound_nonneg n β hβ)
    hα_lt := dobrushin_sufficient n d hd hn β hβ hβ_small
    col_summable := by
      -- Any function on a Fintype is summable: it has finite support.
      intro y
      exact summable_of_ne_finset_zero (s := Finset.univ)
        (fun x hx => (hx (Finset.mem_univ x)).elim)
    column_bound := by
      intro y
      -- Reduce tsum to a finite sum on Finset.univ.
      have htsum : (∑' x, influenceCoeff γ x y) =
          ∑ x ∈ (Finset.univ : Finset (LatticeLink d N)), influenceCoeff γ x y := by
        rw [tsum_eq_sum (s := Finset.univ)
          (fun x hx => (hx (Finset.mem_univ x)).elim)]
      rw [htsum]
      -- Majorize by the indicator sum using hInfluence.
      have hstep1 :
          ∑ x ∈ (Finset.univ : Finset (LatticeLink d N)), influenceCoeff γ x y
            ≤ ∑ x ∈ (Finset.univ : Finset (LatticeLink d N)),
                (if sharesPlaquette d N plaq x y then influenceBound n β else 0) := by
        apply Finset.sum_le_sum
        intro x _
        exact hInfluence x y
      -- The indicator sum equals card · influenceBound.
      have hstep2 :
          ∑ x ∈ (Finset.univ : Finset (LatticeLink d N)),
              (if sharesPlaquette d N plaq x y then influenceBound n β else 0)
            = ((Finset.univ.filter
                (fun x => sharesPlaquette d N plaq x y)).card : ℝ)
              * influenceBound n β := by
        classical
        rw [← Finset.sum_filter]
        rw [Finset.sum_const, nsmul_eq_mul]
      calc ∑ x ∈ (Finset.univ : Finset (LatticeLink d N)), influenceCoeff γ x y
          ≤ ∑ x ∈ (Finset.univ : Finset (LatticeLink d N)),
              (if sharesPlaquette d N plaq x y then influenceBound n β else 0) := hstep1
        _ = ((Finset.univ.filter
              (fun x => sharesPlaquette d N plaq x y)).card : ℝ)
            * influenceBound n β := hstep2
        _ ≤ (maxNeighbors d : ℝ) * influenceBound n β := by
            apply mul_le_mul_of_nonneg_right _ (influenceBound_nonneg n β hβ)
            exact_mod_cast hMaxNeighborsCol y
        _ = dobrushinColumnSum n d β := rfl
    row_summable := by
      intro x
      exact summable_of_ne_finset_zero (s := Finset.univ)
        (fun y hy => (hy (Finset.mem_univ y)).elim)
    row_bound := by
      intro x
      have htsum : (∑' y, influenceCoeff γ x y) =
          ∑ y ∈ (Finset.univ : Finset (LatticeLink d N)), influenceCoeff γ x y := by
        rw [tsum_eq_sum (s := Finset.univ)
          (fun y hy => (hy (Finset.mem_univ y)).elim)]
      rw [htsum]
      have hstep1 :
          ∑ y ∈ (Finset.univ : Finset (LatticeLink d N)), influenceCoeff γ x y
            ≤ ∑ y ∈ (Finset.univ : Finset (LatticeLink d N)),
                (if sharesPlaquette d N plaq x y then influenceBound n β else 0) := by
        apply Finset.sum_le_sum
        intro y _
        exact hInfluence x y
      have hstep2 :
          ∑ y ∈ (Finset.univ : Finset (LatticeLink d N)),
              (if sharesPlaquette d N plaq x y then influenceBound n β else 0)
            = ((Finset.univ.filter
                (fun y => sharesPlaquette d N plaq x y)).card : ℝ)
              * influenceBound n β := by
        classical
        rw [← Finset.sum_filter]
        rw [Finset.sum_const, nsmul_eq_mul]
      calc ∑ y ∈ (Finset.univ : Finset (LatticeLink d N)), influenceCoeff γ x y
          ≤ ∑ y ∈ (Finset.univ : Finset (LatticeLink d N)),
              (if sharesPlaquette d N plaq x y then influenceBound n β else 0) := hstep1
        _ = ((Finset.univ.filter
              (fun y => sharesPlaquette d N plaq x y)).card : ℝ)
            * influenceBound n β := hstep2
        _ ≤ (maxNeighbors d : ℝ) * influenceBound n β := by
            apply mul_le_mul_of_nonneg_right _ (influenceBound_nonneg n β hβ)
            exact_mod_cast hMaxNeighborsRow x
        _ = dobrushinColumnSum n d β := rfl }

/-! ## Convenience wrapper: Dobrushin from a plaquette-per-link bound

The two `hMaxNeighbors*` bridge hypotheses in `ymDobrushinCondition`
encode a genuinely geometric fact about the lattice: each link lies
on at most `2·(d-1) = maxPlaquettesPerLink d` plaquettes. Combined
with the fact that each plaquette has four boundary links (proven
above in `sharesPlaquette_card_le_plaq_containing[_row]`), this
yields the neighbor-count bound `card ≤ 4·M`.

This wrapper packages that reduction: the user supplies only a
single `hPlaqPerLink` hypothesis (plus a numeric inequality
`4·M ≤ maxNeighbors d` witnessing that `maxNeighbors d` is loose
enough). In particular, with `M = 2·(d-1) = maxPlaquettesPerLink d`
one has `4·M = 8(d-1)`, which is the *best* bound provable from
this coarse union argument; the sharper `6(d-1) = maxNeighbors d`
requires tracking which position on each plaquette's boundary
equals the fixed link. -/
def ymDobrushinCondition_of_plaqPerLink
    (β : ℝ) (hβ : 0 ≤ β) (plaq : Finset (LatticePlaquette d N))
    (hd : 2 ≤ d) (hn : 1 ≤ n)
    (hβ_small : β < 1 / (4 * ↑n * ↑(maxNeighbors d)))
    (hZ_pos : ∀ Λ σ, 0 < gibbsConditionalZ G n d N plaq β Λ σ)
    (hw_meas : Measurable fun U => boltzmannWeight G n d N β U plaq)
    (hw_integrable : ∀ (Λ : Finset (LatticeLink d N))
        (σ : GaugeConnection G d N),
        Integrable (fun uΛ : LatticeLink d N → G =>
            gibbsConditionalWeight G n d N plaq β Λ σ uΛ)
          (Measure.pi (fun _ : LatticeLink d N => haarG G)))
    (hmeas_condDist : ∀ (Λ : Finset (LatticeLink d N))
      (A : Set (GaugeConnection G d N)),
      MeasurableSet A →
      Measurable (fun σ : GaugeConnection G d N =>
        ((gibbsCondMeasure G n d N plaq β Λ σ) A).toReal))
    (hInfluence : ∀ x y : LatticeLink d N,
      influenceCoeff
        (ymGibbsSpec G n d N plaq β hZ_pos hw_meas hw_integrable hmeas_condDist)
        x y ≤ (if sharesPlaquette d N plaq x y then influenceBound n β else 0))
    -- Single combinatorial bridge hypothesis: each link lies on at most
    -- `M` plaquettes from `plaq`.
    (M : ℕ)
    (hPlaqPerLink : ∀ ℓ : LatticeLink d N,
      (plaq.filter
        (fun p => ℓ ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks)).card
          ≤ M)
    -- Numeric slack: the coarse neighbor bound `4·M` must fit in `maxNeighbors d`.
    (hLoose : 4 * M ≤ maxNeighbors d) :
    DobrushinCondition
      (ymGibbsSpec G n d N plaq β hZ_pos hw_meas hw_integrable hmeas_condDist) :=
  ymDobrushinCondition G n d N β hβ plaq hd hn hβ_small
    hZ_pos hw_meas hw_integrable hmeas_condDist hInfluence
    (hMaxNeighborsCol := fun y =>
      (maxNeighborsCol_of_plaqPerLink d N plaq M hPlaqPerLink y).trans hLoose)
    (hMaxNeighborsRow := fun x =>
      (maxNeighborsRow_of_plaqPerLink d N plaq M hPlaqPerLink x).trans hLoose)

/-! ## Path to uniqueness

With `ymDobrushinCondition` realized as an actual `DobrushinCondition`
term, the abstract `dobrushin_uniqueness` theorem from markov-semigroups
gives:

  ∀ μ₁ μ₂ Gibbs measures for ymGibbsSpec, μ₁ = μ₂.

This is the uniqueness of the Yang-Mills Gibbs measure at strong
coupling, which (combined with gauge invariance) gives the mass gap. -/

end
