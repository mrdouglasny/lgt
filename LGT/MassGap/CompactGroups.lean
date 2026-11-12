/-
Copyright (c) 2026. Released under Apache 2.0 license (same as `lgt`).

# Strong-coupling mass gap for closed subgroups of U(n), and for SU(n)

`LGT.MassGap.StrongCoupling` proves exponential decay of the connected
plaquette two-point function at strong coupling, but only instantiates it
for `G = U(n)`. `U(n)` is not simple, so it is not one of the gauge groups
of the Yang–Mills problem. This file extends the result to

* every subgroup `H ≤ U(n)` that is compact (equivalently, closed in `U(n)`),
  which includes `SU(n)`, `SO(n)`, `Sp(n)` and, via Peter–Weyl, every compact
  Lie group in some faithful unitary representation; this is the same class
  of gauge groups ("closed matrix subgroup G ⊂ U(m)") taken as input by the
  OpenAI continuum construction;
* `SU(n)` concretely, with compactness proved and the reference measure
  instantiated as the genuine normalized Haar measure.

No existing `lgt` file is modified. The proofs reuse
`ym_mass_gap_strong_coupling`, `linkGraphDist_support` and
`boundary_sum_bound`, which are already generic in the gauge group.

## Main results

* `ym_mass_gap_exponential_decay_subgroup` — algebraic decay for any compact
  `H ≤ U(n)`, with the same constants as the U(n) theorem.
* `ym_mass_gap_rate_exists_subgroup` — existential exponential rate `m > 0`.
* `SUn`, `mem_SUn_iff_specialUnitaryGroup` — SU(n) as a subgroup of U(n),
  identified with Mathlib's `Matrix.specialUnitaryGroup`.
* `isClosed_SUn`, `SUn.instCompactSpace` — SU(n) is compact.
* `compactHaarProbability`, `compactHaar_isHaarMeasure` — normalized Haar
  probability measure on any compact group (left invariant).
* `su_mass_gap_exponential_decay`, `su_mass_gap_rate_exists` — the SU(n)
  strong-coupling lattice mass gap.

## Conventions

As in `lgt`: the Wilson action is `β Σ_p (n − Re Tr U_p)`, so this `β` is
`β_std / n` in the usual normalization `β_std Σ_p (1 − Re Tr U_p / n)`. The
hypothesis `β < 1/(32 n (d−1))` is a strong-coupling (large bare `g²`)
condition, far from the continuum limit `β → ∞`.

## Status

Written against `lgt` revision `b8793cc` and Mathlib `v4.30.0`; see the
accompanying README for its build status.
-/

import LGT.MassGap.StrongCoupling
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.MeasureTheory.Measure.Haar.Basic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Matrix MeasureTheory Measure TopologicalSpace Real

noncomputable section

/-! ## Haar probability measure on an arbitrary compact group -/

section CompactHaar

variable (K : Type*) [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

/-- The whole of a compact group, as a `PositiveCompacts`. -/
def univPositiveCompacts : PositiveCompacts K where
  toCompacts := ⟨Set.univ, isCompact_univ⟩
  interior_nonempty' := by rw [interior_univ]; exact ⟨1, Set.mem_univ _⟩

/-- The Haar measure of a compact group normalized to total mass one. -/
def compactHaar : Measure K := haarMeasure (univPositiveCompacts K)

instance compactHaar_isProbability : IsProbabilityMeasure (compactHaar K) := by
  constructor
  show haarMeasure (univPositiveCompacts K) Set.univ = 1
  have h := @haarMeasure_self K _ _ _ _ _ (univPositiveCompacts K)
  simp [univPositiveCompacts] at h
  exact h

/-- `compactHaar` is a genuine Haar measure (in particular left invariant), so
the `HasHaarProbability` instance built from it is the physical one. -/
theorem compactHaar_isHaarMeasure : IsHaarMeasure (compactHaar K) :=
  isHaarMeasure_haarMeasure _

/-- Normalized Haar probability measure on a compact group, packaged for `lgt`. -/
def compactHaarProbability : HasHaarProbability K where
  haar := compactHaar K
  isProb := compactHaar_isProbability K

end CompactHaar

/-! ## Subgroups of U(n) as gauge groups -/

section Subgroups

variable (n : ℕ)

/-- A subgroup of `U(n)` acts in the defining representation `H → U(n) → M_n(ℂ)`. -/
instance instHasGaugeTraceSubgroup (H : Subgroup (Matrix.unitaryGroup (Fin n) ℂ)) :
    HasGaugeTrace H n where
  rep := (unitaryGroupIncl n).comp H.subtype

variable (H : Subgroup (Matrix.unitaryGroup (Fin n) ℂ))

/-- The trace of `g ∈ H` is the trace of `g` viewed in `U(n)`. -/
theorem subgroup_gaugeReTr_eq (g : H) :
    gaugeReTr H n g =
      gaugeReTr (Matrix.unitaryGroup (Fin n) ℂ) n (g : Matrix.unitaryGroup (Fin n) ℂ) :=
  rfl

theorem subgroup_gaugeReTr_le (g : H) : gaugeReTr H n g ≤ ↑n := by
  rw [subgroup_gaugeReTr_eq]
  exact unitaryGroup_gaugeReTr_le n _

theorem subgroup_gaugeReTr_neg_le (g : H) : -↑n ≤ gaugeReTr H n g := by
  rw [subgroup_gaugeReTr_eq]
  exact unitaryGroup_gaugeReTr_neg_le n _

theorem subgroup_rep_continuous :
    Continuous (HasGaugeTrace.rep (G := H) (n := n)) := by
  change Continuous
    (fun g : H => ((g : Matrix.unitaryGroup (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))
  exact continuous_subtype_val.comp continuous_subtype_val

/-- A closed subgroup of the compact group `U(n)` is compact. -/
theorem compactSpace_of_isClosed
    (hH : IsClosed (H : Set (Matrix.unitaryGroup (Fin n) ℂ))) : CompactSpace H := by
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) := instCompactSpaceUnitaryGroup n
  exact isCompact_iff_compactSpace.mp hH.isCompact

end Subgroups

/-! ## The strong-coupling mass gap for compact subgroups of U(n) -/

section SubgroupMassGap

/-- **Strong-coupling mass gap, any compact gauge group `H ≤ U(n)`.**

For Wilson lattice gauge theory on `(ℤ/Nℤ)^d` with gauge group a compact
subgroup `H` of `U(n)` in the defining representation, at
`β < 1/(32 n (d−1))`,

    |⟨Re Tr U_p · Re Tr U_q⟩_c| ≤ 32 n² / (1 − α) · α^((d(p,q) − 1)/2),

uniformly in the lattice size `N`, where `α = dobrushinAlpha n d β < 1` and
`d(p,q)` is the periodic L¹ plaquette distance. The single-link reference
measure is any probability measure supplied by `HasHaarProbability H`; the
SU(n) corollary below uses the normalized Haar measure. -/
theorem ym_mass_gap_exponential_decay_subgroup
    (n : ℕ) (hn : 1 ≤ n)
    (H : Subgroup (Matrix.unitaryGroup (Fin n) ℂ))
    [CompactSpace H] [HasHaarProbability H]
    (d N : ℕ) (hd : 2 ≤ d) (hN : 2 < N) [NeZero N]
    [Fintype (LatticeLink d N)] [DecidableEq (LatticeLink d N)]
    (β : ℝ) (hβ : 0 ≤ β)
    (hβ_small : β < 1 / (4 * ↑n * ↑(maxNeighbors d)))
    (plaq : Finset (LatticePlaquette d N))
    (p q : LatticePlaquette d N) :
    |connected2pt H n d N β plaq (plaqObs H n d N p) (plaqObs H n d N q)| ≤
      32 * (↑n : ℝ) ^ 2 / (1 - dobrushinAlpha n d β) *
        (dobrushinAlpha n d β) ^ ((latticePlaquetteDist d N p q - 1) / 2) := by
  classical
  haveI : Inhabited H := ⟨1⟩
  have hα_lt : dobrushinAlpha n d β < 1 :=
    dobrushin_sufficient n d hd hn β hβ hβ_small
  have hstrong :=
    ym_mass_gap_strong_coupling
      (G := H) (n := n) (d := d) (N := N)
      hd hn hN β hβ hβ_small
      (subgroup_gaugeReTr_neg_le n H)
      (subgroup_gaugeReTr_le n H)
      plaq p q
      (subgroup_rep_continuous n H)
      (fun x y : LatticeLink d N => linkGraphDist d N x y)
      (fun x => linkGraphDist_self d N x)
      (fun x y z => linkGraphDist_triangle d N hd hN x y z)
      (linkGraphDist_support (G := H) (n := n) (d := d) (N := N) plaq β)
  have hsum :
      ∑ x ∈ ((Finset.univ : Finset (Fin 4)).image
              (LatticePlaquette.boundaryLinks p)),
        ∑ y ∈ ((Finset.univ : Finset (Fin 4)).image
              (LatticePlaquette.boundaryLinks q)),
          (dobrushinAlpha n d β) ^ linkGraphDist d N y x /
            (1 - dobrushinAlpha n d β)
        ≤
          16 *
            ((dobrushinAlpha n d β) ^
                ((latticePlaquetteDist d N p q - 1) / 2) /
              (1 - dobrushinAlpha n d β)) := by
    simpa [LatticePlaquette.boundaryLinkFinset] using
      (boundary_sum_bound n d N hd hN β hβ hα_lt p q)
  have hcoef_nonneg : 0 ≤ 2 * (↑n : ℝ) * (↑n : ℝ) := by positivity
  have hbound := hstrong.trans (mul_le_mul_of_nonneg_left hsum hcoef_nonneg)
  have harith :
      2 * (↑n : ℝ) * (↑n : ℝ) *
          (16 *
            ((dobrushinAlpha n d β) ^
                ((latticePlaquetteDist d N p q - 1) / 2) /
              (1 - dobrushinAlpha n d β))) =
        32 * (↑n : ℝ) ^ 2 / (1 - dobrushinAlpha n d β) *
          (dobrushinAlpha n d β) ^
            ((latticePlaquetteDist d N p q - 1) / 2) := by
    ring
  simpa [harith] using hbound

/-! ### Rate form

The helper lemmas below restate private lemmas of `StrongCoupling.lean`,
which cannot be imported. They involve no gauge group. -/

lemma influenceBound_pos' (n : ℕ) (hn : 1 ≤ n) (β : ℝ) (hβ_pos : 0 < β) :
    0 < influenceBound n β := by
  unfold influenceBound
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn
  have hneg : -4 * (n : ℝ) * β < 0 := by nlinarith [hn_pos, hβ_pos]
  linarith [Real.exp_lt_one_iff.mpr hneg]

lemma dobrushinAlpha_pos' (n d : ℕ) (hn : 1 ≤ n) (hd : 2 ≤ d)
    (β : ℝ) (hβ_pos : 0 < β) :
    0 < dobrushinAlpha n d β := by
  unfold dobrushinAlpha
  have hmax_pos : (0 : ℝ) < maxNeighbors d := by
    unfold maxNeighbors maxPlaquettesPerLink
    have hd' : 0 < d - 1 := by omega
    exact_mod_cast (Nat.mul_pos (by omega : 0 < 4) (Nat.mul_pos (by omega : 0 < 2) hd'))
  exact mul_pos hmax_pos (influenceBound_pos' n hn β hβ_pos)

lemma plaquetteDist_rate_floor_bound' (t : ℕ) :
    ((t : ℝ) - 2) / 2 ≤ (((t - 1) / 2 : ℕ) : ℝ) := by
  have hnat : t ≤ 2 * ((t - 1) / 2) + 2 := by
    have h : (t - 1) - 1 ≤ 2 * ((t - 1) / 2) := by
      have hdecomp := Nat.mod_add_div (t - 1) 2
      have hmod : (t - 1) % 2 = 0 ∨ (t - 1) % 2 = 1 := by omega
      rcases hmod with hmod | hmod <;> omega
    omega
  have hreal : (t : ℝ) ≤ 2 * (((t - 1) / 2 : ℕ) : ℝ) + 2 := by
    exact_mod_cast hnat
  nlinarith

lemma pow_floor_le_exp_rate' {α : ℝ} (hα_pos : 0 < α) (hα_lt : α < 1) (t : ℕ) :
    α ^ ((t - 1) / 2) ≤ α⁻¹ * Real.exp (-((-Real.log α) / 2) * (t : ℝ)) := by
  set r : ℕ := (t - 1) / 2
  have hlog_neg : Real.log α < 0 := Real.log_neg hα_pos hα_lt
  have hr : ((t : ℝ) - 2) / 2 ≤ (r : ℝ) := by
    simpa only [r] using plaquetteDist_rate_floor_bound' t
  have hmul : Real.log α * (r : ℝ) ≤ Real.log α * (((t : ℝ) - 2) / 2) := by
    exact mul_le_mul_of_nonpos_left hr hlog_neg.le
  calc
    α ^ r = Real.exp (Real.log α * (r : ℝ)) := by
      rw [mul_comm, Real.exp_nat_mul, Real.exp_log hα_pos]
    _ ≤ Real.exp (Real.log α * (((t : ℝ) - 2) / 2)) := Real.exp_le_exp.mpr hmul
    _ = α⁻¹ * Real.exp (-((-Real.log α) / 2) * (t : ℝ)) := by
      rw [show Real.log α * (((t : ℝ) - 2) / 2) =
          -Real.log α + (Real.log α / 2) * (t : ℝ) by ring]
      rw [Real.exp_add, Real.exp_neg, Real.exp_log hα_pos]
      congr 1
      ring_nf

lemma decay_bound_to_rate' {α C : ℝ} (hα_pos : 0 < α) (hα_lt : α < 1)
    (hC_nonneg : 0 ≤ C) (t : ℕ) :
    C * α ^ ((t - 1) / 2) ≤
      C / α * Real.exp (-((-Real.log α) / 2) * (t : ℝ)) := by
  have hpow := pow_floor_le_exp_rate' hα_pos hα_lt t
  calc
    C * α ^ ((t - 1) / 2)
        ≤ C * (α⁻¹ * Real.exp (-((-Real.log α) / 2) * (t : ℝ))) := by
          exact mul_le_mul_of_nonneg_left hpow hC_nonneg
    _ = C / α * Real.exp (-((-Real.log α) / 2) * (t : ℝ)) := by
          field_simp [hα_pos.ne']

/-- **Strong-coupling mass gap with an explicit positive rate**, any compact
gauge group `H ≤ U(n)`: there is `m > 0`, independent of the lattice size
and of the plaquettes, with
`|⟨Re Tr U_p · Re Tr U_q⟩_c| ≤ C · exp(−m · d(p,q))`. -/
theorem ym_mass_gap_rate_exists_subgroup
    (n : ℕ) (hn : 1 ≤ n)
    (H : Subgroup (Matrix.unitaryGroup (Fin n) ℂ))
    [CompactSpace H] [HasHaarProbability H]
    (d N : ℕ) (hd : 2 ≤ d) (hN : 2 < N) [NeZero N]
    [Fintype (LatticeLink d N)] [DecidableEq (LatticeLink d N)]
    (β : ℝ) (hβ_pos : 0 < β)
    (hβ_small : β < 1 / (4 * ↑n * ↑(maxNeighbors d))) :
    ∃ (m : ℝ), 0 < m ∧ ∀ (plaq : Finset (LatticePlaquette d N))
        (p q : LatticePlaquette d N),
      |connected2pt H n d N β plaq (plaqObs H n d N p) (plaqObs H n d N q)| ≤
        32 * (↑n : ℝ) ^ 2 /
          (dobrushinAlpha n d β * (1 - dobrushinAlpha n d β)) *
          Real.exp (-m * ↑(latticePlaquetteDist d N p q)) := by
  classical
  set α : ℝ := dobrushinAlpha n d β
  have hα_pos : 0 < α := by
    simpa [α] using dobrushinAlpha_pos' n d hn hd β hβ_pos
  have hα_lt : α < 1 := by
    simpa [α] using dobrushin_sufficient n d hd hn β hβ_pos.le hβ_small
  refine ⟨(-Real.log α) / 2, ?_, ?_⟩
  · exact div_pos (neg_pos.mpr (Real.log_neg hα_pos hα_lt)) (by norm_num)
  · intro plaq p q
    have hden_pos : 0 < 1 - α := by linarith
    have hC_nonneg : 0 ≤ 32 * (↑n : ℝ) ^ 2 / (1 - α) := by positivity
    have hK :=
      ym_mass_gap_exponential_decay_subgroup n hn H d N hd hN β hβ_pos.le hβ_small
        plaq p q
    have hrate := decay_bound_to_rate' (α := α)
      (C := 32 * (↑n : ℝ) ^ 2 / (1 - α)) hα_pos hα_lt hC_nonneg
      (latticePlaquetteDist d N p q)
    have htarget :
        32 * (↑n : ℝ) ^ 2 / (1 - α) / α *
            Real.exp (-((-Real.log α) / 2) * ↑(latticePlaquetteDist d N p q)) =
          32 * (↑n : ℝ) ^ 2 / (α * (1 - α)) *
            Real.exp (-((-Real.log α) / 2) * ↑(latticePlaquetteDist d N p q)) := by
      field_simp [hα_pos.ne', hden_pos.ne']
    have hrate' :
        32 * (↑n : ℝ) ^ 2 / (1 - α) *
            α ^ ((latticePlaquetteDist d N p q - 1) / 2) ≤
          32 * (↑n : ℝ) ^ 2 / (α * (1 - α)) *
            Real.exp (-((-Real.log α) / 2) * ↑(latticePlaquetteDist d N p q)) := by
      rw [← htarget]
      exact hrate
    exact hK.trans (by simpa [α] using hrate')

end SubgroupMassGap

/-! ## SU(n) -/

section SpecialUnitary

variable (n : ℕ)

/-- The determinant on `U(n)` as a monoid homomorphism to `ℂ`. -/
def unitaryDet : Matrix.unitaryGroup (Fin n) ℂ →* ℂ :=
  Matrix.detMonoidHom.comp (unitaryGroupIncl n)

/-- `SU(n)` as a subgroup of `U(n)`: unitary matrices of determinant one. -/
def SUn : Subgroup (Matrix.unitaryGroup (Fin n) ℂ) := (unitaryDet n).ker

theorem mem_SUn_iff (U : Matrix.unitaryGroup (Fin n) ℂ) :
    U ∈ SUn n ↔ (U : Matrix (Fin n) (Fin n) ℂ).det = 1 := by
  rw [SUn, MonoidHom.mem_ker]
  rfl

/-- `SUn n` is exactly Mathlib's `Matrix.specialUnitaryGroup`, so the theorems
below are about the standard `SU(n)`. -/
theorem mem_SUn_iff_specialUnitaryGroup (U : Matrix.unitaryGroup (Fin n) ℂ) :
    U ∈ SUn n ↔ (U : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.specialUnitaryGroup (Fin n) ℂ := by
  rw [mem_SUn_iff, Matrix.mem_specialUnitaryGroup_iff]
  exact ⟨fun h => ⟨U.2, h⟩, fun h => h.2⟩

theorem continuous_unitaryDet : Continuous (unitaryDet n) := by
  change Continuous
    (fun U : Matrix.unitaryGroup (Fin n) ℂ => (U : Matrix (Fin n) (Fin n) ℂ).det)
  exact continuous_subtype_val.matrix_det

theorem isClosed_SUn : IsClosed (SUn n : Set (Matrix.unitaryGroup (Fin n) ℂ)) := by
  rw [SUn, MonoidHom.coe_ker]
  exact isClosed_singleton.preimage (continuous_unitaryDet n)

/-- `SU(n)` is compact. -/
instance SUn.instCompactSpace : CompactSpace (SUn n) :=
  compactSpace_of_isClosed n (SUn n) (isClosed_SUn n)

/-- `SU(n)` carries its normalized Haar probability measure. -/
instance SUn.instHasHaarProbability : HasHaarProbability (SUn n) :=
  compactHaarProbability (SUn n)

/-- **Strong-coupling lattice mass gap for SU(n) Yang–Mills.**

Wilson lattice gauge theory with gauge group `SU(n)` and normalized Haar
link measure on `(ℤ/Nℤ)^d`, `d ≥ 2`, at `β < 1/(32 n (d−1))`:

    |⟨Re Tr U_p · Re Tr U_q⟩_c| ≤ 32 n² / (1 − α) · α^((d(p,q) − 1)/2),

uniformly in `N`. -/
theorem su_mass_gap_exponential_decay
    (hn : 1 ≤ n)
    (d N : ℕ) (hd : 2 ≤ d) (hN : 2 < N) [NeZero N]
    [Fintype (LatticeLink d N)] [DecidableEq (LatticeLink d N)]
    (β : ℝ) (hβ : 0 ≤ β)
    (hβ_small : β < 1 / (4 * ↑n * ↑(maxNeighbors d)))
    (plaq : Finset (LatticePlaquette d N))
    (p q : LatticePlaquette d N) :
    |connected2pt (SUn n) n d N β plaq
        (plaqObs (SUn n) n d N p) (plaqObs (SUn n) n d N q)| ≤
      32 * (↑n : ℝ) ^ 2 / (1 - dobrushinAlpha n d β) *
        (dobrushinAlpha n d β) ^ ((latticePlaquetteDist d N p q - 1) / 2) :=
  ym_mass_gap_exponential_decay_subgroup n hn (SUn n) d N hd hN β hβ hβ_small plaq p q

/-- **SU(n) strong-coupling mass gap, rate form**: `∃ m > 0` with
`|⟨Re Tr U_p · Re Tr U_q⟩_c| ≤ C · exp(−m · d(p,q))`, uniformly in `N`. -/
theorem su_mass_gap_rate_exists
    (hn : 1 ≤ n)
    (d N : ℕ) (hd : 2 ≤ d) (hN : 2 < N) [NeZero N]
    [Fintype (LatticeLink d N)] [DecidableEq (LatticeLink d N)]
    (β : ℝ) (hβ_pos : 0 < β)
    (hβ_small : β < 1 / (4 * ↑n * ↑(maxNeighbors d))) :
    ∃ (m : ℝ), 0 < m ∧ ∀ (plaq : Finset (LatticePlaquette d N))
        (p q : LatticePlaquette d N),
      |connected2pt (SUn n) n d N β plaq
          (plaqObs (SUn n) n d N p) (plaqObs (SUn n) n d N q)| ≤
        32 * (↑n : ℝ) ^ 2 /
          (dobrushinAlpha n d β * (1 - dobrushinAlpha n d β)) *
          Real.exp (-m * ↑(latticePlaquetteDist d N p q)) :=
  ym_mass_gap_rate_exists_subgroup n hn (SUn n) d N hd hN β hβ_pos hβ_small

end SpecialUnitary

end
