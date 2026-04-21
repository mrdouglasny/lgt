/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# HasGaugeTrace instance for the Unitary Group U(n)

Concrete instantiation of `HasGaugeTrace` for `Matrix.unitaryGroup (Fin n) ℂ`,
with proofs of the trace bounds and continuity needed by `ym_mass_gap_strong_coupling`,
plus the three typeclass instances needed by `ym_mass_gap_UN`:
`CompactSpace`, `SecondCountableTopology`, and `HasHaarProbability`.

## Main results

* `instHasGaugeTraceUnitaryGroup` -- `HasGaugeTrace (Matrix.unitaryGroup (Fin n) ℂ) n`
* `unitaryGroup_gaugeReTr_le` -- `gaugeReTr G n g ≤ ↑n`
* `unitaryGroup_gaugeReTr_neg_le` -- `-↑n ≤ gaugeReTr G n g`
* `unitaryGroup_rep_continuous` -- `Continuous (HasGaugeTrace.rep)`
* `instCompactSpaceUnitaryGroup` -- `CompactSpace (unitaryGroup (Fin n) ℂ)`
* `instSecondCountableTopologyUnitaryGroup` -- `SecondCountableTopology (unitaryGroup (Fin n) ℂ)`
* `instHasHaarProbabilityUnitaryGroup` -- `HasHaarProbability (unitaryGroup (Fin n) ℂ)`
-/

import LGT.GaugeField.GaugeGroup
import LGT.MassGap.YMMeasure
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.Instances.Matrix
import Mathlib.Data.Complex.BigOperators
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Bases
import Mathlib.MeasureTheory.Measure.Haar.Basic

open Matrix Complex Finset MeasureTheory Measure TopologicalSpace

noncomputable section

variable (n : ℕ)

/-- The inclusion `U(n) → M_n(ℂ)` as a monoid homomorphism. -/
def unitaryGroupIncl : Matrix.unitaryGroup (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ where
  toFun U := U.val
  map_one' := rfl
  map_mul' _ _ := rfl

instance instHasGaugeTraceUnitaryGroup :
    HasGaugeTrace (Matrix.unitaryGroup (Fin n) ℂ) n where
  rep := unitaryGroupIncl n

/-! ### Entry bound for unitary matrices

For a unitary matrix U, every entry satisfies `‖U i j‖ ≤ 1`.
This follows from the column-norm-one property: `∑ k, ‖U k j‖² = 1`.
-/

/-- Every entry of a unitary matrix has norm-squared at most 1. -/
lemma unitaryGroup_entry_normSq_le (U : Matrix.unitaryGroup (Fin n) ℂ)
    (i j : Fin n) : Complex.normSq (U.val i j) ≤ 1 := by
  -- From star_mul_self: star U.val * U.val = 1, taking (j,j) entry
  have hU := UnitaryGroup.star_mul_self U
  -- Extract the (j,j) diagonal entry of the equation
  have hdiag : ∑ k : Fin n, (star (U.val k j) * U.val k j).re = 1 := by
    have := congr_fun (congr_fun hU j) j
    simp only [mul_apply, one_apply_eq] at this
    have h2 := congr_arg Complex.re this
    rwa [Complex.re_sum, Complex.one_re] at h2
  -- Each summand equals normSq
  have hterm : ∀ k : Fin n,
      (star (U.val k j) * U.val k j).re = Complex.normSq (U.val k j) := by
    intro k
    simp [Complex.normSq_apply]
  simp_rw [hterm] at hdiag
  -- normSq is nonneg, sum = 1, so the i-th term ≤ 1
  calc Complex.normSq (U.val i j)
      ≤ ∑ k : Fin n, Complex.normSq (U.val k j) :=
        Finset.single_le_sum (f := fun k => Complex.normSq (U.val k j))
          (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    _ = 1 := hdiag

/-- Every entry of a unitary matrix has norm at most 1. -/
lemma unitaryGroup_entry_norm_le (U : Matrix.unitaryGroup (Fin n) ℂ)
    (i j : Fin n) : ‖U.val i j‖ ≤ 1 := by
  rw [Complex.norm_def]
  calc √(Complex.normSq (U.val i j))
      ≤ √1 := Real.sqrt_le_sqrt (unitaryGroup_entry_normSq_le n U i j)
    _ = 1 := Real.sqrt_one

/-! ### Trace bounds -/

/-- `gaugeReTr G n g ≤ n` for the unitary group. -/
theorem unitaryGroup_gaugeReTr_le
    (g : Matrix.unitaryGroup (Fin n) ℂ) :
    gaugeReTr (Matrix.unitaryGroup (Fin n) ℂ) n g ≤ ↑n := by
  simp only [gaugeReTr, gaugeTrace, Matrix.trace, Matrix.diag]
  rw [Complex.re_sum]
  calc ∑ i : Fin n, (HasGaugeTrace.rep g i i).re
      ≤ ∑ _i : Fin n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact (Complex.re_le_norm _).trans (unitaryGroup_entry_norm_le n g i i)
    _ = ↑n := by simp

/-- `-n ≤ gaugeReTr G n g` for the unitary group. -/
theorem unitaryGroup_gaugeReTr_neg_le
    (g : Matrix.unitaryGroup (Fin n) ℂ) :
    -↑n ≤ gaugeReTr (Matrix.unitaryGroup (Fin n) ℂ) n g := by
  simp only [gaugeReTr, gaugeTrace, Matrix.trace, Matrix.diag]
  rw [Complex.re_sum]
  have : -(↑n : ℝ) = ∑ _i : Fin n, (-1 : ℝ) := by simp
  rw [this]
  apply Finset.sum_le_sum
  intro i _
  have h1 : |Complex.re (HasGaugeTrace.rep g i i)| ≤ ‖HasGaugeTrace.rep g i i‖ :=
    Complex.abs_re_le_norm _
  have h2 : ‖HasGaugeTrace.rep g i i‖ ≤ 1 := unitaryGroup_entry_norm_le n g i i
  linarith [abs_le.mp (h1.trans h2)]

/-! ### Continuity of the representation -/

/-- The representation `U(n) → M_n(ℂ)` is continuous (subtype inclusion). -/
theorem unitaryGroup_rep_continuous :
    Continuous (HasGaugeTrace.rep (G := Matrix.unitaryGroup (Fin n) ℂ) (n := n)) :=
  continuous_subtype_val

/-! ### Topology on Matrix (Fin n) (Fin n) ℂ

The matrix space inherits `SecondCountableTopology` from the pi-type
`Fin n → Fin n → ℂ`, since `ℂ` is second-countable and the index is finite.
-/

instance instSecondCountableTopologyMatrix :
    SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))

/-! ### CompactSpace (unitaryGroup (Fin n) ℂ)

U(n) is compact: it is a closed, bounded subset of the finite-dimensional
matrix space M_n(ℂ).

**Closed:** The carrier `{A | star A * A = 1 ∧ A * star A = 1}` is the
preimage of the closed set `{(1, 1)}` under the continuous map
`A ↦ (star A * A, A * star A)`. This is `isClosed_unitary` from Mathlib.

**Bounded:** Every entry of a unitary matrix has norm at most 1
(proved above as `unitaryGroup_entry_norm_le`), so the carrier is
contained in `(closedBall 0 1).matrix`, which is compact by
`IsCompact.matrix` and the compactness of closed balls in `ℂ`
(a proper metric space).
-/

/-- The carrier of `unitaryGroup` is contained in the set of matrices whose
entries lie in the closed unit disk. -/
lemma unitaryGroup_carrier_subset_closedBall :
    (unitaryGroup (Fin n) ℂ).carrier ⊆
      (Metric.closedBall (0 : ℂ) 1).matrix := by
  intro A hA i j
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact unitaryGroup_entry_norm_le n ⟨A, hA⟩ i j

/-- `U(n)` is compact: closed and bounded in the finite-dimensional matrix space. -/
instance instCompactSpaceUnitaryGroup :
    CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) := by
  have hclosed : IsClosed (unitaryGroup (Fin n) ℂ).carrier := isClosed_unitary
  exact isCompact_iff_compactSpace.mp
    (IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) 1).matrix
      hclosed (unitaryGroup_carrier_subset_closedBall n))

/-! ### SecondCountableTopology (unitaryGroup (Fin n) ℂ)

`U(n)` is second-countable: it carries the subspace topology induced by the
inclusion into `M_n(ℂ)`, and subspaces of second-countable spaces are
second-countable.
-/

/-- `U(n)` is second-countable (subspace of the second-countable matrix space). -/
instance instSecondCountableTopologyUnitaryGroup :
    SecondCountableTopology (Matrix.unitaryGroup (Fin n) ℂ) :=
  Topology.IsInducing.secondCountableTopology (f := Subtype.val) ⟨rfl⟩

/-! ### HasHaarProbability (unitaryGroup (Fin n) ℂ)

Compact groups carry a unique bi-invariant probability measure (Haar measure).
We construct it via Mathlib's `haarMeasure`, choosing `K₀ = univ` (the whole
group, which is a `PositiveCompacts` because it is compact with nonempty
interior). The normalization `haarMeasure K₀ K₀ = 1` then gives
`haarMeasure K₀ univ = 1`, i.e. a probability measure.
-/

instance instMeasurableSpaceUnitaryGroup :
    MeasurableSpace (Matrix.unitaryGroup (Fin n) ℂ) := borel _

instance instBorelSpaceUnitaryGroup :
    BorelSpace (Matrix.unitaryGroup (Fin n) ℂ) := ⟨rfl⟩

/-- The whole unitary group, viewed as a `PositiveCompacts`. -/
private def unitaryGroupUniv :
    PositiveCompacts (Matrix.unitaryGroup (Fin n) ℂ) where
  toCompacts := ⟨Set.univ, isCompact_univ⟩
  interior_nonempty' := by rw [interior_univ]; exact Set.univ_nonempty

/-- The Haar probability measure on `U(n)`, normalized so that the total mass is 1. -/
noncomputable def unitaryHaar :
    Measure (Matrix.unitaryGroup (Fin n) ℂ) :=
  haarMeasure (unitaryGroupUniv n)

instance instIsProbabilityMeasureUnitaryHaar :
    IsProbabilityMeasure (unitaryHaar n) := by
  constructor
  show unitaryHaar n Set.univ = 1
  unfold unitaryHaar
  have h := @haarMeasure_self (Matrix.unitaryGroup (Fin n) ℂ) _ _ _ _ _
    (unitaryGroupUniv n)
  simp [unitaryGroupUniv] at h
  exact h

/-- `U(n)` carries a Haar probability measure. -/
instance instHasHaarProbabilityUnitaryGroup :
    HasHaarProbability (Matrix.unitaryGroup (Fin n) ℂ) where
  haar := unitaryHaar n
  isProb := instIsProbabilityMeasureUnitaryHaar n

end
