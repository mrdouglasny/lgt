/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# HasGaugeTrace instance for the Special Unitary Group SU(n)

Concrete instantiation of `HasGaugeTrace` for `Matrix.specialUnitaryGroup (Fin n) ℂ`,
mirroring `LGT/GaugeField/UnitaryGroup.lean`.

`SU(n)` is the physically relevant gauge group for Yang--Mills theory, and the
existing `U(n)` instantiation does not cover it: `specialUnitaryGroup` is a
distinct Mathlib type (`unitaryGroup n α ⊓ MonoidHom.mker detMonoidHom`), so
none of the `U(n)` instances apply to it by unification.

Every result here is obtained by transport along the inclusion
`SU(n) → U(n)`, so no new mathematics is introduced: the trace bounds and
continuity are the `U(n)` statements pulled back, and compactness is
closedness of the determinant condition intersected with `U(n)`.

## Main results

* `specialUnitaryGroupIncl` -- the monoid hom `SU(n) → M_n(ℂ)`
* `specialUnitaryGroupToUnitaryGroup` -- the monoid hom `SU(n) → U(n)`
* `instHasGaugeTraceSpecialUnitaryGroup` -- `HasGaugeTrace (specialUnitaryGroup (Fin n) ℂ) n`
* `specialUnitaryGroup_gaugeReTr_le` -- `gaugeReTr G n g ≤ ↑n`
* `specialUnitaryGroup_gaugeReTr_neg_le` -- `-↑n ≤ gaugeReTr G n g`
* `specialUnitaryGroup_rep_continuous` -- `Continuous (HasGaugeTrace.rep)`
* `instCompactSpaceSpecialUnitaryGroup` -- `CompactSpace (specialUnitaryGroup (Fin n) ℂ)`
* `instSecondCountableTopologySpecialUnitaryGroup`
* `instHasHaarProbabilitySpecialUnitaryGroup`
-/

import LGT.GaugeField.GaugeGroup
import LGT.GaugeField.UnitaryGroup
import LGT.MassGap.YMMeasure
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix Complex Finset MeasureTheory Measure TopologicalSpace

noncomputable section

variable (n : ℕ)

/-! ### The inclusions -/

/-- The inclusion `SU(n) → M_n(ℂ)` as a monoid homomorphism. -/
def specialUnitaryGroupIncl :
    Matrix.specialUnitaryGroup (Fin n) ℂ →* Matrix (Fin n) (Fin n) ℂ where
  toFun U := U.val
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The inclusion `SU(n) → U(n)` as a monoid homomorphism. -/
def specialUnitaryGroupToUnitaryGroup :
    Matrix.specialUnitaryGroup (Fin n) ℂ →* Matrix.unitaryGroup (Fin n) ℂ where
  toFun U := ⟨U.val, U.prop.1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp]
theorem specialUnitaryGroupToUnitaryGroup_val
    (U : Matrix.specialUnitaryGroup (Fin n) ℂ) :
    (specialUnitaryGroupToUnitaryGroup n U).val = U.val := rfl

instance instHasGaugeTraceSpecialUnitaryGroup :
    HasGaugeTrace (Matrix.specialUnitaryGroup (Fin n) ℂ) n where
  rep := specialUnitaryGroupIncl n

/-- `SU(n)` is inhabited by the identity; `ym_mass_gap_strong_coupling`
requires `[Inhabited G]`. -/
instance instInhabitedSpecialUnitaryGroup :
    Inhabited (Matrix.specialUnitaryGroup (Fin n) ℂ) := ⟨ 1 ⟩

/-! ### Trace bounds, transported from `U(n)` -/

/-- The gauge trace of an `SU(n)` element equals that of its image in `U(n)`. -/
theorem specialUnitaryGroup_gaugeTrace_eq
    (g : Matrix.specialUnitaryGroup (Fin n) ℂ) :
    gaugeTrace (Matrix.specialUnitaryGroup (Fin n) ℂ) n g =
      gaugeTrace (Matrix.unitaryGroup (Fin n) ℂ) n
        (specialUnitaryGroupToUnitaryGroup n g) := rfl

theorem specialUnitaryGroup_gaugeReTr_eq
    (g : Matrix.specialUnitaryGroup (Fin n) ℂ) :
    gaugeReTr (Matrix.specialUnitaryGroup (Fin n) ℂ) n g =
      gaugeReTr (Matrix.unitaryGroup (Fin n) ℂ) n
        (specialUnitaryGroupToUnitaryGroup n g) := rfl

theorem specialUnitaryGroup_gaugeReTr_le
    (g : Matrix.specialUnitaryGroup (Fin n) ℂ) :
    gaugeReTr (Matrix.specialUnitaryGroup (Fin n) ℂ) n g ≤ ↑n := by
  rw [specialUnitaryGroup_gaugeReTr_eq]
  exact unitaryGroup_gaugeReTr_le n _

theorem specialUnitaryGroup_gaugeReTr_neg_le
    (g : Matrix.specialUnitaryGroup (Fin n) ℂ) :
    -↑n ≤ gaugeReTr (Matrix.specialUnitaryGroup (Fin n) ℂ) n g := by
  rw [specialUnitaryGroup_gaugeReTr_eq]
  exact unitaryGroup_gaugeReTr_neg_le n _

/-- The Wilson plaquette cost is nonnegative on `SU(n)`. -/
theorem specialUnitaryGroup_wilsonPlaquetteCost_nonneg
    (g : Matrix.specialUnitaryGroup (Fin n) ℂ) :
    0 ≤ wilsonPlaquetteCost (Matrix.specialUnitaryGroup (Fin n) ℂ) n g := by
  have h := specialUnitaryGroup_gaugeReTr_le n g
  simpa [wilsonPlaquetteCost] using h

/-! ### Continuity -/

theorem specialUnitaryGroup_rep_continuous :
    Continuous (HasGaugeTrace.rep
      (G := Matrix.specialUnitaryGroup (Fin n) ℂ) (n := n)) :=
  continuous_subtype_val

/-! ### Compactness

`SU(n)` is the intersection of `U(n)` with the closed condition `det = 1`,
so it is closed; it is contained in the same closed unit ball as `U(n)`.
-/

lemma specialUnitaryGroup_carrier_subset_closedBall :
    (specialUnitaryGroup (Fin n) ℂ).carrier ⊆
      (Metric.closedBall (0 : ℂ) 1).matrix := by
  intro A hA
  exact unitaryGroup_carrier_subset_closedBall n hA.1

lemma isClosed_specialUnitaryGroup :
    IsClosed (specialUnitaryGroup (Fin n) ℂ).carrier := by
  have hdet : IsClosed {A : Matrix (Fin n) (Fin n) ℂ | A.det = 1} :=
    isClosed_eq (Continuous.matrix_det continuous_id) continuous_const
  exact isClosed_unitary.inter hdet

instance instCompactSpaceSpecialUnitaryGroup :
    CompactSpace (Matrix.specialUnitaryGroup (Fin n) ℂ) :=
  isCompact_iff_compactSpace.mp
    (IsCompact.of_isClosed_subset (isCompact_closedBall (0 : ℂ) 1).matrix
      (isClosed_specialUnitaryGroup n)
      (specialUnitaryGroup_carrier_subset_closedBall n))

instance instSecondCountableTopologySpecialUnitaryGroup :
    SecondCountableTopology (Matrix.specialUnitaryGroup (Fin n) ℂ) :=
  Topology.IsInducing.secondCountableTopology (f := Subtype.val) ⟨rfl⟩

/-! ### Topological group structure

Mathlib supplies `IsTopologicalGroup` for `unitary R` but `specialUnitaryGroup`
is a bare `Submonoid` carrying its own `Group` instance, so the instance does
not transfer by unification and is proved here from the induced topology.
-/

instance instIsTopologicalGroupSpecialUnitaryGroup :
    IsTopologicalGroup (Matrix.specialUnitaryGroup (Fin n) ℂ) where
  continuous_mul := by
    refine Topology.IsInducing.subtypeVal.continuous_iff.mpr ?_
    exact (continuous_subtype_val.comp continuous_fst).matrix_mul
      (continuous_subtype_val.comp continuous_snd)
  continuous_inv := by
    refine Topology.IsInducing.subtypeVal.continuous_iff.mpr ?_
    exact continuous_subtype_val.matrix_conjTranspose

/-! ### Haar probability -/

instance instMeasurableSpaceSpecialUnitaryGroup :
    MeasurableSpace (Matrix.specialUnitaryGroup (Fin n) ℂ) := borel _

instance instBorelSpaceSpecialUnitaryGroup :
    BorelSpace (Matrix.specialUnitaryGroup (Fin n) ℂ) := ⟨rfl⟩

/-- The whole special unitary group, viewed as a `PositiveCompacts`. -/
private def specialUnitaryGroupUniv :
    PositiveCompacts (Matrix.specialUnitaryGroup (Fin n) ℂ) where
  toCompacts := ⟨Set.univ, isCompact_univ⟩
  interior_nonempty' := by rw [interior_univ]; exact Set.univ_nonempty

/-- The Haar probability measure on `SU(n)`. -/
noncomputable def specialUnitaryHaar :
    Measure (Matrix.specialUnitaryGroup (Fin n) ℂ) :=
  haarMeasure (specialUnitaryGroupUniv n)

instance instIsProbabilityMeasureSpecialUnitaryHaar :
    IsProbabilityMeasure (specialUnitaryHaar n) := by
  constructor
  show specialUnitaryHaar n Set.univ = 1
  unfold specialUnitaryHaar
  have h := @haarMeasure_self (Matrix.specialUnitaryGroup (Fin n) ℂ) _ _ _ _ _
    (specialUnitaryGroupUniv n)
  simp [specialUnitaryGroupUniv] at h
  exact h

/-- `SU(n)` carries a Haar probability measure. -/
instance instHasHaarProbabilitySpecialUnitaryGroup :
    HasHaarProbability (Matrix.specialUnitaryGroup (Fin n) ℂ) where
  haar := specialUnitaryHaar n
  isProb := instIsProbabilityMeasureSpecialUnitaryHaar n

end
