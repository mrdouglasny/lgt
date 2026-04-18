/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# HasGaugeTrace instance for the Unitary Group U(n)

Concrete instantiation of `HasGaugeTrace` for `Matrix.unitaryGroup (Fin n) ℂ`,
with proofs of the trace bounds and continuity needed by `ym_mass_gap_strong_coupling`.

## Main results

* `instHasGaugeTraceUnitaryGroup` -- `HasGaugeTrace (Matrix.unitaryGroup (Fin n) ℂ) n`
* `unitaryGroup_gaugeReTr_le` -- `gaugeReTr G n g ≤ ↑n`
* `unitaryGroup_gaugeReTr_neg_le` -- `-↑n ≤ gaugeReTr G n g`
* `unitaryGroup_rep_continuous` -- `Continuous (HasGaugeTrace.rep)`
-/

import LGT.GaugeField.GaugeGroup
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.Instances.Matrix
import Mathlib.Data.Complex.BigOperators

open Matrix Complex Finset

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

end
