/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Integrability of Continuous Functions on Compact Groups

On a compact space with a finite measure, every continuous function
is integrable. Supplies the integrability witnesses needed in the
YM mass gap proof.

## Main result

- `continuous_integrable_of_compactSpace` — Continuous f → Integrable f μ
-/

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousMap.Compact

open MeasureTheory

/-- A continuous function on a compact space is integrable w.r.t. any
finite measure.

Proof: on a compact space, every continuous function has compact support
(since tsupport f ⊆ univ, which is compact). A continuous function with
compact support is integrable by `Continuous.integrable_of_hasCompactSupport`. -/
theorem continuous_integrable_of_compactSpace
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : X → E} (hf : Continuous f)
    {μ : Measure X} [IsFiniteMeasure μ] :
    Integrable f μ := by
  apply hf.integrable_of_hasCompactSupport
  exact IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport f)
    (Set.subset_univ _)
