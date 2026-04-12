/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Gauge Group Infrastructure

`HasGaugeTrace G n` provides a representation G →* M_n(ℂ) with trace.

## References

- Chatterjee (2026), §15.2
-/

import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Complex.Basic

/-- A matrix representation for the gauge group. -/
class HasGaugeTrace (G : Type*) (n : ℕ) [Group G] where
  rep : G →* Matrix (Fin n) (Fin n) ℂ

/-- Complex trace of a group element in the gauge representation. -/
def gaugeTrace (G : Type*) (n : ℕ) [Group G] [HasGaugeTrace G n] (g : G) : ℂ :=
  Matrix.trace (HasGaugeTrace.rep (G := G) (n := n) g)

/-- Real part of the trace. -/
def gaugeReTr (G : Type*) (n : ℕ) [Group G] [HasGaugeTrace G n] (g : G) : ℝ :=
  (gaugeTrace G n g).re

/-- Wilson action integrand: Re Tr(I - U_p) = n - Re Tr(U_p). -/
def wilsonPlaquetteCost (G : Type*) (n : ℕ) [Group G] [HasGaugeTrace G n] (Up : G) : ℝ :=
  ↑n - gaugeReTr G n Up
