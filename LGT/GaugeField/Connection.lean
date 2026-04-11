/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lattice Gauge Connections

A lattice gauge field (connection) assigns to each oriented link
an element of a compact Lie group G. This is the discrete analogue
of a connection 1-form on a principal G-bundle.

## Main definitions

- `GaugeConnection G d N` — a G-valued function on links
- `plaquetteHolonomy` — ordered product of group elements around a plaquette
- `wilsonAction` — the Wilson plaquette action S = -β Σ Re Tr U_p

## References

- Chatterjee, "Gauge Theory Lecture Notes" (2026), §15.2
- Wilson, Phys. Rev. D 10 (1974), 2445
-/

import LGT.Lattice.CellComplex

/-! ## Gauge connections -/

/-- A lattice gauge connection: assigns a group element to each link.
U(l) represents parallel transport along link l. -/
def GaugeConnection (G : Type*) (d : ℕ) (N : ℕ) := LatticeLink d N → G

variable {G : Type*} [Group G]

/-- The holonomy (ordered product) around a plaquette.
For plaquette p with boundary links l₁, l₂, l₃⁻¹, l₄⁻¹:
  U_p = U(l₁) · U(l₂) · U(l₃)⁻¹ · U(l₄)⁻¹  -/
def plaquetteHolonomy (U : GaugeConnection G d N) (p : LatticePlaquette d N) : G :=
  let links := p.boundaryLinks
  U (links 0) * U (links 1) * (U (links 2))⁻¹ * (U (links 3))⁻¹

end
