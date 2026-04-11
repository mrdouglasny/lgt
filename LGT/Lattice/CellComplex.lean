/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cell Complex Structure of the Lattice ℤᵈ

The lattice ℤᵈ (or its finite quotient (ℤ/Nℤ)ᵈ) has a natural cell
complex structure:
- 0-cells (sites/vertices): points in ℤᵈ
- 1-cells (links/edges): directed edges between nearest neighbors
- 2-cells (plaquettes/faces): unit squares

This module defines these cells and their boundary/coboundary maps,
providing the foundation for discrete differential geometry and
lattice gauge theory.

## Main definitions

- `LatticeSite d N` — sites of (ℤ/Nℤ)ᵈ
- `LatticeLink d N` — oriented links (site + direction)
- `LatticePlaquette d N` — oriented plaquettes (site + two directions)
- `linkSource`, `linkTarget` — boundary of a link
- `plaquetteBoundary` — oriented boundary of a plaquette (4 links)

## References

- Chatterjee, "Gauge Theory Lecture Notes" (2026), §15.2, App C.8
- Wilson, Phys. Rev. D 10 (1974), 2445
-/

import Mathlib.Data.ZMod.Basic

/-! ## Sites, links, and plaquettes -/

/-- A site (0-cell) on the d-dimensional lattice (ℤ/Nℤ)ᵈ. -/
abbrev LatticeSite (d : ℕ) (N : ℕ) := Fin d → ZMod N

/-- A link (oriented 1-cell) on the lattice: a site plus a direction.
The link goes from `site` to `site + e_dir` where e_dir is the
unit vector in direction `dir`. -/
structure LatticeLink (d : ℕ) (N : ℕ) where
  /-- The source site of the link. -/
  site : LatticeSite d N
  /-- The direction of the link (which coordinate axis). -/
  dir : Fin d
  deriving DecidableEq

/-- A plaquette (oriented 2-cell) on the lattice: a site plus two
distinct directions. The plaquette is the unit square in the plane
spanned by directions `dir1` and `dir2`, with `dir1 < dir2`. -/
structure LatticePlaquette (d : ℕ) (N : ℕ) where
  /-- The corner site of the plaquette. -/
  site : LatticeSite d N
  /-- First direction (row). -/
  dir1 : Fin d
  /-- Second direction (column), must satisfy dir1 < dir2. -/
  dir2 : Fin d
  /-- Orientation: dir1 < dir2. -/
  h_lt : dir1 < dir2
  deriving DecidableEq

/-! ## Lattice navigation -/

/-- Shift a site by one step in direction `μ`. -/
def siteShift (d N : ℕ) (x : LatticeSite d N) (μ : Fin d) :
    LatticeSite d N :=
  Function.update x μ (x μ + 1)

/-- The source of a link. -/
def LatticeLink.source (l : LatticeLink d N) : LatticeSite d N :=
  l.site

/-- The target of a link (source shifted by one in the link direction). -/
def LatticeLink.target (l : LatticeLink d N) : LatticeSite d N :=
  siteShift d N l.site l.dir

/-- The reverse of a link (same sites, opposite orientation). -/
def LatticeLink.reverse (l : LatticeLink d N) : LatticeLink d N :=
  ⟨l.target, l.dir⟩

/-! ## Plaquette boundary

The boundary of a plaquette consists of 4 oriented links forming
a closed loop:

```
    x + e₂ ←——— x + e₁ + e₂
      |                |
      |    plaquette   |
      |                |
      x ————→ x + e₁
```

Going counterclockwise: right, up, left, down.
The boundary is: l₁ + l₂ - l₃ - l₄ where
  l₁ = (x, e₁), l₂ = (x+e₁, e₂), l₃ = (x+e₂, e₁), l₄ = (x, e₂)
-/

/-- The four links forming the boundary of a plaquette, in order:
right, up, left⁻¹, down⁻¹. -/
def LatticePlaquette.boundaryLinks (p : LatticePlaquette d N) :
    Fin 4 → LatticeLink d N
  | 0 => ⟨p.site, p.dir1⟩                              -- right
  | 1 => ⟨siteShift d N p.site p.dir1, p.dir2⟩         -- up
  | 2 => ⟨siteShift d N p.site p.dir2, p.dir1⟩         -- left (reversed)
  | 3 => ⟨p.site, p.dir2⟩                              -- down (reversed)

/-- The orientation signs of the boundary links:
+1 for forward, -1 for backward. -/
def LatticePlaquette.boundarySigns : Fin 4 → Int
  | 0 => 1    -- right: forward
  | 1 => 1    -- up: forward
  | 2 => -1   -- left: backward (reversed)
  | 3 => -1   -- down: backward (reversed)

end
