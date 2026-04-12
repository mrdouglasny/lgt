/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Cell Complex Structure of the Lattice

Builds on gaussian-field's `FinLatticeSites` and `AsymLatticeSites` to
define links (1-cells) and plaquettes (2-cells) for gauge theory.

## References

- Chatterjee, "Gauge Theory Lecture Notes" (2026), §15.2, App C.8
-/

import Lattice.Sites
import Torus.AsymmetricTorus

open GaussianField

noncomputable section

variable (d : ℕ) (N : ℕ)

/-! ## Links on (ℤ/Nℤ)ᵈ -/

/-- A link (oriented 1-cell): site + direction. -/
structure LatticeLink (d : ℕ) (N : ℕ) where
  site : FinLatticeSites d N
  dir : Fin d
  deriving DecidableEq

/-- Shift a site by +1 in direction μ. -/
def siteShift (x : FinLatticeSites d N) (μ : Fin d) :
    FinLatticeSites d N :=
  Function.update x μ (x μ + 1)

/-- Target of a link. -/
def LatticeLink.target {d N : ℕ} (l : LatticeLink d N) :
    FinLatticeSites d N :=
  siteShift d N l.site l.dir

/-- A plaquette (oriented 2-cell): site + two ordered directions. -/
structure LatticePlaquette (d : ℕ) (N : ℕ) where
  site : FinLatticeSites d N
  dir1 : Fin d
  dir2 : Fin d
  h_lt : dir1 < dir2
  deriving DecidableEq

/-- The four boundary links of a plaquette (counterclockwise). -/
def LatticePlaquette.boundaryLinks {d N : ℕ}
    (p : LatticePlaquette d N) : Fin 4 → LatticeLink d N
  | 0 => ⟨p.site, p.dir1⟩
  | 1 => ⟨siteShift d N p.site p.dir1, p.dir2⟩
  | 2 => ⟨siteShift d N p.site p.dir2, p.dir1⟩  -- reversed
  | 3 => ⟨p.site, p.dir2⟩                        -- reversed

/-! ## 2D asymmetric lattice (for mass gap proof)

Uses `AsymLatticeSites Nt Ns = ZMod Nt × ZMod Ns` from gaussian-field. -/

/-- Direction on a 2D lattice. -/
inductive Dir2D where
  | time : Dir2D
  | space : Dir2D
  deriving DecidableEq, Fintype, Repr

/-- A link on the asymmetric 2D lattice. -/
structure AsymLink (Nt Ns : ℕ) where
  site : AsymLatticeSites Nt Ns
  dir : Dir2D
  deriving DecidableEq

/-- Target of an asymmetric link. -/
def AsymLink.target {Nt Ns : ℕ} (l : AsymLink Nt Ns) :
    AsymLatticeSites Nt Ns :=
  match l.dir with
  | Dir2D.time  => (l.site.1 + 1, l.site.2)
  | Dir2D.space => (l.site.1, l.site.2 + 1)

/-- A plaquette on the 2D lattice (only one orientation: time × space). -/
structure AsymPlaquette (Nt Ns : ℕ) where
  site : AsymLatticeSites Nt Ns
  deriving DecidableEq

/-- Boundary links of a 2D plaquette. -/
def AsymPlaquette.boundaryLinks {Nt Ns : ℕ}
    (p : AsymPlaquette Nt Ns) : Fin 4 → AsymLink Nt Ns
  | 0 => ⟨p.site, Dir2D.time⟩
  | 1 => ⟨(p.site.1 + 1, p.site.2), Dir2D.space⟩
  | 2 => ⟨(p.site.1, p.site.2 + 1), Dir2D.time⟩   -- reversed
  | 3 => ⟨p.site, Dir2D.space⟩                      -- reversed

/-! ## Fintype instances for 2D cells -/

instance (Nt Ns : ℕ) [NeZero Nt] [NeZero Ns] : Fintype (AsymPlaquette Nt Ns) :=
  Fintype.ofEquiv (AsymLatticeSites Nt Ns)
    { toFun := AsymPlaquette.mk
      invFun := AsymPlaquette.site
      left_inv := fun x => rfl
      right_inv := fun p => by cases p; rfl }

end
