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

/-- Shifts in different directions commute. -/
theorem siteShift_comm (x : FinLatticeSites d N) (μ ν : Fin d) (h : μ ≠ ν) :
    siteShift d N (siteShift d N x μ) ν = siteShift d N (siteShift d N x ν) μ := by
  ext i
  simp only [siteShift, Function.update]
  split_ifs with h1 h2 h3 h4 <;> subst_eqs <;> simp_all

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

/-! ## Lattice incidence lemmas -/

section IncidenceLemmas

variable {d N : ℕ}

/-- siteShift is injective in the site argument. -/
theorem siteShift_injective (μ : Fin d) :
    Function.Injective (fun x : FinLatticeSites d N => siteShift d N x μ) := by
  intro x y h
  funext i
  by_cases hi : i = μ
  · subst hi
    have h1 := congr_fun h i
    simp only [siteShift] at h1
    rw [Function.update_self, Function.update_self] at h1
    exact add_right_cancel h1
  · have h1 := congr_fun h i
    simp only [siteShift] at h1
    rwa [Function.update_of_ne hi, Function.update_of_ne hi] at h1

/-- Site recovery from two siteShift equations with different dirs. -/
private theorem site_of_cross_shift (s₁ s₂ : FinLatticeSites d N)
    (μ₁ μ₂ : Fin d) (h_lt : μ₁ < μ₂)
    (h₁ : siteShift d N s₁ μ₁ = siteShift d N s₂ μ₁)
    (h₂ : siteShift d N s₁ μ₂ = siteShift d N s₂ μ₂) : s₁ = s₂ :=
  siteShift_injective μ₁ h₁

/-- Helper: recover site equality from mixed siteShift/direct equations. -/
private theorem site_of_shift_and_direct (s₁ s₂ : FinLatticeSites d N)
    (μ : Fin d) (h_shift : siteShift d N s₁ μ = siteShift d N s₂ μ) :
    s₁ = s₂ :=
  siteShift_injective μ h_shift

/-- Core uniqueness: a plaquette is determined by boundary links at positions 0 and 3. -/
theorem plaquette_eq_of_links_03 (p₁ p₂ : LatticePlaquette d N)
    (h0 : p₁.boundaryLinks 0 = p₂.boundaryLinks 0)
    (h3 : p₁.boundaryLinks 3 = p₂.boundaryLinks 3) : p₁ = p₂ := by
  simp only [LatticePlaquette.boundaryLinks, LatticeLink.mk.injEq] at h0 h3
  cases p₁; cases p₂; simp only [LatticePlaquette.mk.injEq]
  exact ⟨h0.1, h0.2, h3.2⟩

/-- Core uniqueness: determined by links at positions 0 and 1. -/
theorem plaquette_eq_of_links_01 (p₁ p₂ : LatticePlaquette d N)
    (h0 : p₁.boundaryLinks 0 = p₂.boundaryLinks 0)
    (h1 : p₁.boundaryLinks 1 = p₂.boundaryLinks 1) : p₁ = p₂ := by
  simp only [LatticePlaquette.boundaryLinks, LatticeLink.mk.injEq] at h0 h1
  cases p₁; cases p₂; simp only [LatticePlaquette.mk.injEq]
  exact ⟨h0.1, h0.2, h1.2⟩

/-- Each boundary link direction is either dir1 or dir2. -/
private theorem boundaryLink_dir_cases (p : LatticePlaquette d N) (k : Fin 4) :
    (p.boundaryLinks k).dir = p.dir1 ∨ (p.boundaryLinks k).dir = p.dir2 := by
  fin_cases k <;> simp [LatticePlaquette.boundaryLinks]

/-- Boundary links at positions 0 and 2 have dir = dir1. -/
private theorem boundaryLink_dir1 (p : LatticePlaquette d N) (k : Fin 4) (hk : k = 0 ∨ k = 2) :
    (p.boundaryLinks k).dir = p.dir1 := by
  rcases hk with rfl | rfl <;> rfl

/-- Boundary links at positions 1 and 3 have dir = dir2. -/
private theorem boundaryLink_dir2 (p : LatticePlaquette d N) (k : Fin 4) (hk : k = 1 ∨ k = 3) :
    (p.boundaryLinks k).dir = p.dir2 := by
  rcases hk with rfl | rfl <;> rfl

-- Shared plaquette bound: two distinct links share at most one plaquette.
set_option maxHeartbeats 3200000 in
theorem shared_plaquettes_le_one
    (x y : LatticeLink d N) (hxy : x ≠ y)
    (plaq : Finset (LatticePlaquette d N)) :
    (plaq.filter (fun p =>
      x ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks ∧
      y ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks)).card ≤ 1 := by
  sorry

end IncidenceLemmas

/-- Maximum number of plaquettes containing a single link: 2(d-1).
(Also defined in DobrushinVerification; kept here for the incidence lemma.) -/
def maxPlaquettesPerLink' (d : ℕ) : ℕ := 2 * (d - 1)

/-- Each link lies on at most `2*(d-1)` plaquettes. -/
theorem plaquettes_per_link_le' {d N : ℕ}
    (ℓ : LatticeLink d N)
    (plaq : Finset (LatticePlaquette d N)) :
    (plaq.filter (fun p =>
      ℓ ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks)).card
        ≤ maxPlaquettesPerLink' d := by
  sorry

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
