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

/-- siteShift changes the μ-component by +1. -/
private theorem siteShift_apply_self (x : FinLatticeSites d N) (μ : Fin d) :
    siteShift d N x μ μ = x μ + 1 := by
  simp [siteShift, Function.update_self]

/-- For N > 2, `(2 : ZMod N) ≠ 0`. -/
private theorem two_ne_zero_zmod (hN : 2 < N) : (2 : ZMod N) ≠ 0 := by
  have h1 : ((2 : ℕ) : ZMod N) = (2 : ZMod N) := by norm_cast
  rw [← h1, Ne, ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt (by omega) hN

/-- For N > 2, double shift does not return to the original site. -/
private theorem siteShift_siteShift_ne (hN : 2 < N) (x : FinLatticeSites d N) (μ : Fin d) :
    siteShift d N (siteShift d N x μ) μ ≠ x := by
  intro h
  have h1 := congr_fun h μ
  simp only [siteShift_apply_self] at h1
  apply two_ne_zero_zmod hN
  have h2 : x μ + 2 = x μ := by linear_combination h1
  linear_combination h2

/-- For N > 1, siteShift does not fix the site. -/
private theorem siteShift_ne_self (hN : 1 < N) (x : FinLatticeSites d N) (μ : Fin d) :
    siteShift d N x μ ≠ x := by
  intro h
  have h1 := congr_fun h μ
  simp only [siteShift_apply_self] at h1
  have h2 : (1 : ZMod N) = 0 := by linear_combination h1
  have h3 : ((1 : ℕ) : ZMod N) = (1 : ZMod N) := by norm_cast
  rw [← h3, ZMod.natCast_eq_zero_iff] at h2
  exact Nat.not_dvd_of_pos_of_lt (by omega) hN h2

/-- If siteShift s₁ μ = s₂ and siteShift s₂ μ = s₁, contradiction for N > 2. -/
private theorem siteShift_cross_absurd (hN : 2 < N)
    (s₁ s₂ : FinLatticeSites d N) (μ : Fin d)
    (h1 : siteShift d N s₁ μ = s₂) (h2 : siteShift d N s₂ μ = s₁) : False :=
  siteShift_siteShift_ne hN s₁ μ (by rw [h1, h2])

/-- siteShift preserves other components. -/
private theorem siteShift_apply_ne (x : FinLatticeSites d N) (μ : Fin d) (ν : Fin d)
    (hne : ν ≠ μ) : siteShift d N x μ ν = x ν := by
  simp [siteShift, Function.update_of_ne hne]

/-- A boundary link's direction is dir1 or dir2. -/
private theorem boundaryLink_mem_dir (p : LatticePlaquette d N) (ℓ : LatticeLink d N)
    (h : ℓ ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks) :
    ℓ.dir = p.dir1 ∨ ℓ.dir = p.dir2 := by
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
  have hdir := boundaryLink_dir_cases p k
  rw [hk] at hdir
  exact hdir

/-- If a boundary link has dir = dir1, its site is p.site or siteShift p.site p.dir2. -/
private theorem boundaryLink_site_of_dir1 (p : LatticePlaquette d N) (ℓ : LatticeLink d N)
    (h : ℓ ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks)
    (hd : ℓ.dir = p.dir1) :
    ℓ.site = p.site ∨ ℓ.site = siteShift d N p.site p.dir2 := by
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
  fin_cases k <;> simp only [LatticePlaquette.boundaryLinks] at hk
  · -- k=0: ⟨p.site, p.dir1⟩ = ℓ
    left; exact (congr_arg LatticeLink.site hk).symm
  · -- k=1: ⟨siteShift site dir1, dir2⟩ = ℓ, dir2 = dir1 contradiction
    exfalso; have hd' := congr_arg LatticeLink.dir hk; simp only at hd'
    exact absurd p.h_lt (not_lt.mpr (le_of_eq (hd'.trans hd)))
  · -- k=2: ⟨siteShift site dir2, dir1⟩ = ℓ
    right; exact (congr_arg LatticeLink.site hk).symm
  · -- k=3: ⟨p.site, dir2⟩ = ℓ, dir2 = dir1 contradiction
    exfalso; have hd' := congr_arg LatticeLink.dir hk; simp only at hd'
    exact absurd p.h_lt (not_lt.mpr (le_of_eq (hd'.trans hd)))

/-- If a boundary link has dir = dir2, its site is p.site or siteShift p.site p.dir1. -/
private theorem boundaryLink_site_of_dir2 (p : LatticePlaquette d N) (ℓ : LatticeLink d N)
    (h : ℓ ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks)
    (hd : ℓ.dir = p.dir2) :
    ℓ.site = p.site ∨ ℓ.site = siteShift d N p.site p.dir1 := by
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
  fin_cases k <;> simp only [LatticePlaquette.boundaryLinks] at hk
  · -- k=0: ⟨p.site, p.dir1⟩ = ℓ, dir1 = dir2 contradiction
    exfalso; have hd' := congr_arg LatticeLink.dir hk; simp only at hd'
    exact absurd p.h_lt (not_lt.mpr (le_of_eq ((hd'.trans hd).symm)))
  · -- k=1: ⟨siteShift site dir1, dir2⟩ = ℓ
    right; exact (congr_arg LatticeLink.site hk).symm
  · -- k=2: ⟨siteShift site dir2, dir1⟩ = ℓ, dir1 = dir2 contradiction
    exfalso; have hd' := congr_arg LatticeLink.dir hk; simp only at hd'
    exact absurd p.h_lt (not_lt.mpr (le_of_eq ((hd'.trans hd).symm)))
  · -- k=3: ⟨p.site, dir2⟩ = ℓ
    left; exact (congr_arg LatticeLink.site hk).symm

/-- If siteShift s₁ μ₁ = siteShift s₂ μ₂ with μ₁ = μ₂, then s₁ = s₂. -/
private theorem siteShift_injective' {μ₁ μ₂ : Fin d} (hμ : μ₁ = μ₂)
    {s₁ s₂ : FinLatticeSites d N}
    (h : siteShift d N s₁ μ₁ = siteShift d N s₂ μ₂) : s₁ = s₂ := by
  subst hμ; exact siteShift_injective μ₁ h

/-- Double siteShift with same dir returning to original gives contradiction. -/
private theorem siteShift_cross_absurd' (hN : 2 < N) {μ₁ μ₂ : Fin d} (hμ : μ₁ = μ₂)
    {s₁ s₂ : FinLatticeSites d N}
    (h1 : siteShift d N s₁ μ₁ = s₂) (h2 : siteShift d N s₂ μ₂ = s₁) : False := by
  subst hμ; exact siteShift_cross_absurd hN s₁ s₂ μ₁ h1 h2

/-- Extensionality for plaquettes (section-local). -/
private theorem plaquette_ext_local {p₁ p₂ : LatticePlaquette d N}
    (hs : p₁.site = p₂.site) (h1 : p₁.dir1 = p₂.dir1) (h2 : p₁.dir2 = p₂.dir2) :
    p₁ = p₂ := by
  cases p₁; cases p₂; simp only [LatticePlaquette.mk.injEq]; exact ⟨hs, h1, h2⟩

/-- siteShift with different dirs on the same site gives different results. -/
private theorem siteShift_ne_of_ne_dir (hN : 1 < N) (s : FinLatticeSites d N) (μ ν : Fin d)
    (hne : μ ≠ ν) : siteShift d N s μ ≠ siteShift d N s ν := by
  intro h
  have h1 := congr_fun h μ
  simp only [siteShift, Function.update_self, Function.update_of_ne hne] at h1
  have h2 : siteShift d N s μ = s := by
    funext i; simp only [siteShift]
    by_cases hi : i = μ
    · subst hi; rw [Function.update_self]; exact h1
    · rw [Function.update_of_ne hi]
  exact siteShift_ne_self hN s μ h2

/-- Double siteShift with different dirs returning to original contradicts N > 1. -/
private theorem siteShift_siteShift_ne_self_cross (hN : 1 < N) (s : FinLatticeSites d N)
    (μ ν : Fin d) (hne : μ ≠ ν)
    (h : siteShift d N (siteShift d N s ν) μ = s) : False := by
  have h1 := congr_fun h ν
  simp only [siteShift, Function.update_of_ne (fun h => hne h.symm), Function.update_self] at h1
  have h2 : siteShift d N s ν = s := by
    funext i; simp only [siteShift]
    by_cases hi : i = ν
    · subst hi; rw [Function.update_self]; exact h1
    · rw [Function.update_of_ne hi]
  exact siteShift_ne_self hN s ν h2

-- Helper: two plaquettes sharing the same pair of distinct boundary links must be equal.
set_option maxHeartbeats 3200000 in
private theorem plaquette_unique_of_two_links (hN : 2 < N)
    (x y : LatticeLink d N) (hxy : x ≠ y)
    (p₁ p₂ : LatticePlaquette d N)
    (hx₁ : x ∈ (Finset.univ : Finset (Fin 4)).image p₁.boundaryLinks)
    (hy₁ : y ∈ (Finset.univ : Finset (Fin 4)).image p₁.boundaryLinks)
    (hx₂ : x ∈ (Finset.univ : Finset (Fin 4)).image p₂.boundaryLinks)
    (hy₂ : y ∈ (Finset.univ : Finset (Fin 4)).image p₂.boundaryLinks) :
    p₁ = p₂ := by
  have hN1 : 1 < N := by omega
  have hxd₁ := boundaryLink_mem_dir p₁ x hx₁
  have hyd₁ := boundaryLink_mem_dir p₁ y hy₁
  have hxd₂ := boundaryLink_mem_dir p₂ x hx₂
  have hyd₂ := boundaryLink_mem_dir p₂ y hy₂
  by_cases hdir : x.dir = y.dir
  · -- CASE: x.dir = y.dir
    have hsite_ne : x.site ≠ y.site := by
      intro h; exact hxy (by cases x; cases y; simp only [LatticeLink.mk.injEq]; exact ⟨h, hdir⟩)
    -- Sub-case: x.dir = p₁.dir1 and x.dir = p₂.dir2 is impossible (and symmetric)
    -- because it leads to p₂.dir1 < p₂.dir2 = p₁.dir1 < p₁.dir2 and the sites can't match
    have cross_absurd : ∀ (p q : LatticePlaquette d N),
        x.dir = p.dir1 → x.dir = q.dir2 →
        x ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks →
        y ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks →
        x ∈ (Finset.univ : Finset (Fin 4)).image q.boundaryLinks →
        y ∈ (Finset.univ : Finset (Fin 4)).image q.boundaryLinks →
        False := by
      intro p q hxp hxq hxp_mem hyp_mem hxq_mem hyq_mem
      have hyp : y.dir = p.dir1 := hdir ▸ hxp
      have hyq : y.dir = q.dir2 := hdir ▸ hxq
      have hxsp := boundaryLink_site_of_dir1 p x hxp_mem hxp
      have hysp := boundaryLink_site_of_dir1 p y hyp_mem hyp
      have hxsq := boundaryLink_site_of_dir2 q x hxq_mem hxq
      have hysq := boundaryLink_site_of_dir2 q y hyq_mem hyq
      -- p.dir2 > p.dir1 = q.dir2 > q.dir1, so q.dir1 ≠ p.dir2
      have hne_dirs : q.dir1 ≠ p.dir2 := ne_of_lt (calc
        q.dir1 < q.dir2 := q.h_lt
        _ = p.dir1 := hxq.symm.trans hxp
        _ < p.dir2 := p.h_lt)
      -- x,y sites from p: {p.site, siteShift p.site p.dir2} (dir1 links)
      -- x,y sites from q: {q.site, siteShift q.site q.dir1} (dir2 links)
      -- Since hsite_ne, one is base and one is shifted for each plaquette
      -- For each plaquette, x.site, y.site ∈ {base, shifted}. Since x.site ≠ y.site,
      -- one is base and the other is shifted. All 4×4 combinations give contradictions.
      -- Tactic approach: rcases all 4 sets, eliminate diagonal by hsite_ne,
      -- and use siteShift arithmetic for the rest.
      rcases hxsp with hxsp | hxsp <;> rcases hysp with hysp | hysp
      · exact hsite_ne (hxsp.trans hysp.symm)
      · -- x=p.site, y=siteShift p.site p.dir2
        rcases hxsq with hxsq | hxsq <;> rcases hysq with hysq | hysq
        · exact hsite_ne (hxsq.trans hysq.symm)
        · -- x=p.site=q.site, y=siteShift p.site p.dir2=siteShift q.site q.dir1
          -- since p.site=q.site, siteShift p.site p.dir2 = siteShift p.site q.dir1
          have heq : p.site = q.site := hxsp.symm.trans hxsq
          have : siteShift d N p.site p.dir2 = siteShift d N p.site q.dir1 :=
            hysp.symm.trans (by rw [← heq] at hysq; exact hysq)
          exact siteShift_ne_of_ne_dir hN1 p.site p.dir2 q.dir1 (Ne.symm hne_dirs) this
        · -- x=p.site=siteShift q.site q.dir1, y=siteShift p.site p.dir2=q.site
          -- siteShift (siteShift q.site q.dir1) p.dir2 = q.site
          have h1 : siteShift d N q.site q.dir1 = p.site := (hxsp.symm.trans hxsq).symm
          have h2 : siteShift d N p.site p.dir2 = q.site := hysp.symm.trans hysq
          exact siteShift_siteShift_ne_self_cross hN1 q.site p.dir2 q.dir1 (Ne.symm hne_dirs)
            (by rw [h1]; exact h2)
        · exact hsite_ne (hxsq.trans hysq.symm)
      · -- x=siteShift p.site p.dir2, y=p.site (symmetric)
        rcases hxsq with hxsq | hxsq <;> rcases hysq with hysq | hysq
        · exact hsite_ne (hxsq.trans hysq.symm)
        · -- x=siteShift p.site p.dir2=q.site, y=p.site=siteShift q.site q.dir1
          have h1 : siteShift d N q.site q.dir1 = p.site := (hysp.symm.trans hysq).symm
          have h2 : siteShift d N p.site p.dir2 = q.site := hxsp.symm.trans hxsq
          exact siteShift_siteShift_ne_self_cross hN1 q.site p.dir2 q.dir1 (Ne.symm hne_dirs)
            (by rw [h1]; exact h2)
        · -- x=siteShift p.site p.dir2=siteShift q.site q.dir1, y=p.site=q.site
          have heq : p.site = q.site := hysp.symm.trans hysq
          have : siteShift d N p.site p.dir2 = siteShift d N p.site q.dir1 :=
            hxsp.symm.trans (by rw [← heq] at hxsq; exact hxsq)
          exact siteShift_ne_of_ne_dir hN1 p.site p.dir2 q.dir1 (Ne.symm hne_dirs) this
        · exact hsite_ne (hxsq.trans hysq.symm)
      · exact hsite_ne (hxsp.trans hysp.symm)
    -- Now handle the 4 direction sub-cases
    rcases hxd₁ with hx1₁ | hx1₁ <;> rcases hxd₂ with hx1₂ | hx1₂
    · -- x.dir = p₁.dir1, x.dir = p₂.dir1: "same" case
      have hy1₁ : y.dir = p₁.dir1 := hdir ▸ hx1₁
      have hy1₂ : y.dir = p₂.dir1 := hdir ▸ hx1₂
      have hxs₁ := boundaryLink_site_of_dir1 p₁ x hx₁ hx1₁
      have hxs₂ := boundaryLink_site_of_dir1 p₂ x hx₂ hx1₂
      have hys₁ := boundaryLink_site_of_dir1 p₁ y hy₁ hy1₁
      have hys₂ := boundaryLink_site_of_dir1 p₂ y hy₂ hy1₂
      -- dir2s equal
      have hdir2_eq : p₁.dir2 = p₂.dir2 := by
        by_contra hne
        rcases hxs₁ with hxs₁ | hxs₁ <;> rcases hys₁ with hys₁ | hys₁
        · exact hsite_ne (hxs₁.trans hys₁.symm)
        · rcases hxs₂ with hxs₂ | hxs₂ <;> rcases hys₂ with hys₂ | hys₂
          · exact hsite_ne (hxs₂.trans hys₂.symm)
          · -- x=p₁.site=p₂.site, y=siteShift p₁.site dir2=siteShift p₂.site dir2
            have heq : p₁.site = p₂.site := hxs₁.symm.trans hxs₂
            have : siteShift d N p₁.site p₁.dir2 = siteShift d N p₁.site p₂.dir2 :=
              hys₁.symm.trans (by rw [← heq] at hys₂; exact hys₂)
            exact siteShift_ne_of_ne_dir hN1 p₁.site p₁.dir2 p₂.dir2 hne this
          · -- x=p₁.site=siteShift p₂.site dir2, y=siteShift p₁.site dir2=p₂.site
            have h1 : siteShift d N p₂.site p₂.dir2 = p₁.site := (hxs₁.symm.trans hxs₂).symm
            have h2 : siteShift d N p₁.site p₁.dir2 = p₂.site := hys₁.symm.trans hys₂
            exact siteShift_siteShift_ne_self_cross hN1 p₂.site p₁.dir2 p₂.dir2 hne
              (by rw [h1]; exact h2)
          · exact hsite_ne (hxs₂.trans hys₂.symm)
        · rcases hxs₂ with hxs₂ | hxs₂ <;> rcases hys₂ with hys₂ | hys₂
          · exact hsite_ne (hxs₂.trans hys₂.symm)
          · -- x=siteShift p₁.site dir2=p₂.site, y=p₁.site=siteShift p₂.site dir2
            have h1 : siteShift d N p₂.site p₂.dir2 = p₁.site := (hys₁.symm.trans hys₂).symm
            have h2 : siteShift d N p₁.site p₁.dir2 = p₂.site := hxs₁.symm.trans hxs₂
            exact siteShift_siteShift_ne_self_cross hN1 p₂.site p₁.dir2 p₂.dir2 hne
              (by rw [h1]; exact h2)
          · -- x=siteShift p₁.site dir2=siteShift p₂.site dir2, y=p₁.site=p₂.site
            have heq : p₁.site = p₂.site := hys₁.symm.trans hys₂
            have : siteShift d N p₁.site p₁.dir2 = siteShift d N p₁.site p₂.dir2 :=
              hxs₁.symm.trans (by rw [← heq] at hxs₂; exact hxs₂)
            exact siteShift_ne_of_ne_dir hN1 p₁.site p₁.dir2 p₂.dir2 hne this
          · exact hsite_ne (hxs₂.trans hys₂.symm)
        · exact hsite_ne (hxs₁.trans hys₁.symm)
      -- sites equal
      have hsite_eq : p₁.site = p₂.site := by
        rcases hxs₁ with hxs₁ | hxs₁ <;> rcases hys₁ with hys₁ | hys₁
        · exact absurd (hxs₁.trans hys₁.symm) hsite_ne
        · -- x=p₁.site, y=siteShift p₁.site dir2
          rcases hxs₂ with hxs₂ | hxs₂
          · exact hxs₁.symm.trans hxs₂
          · rcases hys₂ with hys₂ | hys₂
            · -- y=siteShift p₁.site dir2=p₂.site, x=p₁.site=siteShift p₂.site dir2
              exfalso
              have h1 : siteShift d N p₁.site p₁.dir2 = p₂.site := hys₁.symm.trans hys₂
              have h2 : p₁.site = siteShift d N p₂.site p₂.dir2 := hxs₁.symm.trans hxs₂
              exact siteShift_cross_absurd' hN hdir2_eq h1 h2.symm
            · exact siteShift_injective' hdir2_eq (hys₁.symm.trans hys₂)
        · rcases hys₂ with hys₂ | hys₂
          · exact hys₁.symm.trans hys₂
          · rcases hxs₂ with hxs₂ | hxs₂
            · exfalso
              have h1 : siteShift d N p₁.site p₁.dir2 = p₂.site := hxs₁.symm.trans hxs₂
              have h2 : p₁.site = siteShift d N p₂.site p₂.dir2 := hys₁.symm.trans hys₂
              exact siteShift_cross_absurd' hN hdir2_eq h1 h2.symm
            · exact siteShift_injective' hdir2_eq (hxs₁.symm.trans hxs₂)
        · exact absurd (hxs₁.trans hys₁.symm) hsite_ne
      exact plaquette_ext_local hsite_eq (hx1₁.symm.trans hx1₂) hdir2_eq
    · -- x.dir = p₁.dir1, x.dir = p₂.dir2: impossible
      exact absurd (cross_absurd p₁ p₂ hx1₁ hx1₂ hx₁ hy₁ hx₂ hy₂) False.elim
    · -- x.dir = p₁.dir2, x.dir = p₂.dir1: impossible (symmetric)
      exact absurd (cross_absurd p₂ p₁ hx1₂ hx1₁ hx₂ hy₂ hx₁ hy₁) False.elim
    · -- x.dir = p₁.dir2, x.dir = p₂.dir2: "same" case (symmetric)
      have hy1₁ : y.dir = p₁.dir2 := hdir ▸ hx1₁
      have hy1₂ : y.dir = p₂.dir2 := hdir ▸ hx1₂
      have hxs₁ := boundaryLink_site_of_dir2 p₁ x hx₁ hx1₁
      have hxs₂ := boundaryLink_site_of_dir2 p₂ x hx₂ hx1₂
      have hys₁ := boundaryLink_site_of_dir2 p₁ y hy₁ hy1₁
      have hys₂ := boundaryLink_site_of_dir2 p₂ y hy₂ hy1₂
      -- dir1s equal
      have hdir1_eq : p₁.dir1 = p₂.dir1 := by
        by_contra hne
        rcases hxs₁ with hxs₁ | hxs₁ <;> rcases hys₁ with hys₁ | hys₁
        · exact hsite_ne (hxs₁.trans hys₁.symm)
        · rcases hxs₂ with hxs₂ | hxs₂ <;> rcases hys₂ with hys₂ | hys₂
          · exact hsite_ne (hxs₂.trans hys₂.symm)
          · have heq : p₁.site = p₂.site := hxs₁.symm.trans hxs₂
            have : siteShift d N p₁.site p₁.dir1 = siteShift d N p₁.site p₂.dir1 :=
              hys₁.symm.trans (by rw [← heq] at hys₂; exact hys₂)
            exact siteShift_ne_of_ne_dir hN1 p₁.site p₁.dir1 p₂.dir1 hne this
          · have h1 : siteShift d N p₂.site p₂.dir1 = p₁.site := (hxs₁.symm.trans hxs₂).symm
            have h2 : siteShift d N p₁.site p₁.dir1 = p₂.site := hys₁.symm.trans hys₂
            exact siteShift_siteShift_ne_self_cross hN1 p₂.site p₁.dir1 p₂.dir1 hne
              (by rw [h1]; exact h2)
          · exact hsite_ne (hxs₂.trans hys₂.symm)
        · rcases hxs₂ with hxs₂ | hxs₂ <;> rcases hys₂ with hys₂ | hys₂
          · exact hsite_ne (hxs₂.trans hys₂.symm)
          · have h1 : siteShift d N p₂.site p₂.dir1 = p₁.site := (hys₁.symm.trans hys₂).symm
            have h2 : siteShift d N p₁.site p₁.dir1 = p₂.site := hxs₁.symm.trans hxs₂
            exact siteShift_siteShift_ne_self_cross hN1 p₂.site p₁.dir1 p₂.dir1 hne
              (by rw [h1]; exact h2)
          · have heq : p₁.site = p₂.site := hys₁.symm.trans hys₂
            have : siteShift d N p₁.site p₁.dir1 = siteShift d N p₁.site p₂.dir1 :=
              hxs₁.symm.trans (by rw [← heq] at hxs₂; exact hxs₂)
            exact siteShift_ne_of_ne_dir hN1 p₁.site p₁.dir1 p₂.dir1 hne this
          · exact hsite_ne (hxs₂.trans hys₂.symm)
        · exact hsite_ne (hxs₁.trans hys₁.symm)
      -- sites equal
      have hsite_eq : p₁.site = p₂.site := by
        rcases hxs₁ with hxs₁ | hxs₁ <;> rcases hys₁ with hys₁ | hys₁
        · exact absurd (hxs₁.trans hys₁.symm) hsite_ne
        · rcases hxs₂ with hxs₂ | hxs₂
          · exact hxs₁.symm.trans hxs₂
          · rcases hys₂ with hys₂ | hys₂
            · exfalso
              have h1 : siteShift d N p₁.site p₁.dir1 = p₂.site := hys₁.symm.trans hys₂
              have h2 : p₁.site = siteShift d N p₂.site p₂.dir1 := hxs₁.symm.trans hxs₂
              exact siteShift_cross_absurd' hN hdir1_eq h1 h2.symm
            · exact siteShift_injective' hdir1_eq (hys₁.symm.trans hys₂)
        · rcases hys₂ with hys₂ | hys₂
          · exact hys₁.symm.trans hys₂
          · rcases hxs₂ with hxs₂ | hxs₂
            · exfalso
              have h1 : siteShift d N p₁.site p₁.dir1 = p₂.site := hxs₁.symm.trans hxs₂
              have h2 : p₁.site = siteShift d N p₂.site p₂.dir1 := hys₁.symm.trans hys₂
              exact siteShift_cross_absurd' hN hdir1_eq h1 h2.symm
            · exact siteShift_injective' hdir1_eq (hxs₁.symm.trans hxs₂)
        · exact absurd (hxs₁.trans hys₁.symm) hsite_ne
      exact plaquette_ext_local hsite_eq hdir1_eq (hx1₁.symm.trans hx1₂)
  · -- CASE: x.dir ≠ y.dir
    -- Step 1: Show p₁.dir1 = p₂.dir1
    have hd1_eq : p₁.dir1 = p₂.dir1 := by
      -- hx1 : x.dir = p.dir1, hx2 : x.dir = p.dir2, etc.
      rcases hxd₁ with hx1 | hx2 <;> rcases hyd₁ with hy1 | hy2
      · -- x.dir = y.dir (both = dir1), contradicts hdir
        exact absurd (hx1.trans hy1.symm) hdir
      · -- x.dir = p₁.dir1, y.dir = p₁.dir2
        rcases hxd₂ with hx1' | hx2'
        · -- x.dir = p₂.dir1: p₁.dir1 = x.dir = p₂.dir1
          exact hx1.symm.trans hx1'
        · -- x.dir = p₂.dir2
          rcases hyd₂ with hy1' | hy2'
          · -- y.dir = p₂.dir1: chain of inequalities gives contradiction
            exfalso; exact lt_irrefl (p₂.dir1 : Fin d) (calc
              p₂.dir1 = y.dir := hy1'.symm
              _ = p₁.dir2 := hy2
              _ > p₁.dir1 := p₁.h_lt
              _ = x.dir := hx1.symm
              _ = p₂.dir2 := hx2'
              _ > p₂.dir1 := p₂.h_lt)
          · -- y.dir = p₂.dir2 = x.dir, contradicts hdir
            exact absurd (hx2'.trans hy2'.symm) hdir
      · -- x.dir = p₁.dir2, y.dir = p₁.dir1
        rcases hyd₂ with hy1' | hy2'
        · exact hy1.symm.trans hy1'
        · rcases hxd₂ with hx1' | hx2'
          · exfalso; exact lt_irrefl (p₁.dir1 : Fin d) (calc
              p₁.dir1 = y.dir := hy1.symm
              _ = p₂.dir2 := hy2'
              _ > p₂.dir1 := p₂.h_lt
              _ = x.dir := hx1'.symm
              _ = p₁.dir2 := hx2
              _ > p₁.dir1 := p₁.h_lt)
          · exact absurd (hx2'.trans hy2'.symm) hdir
      · -- both = dir2, contradicts hdir
        exact absurd (hx2.trans hy2.symm) hdir
    -- Step 2: Show p₁.dir2 = p₂.dir2
    have hd2_eq : p₁.dir2 = p₂.dir2 := by
      rcases hxd₁ with hx1 | hx2 <;> rcases hyd₁ with hy1 | hy2
      · exact absurd (hx1.trans hy1.symm) hdir
      · -- x.dir = p₁.dir1, y.dir = p₁.dir2
        rcases hyd₂ with hy1' | hy2'
        · -- y.dir = p₂.dir1 means p₁.dir2 = y.dir = p₂.dir1 = p₁.dir1, contradicts h_lt
          exfalso; exact absurd p₁.h_lt (not_lt.mpr (le_of_eq
            (show p₁.dir2 = p₁.dir1 from hy2.symm.trans (hy1'.trans hd1_eq.symm))))
        · -- y.dir = p₂.dir2
          exact hy2.symm.trans hy2'
      · rcases hxd₂ with hx1' | hx2'
        · exfalso; exact absurd p₁.h_lt (not_lt.mpr (le_of_eq
            (show p₁.dir2 = p₁.dir1 from hx2.symm.trans (hx1'.trans hd1_eq.symm))))
        · exact hx2.symm.trans hx2'
      · exact absurd (hx2.trans hy2.symm) hdir
    -- Step 3: Show p₁.site = p₂.site
    have hsite_eq : p₁.site = p₂.site := by
      rcases hxd₁ with hx1 | hx2
      · -- x.dir = p₁.dir1
        have hxs₁ := boundaryLink_site_of_dir1 p₁ x hx₁ hx1
        have hxs₂ := boundaryLink_site_of_dir1 p₂ x hx₂ (hx1.trans hd1_eq)
        have hy2₁ : y.dir = p₁.dir2 := (hyd₁.resolve_left (fun h => hdir (hx1.trans h.symm)))
        have hys₁ := boundaryLink_site_of_dir2 p₁ y hy₁ hy2₁
        have hys₂ := boundaryLink_site_of_dir2 p₂ y hy₂ (hy2₁.trans hd2_eq)
        rcases hxs₁ with hxs₁ | hxs₁ <;> rcases hxs₂ with hxs₂ | hxs₂
        · exact hxs₁.symm.trans hxs₂
        · -- x=p₁.site, x=siteShift p₂.site p₂.dir2
          rcases hys₁ with hys₁ | hys₁ <;> rcases hys₂ with hys₂ | hys₂
          · exact hys₁.symm.trans hys₂
          · -- y=p₁.site=siteShift p₂.site p₂.dir1, x=p₁.site=siteShift p₂.site p₂.dir2
            exfalso; exact siteShift_ne_of_ne_dir hN1 p₂.site p₂.dir2 p₂.dir1 (ne_of_gt p₂.h_lt)
              ((hxs₁.symm.trans hxs₂).symm.trans (hys₁.symm.trans hys₂))
          · -- y=siteShift p₁.site p₁.dir1=p₂.site, x=p₁.site=siteShift p₂.site p₂.dir2
            exfalso; exact siteShift_siteShift_ne_self_cross hN1 p₂.site p₂.dir1 p₂.dir2
              (ne_of_lt p₂.h_lt)
              (by rw [show siteShift d N p₂.site p₂.dir2 = p₁.site from
                    (hxs₁.symm.trans hxs₂).symm,
                  show p₂.dir1 = p₁.dir1 from hd1_eq.symm]
                  exact hys₁.symm.trans hys₂)
          · -- y=siteShift p₁.site p₁.dir1=siteShift p₂.site p₂.dir1
            exact siteShift_injective' hd1_eq (hys₁.symm.trans hys₂)
        · -- x=siteShift p₁.site p₁.dir2=p₂.site
          rcases hys₁ with hys₁ | hys₁ <;> rcases hys₂ with hys₂ | hys₂
          · exact hys₁.symm.trans hys₂
          · -- y=p₁.site=siteShift p₂.site p₂.dir1
            exfalso; exact siteShift_siteShift_ne_self_cross hN1 p₁.site p₁.dir1 p₁.dir2
              (ne_of_lt p₁.h_lt)
              (by rw [show siteShift d N p₁.site p₁.dir2 = p₂.site from
                    hxs₁.symm.trans hxs₂,
                  show p₁.dir1 = p₂.dir1 from hd1_eq]
                  exact (hys₂.symm.trans hys₁))
          · -- y=siteShift p₁.site p₁.dir1=p₂.site, x=siteShift p₁.site p₁.dir2=p₂.site
            exfalso; exact siteShift_ne_of_ne_dir hN1 p₁.site p₁.dir1 p₁.dir2 (ne_of_lt p₁.h_lt)
              ((hys₁.symm.trans hys₂).trans (hxs₂.symm.trans hxs₁))
          · exact siteShift_injective' hd1_eq (hys₁.symm.trans hys₂)
        · -- x=siteShift p₁.site p₁.dir2=siteShift p₂.site p₂.dir2
          exact siteShift_injective' hd2_eq (hxs₁.symm.trans hxs₂)
      · -- x.dir = p₁.dir2, use y for dir1
        have hxs₁ := boundaryLink_site_of_dir2 p₁ x hx₁ hx2
        have hxs₂ := boundaryLink_site_of_dir2 p₂ x hx₂ (hx2.trans hd2_eq)
        have hy1₁ : y.dir = p₁.dir1 := (hyd₁.resolve_right (fun h => hdir (hx2.trans h.symm)))
        have hys₁ := boundaryLink_site_of_dir1 p₁ y hy₁ hy1₁
        have hys₂ := boundaryLink_site_of_dir1 p₂ y hy₂ (hy1₁.trans hd1_eq)
        rcases hys₁ with hys₁ | hys₁ <;> rcases hys₂ with hys₂ | hys₂
        · exact hys₁.symm.trans hys₂
        · -- y=p₁.site, y=siteShift p₂.site p₂.dir2
          rcases hxs₁ with hxs₁ | hxs₁ <;> rcases hxs₂ with hxs₂ | hxs₂
          · exact hxs₁.symm.trans hxs₂
          · exfalso; exact siteShift_ne_of_ne_dir hN1 p₂.site p₂.dir2 p₂.dir1 (ne_of_gt p₂.h_lt)
              ((hys₁.symm.trans hys₂).symm.trans (hxs₁.symm.trans hxs₂))
          · exfalso; exact siteShift_siteShift_ne_self_cross hN1 p₂.site p₂.dir1 p₂.dir2
              (ne_of_lt p₂.h_lt)
              (by rw [show siteShift d N p₂.site p₂.dir2 = p₁.site from
                    (hys₁.symm.trans hys₂).symm,
                  show p₂.dir1 = p₁.dir1 from hd1_eq.symm]
                  exact hxs₁.symm.trans hxs₂)
          · exact siteShift_injective' hd1_eq (hxs₁.symm.trans hxs₂)
        · -- y=siteShift p₁.site p₁.dir2=p₂.site
          rcases hxs₁ with hxs₁ | hxs₁ <;> rcases hxs₂ with hxs₂ | hxs₂
          · exact hxs₁.symm.trans hxs₂
          · exfalso; exact siteShift_siteShift_ne_self_cross hN1 p₁.site p₁.dir1 p₁.dir2
              (ne_of_lt p₁.h_lt)
              (by rw [show siteShift d N p₁.site p₁.dir2 = p₂.site from
                    hys₁.symm.trans hys₂,
                  show p₁.dir1 = p₂.dir1 from hd1_eq]
                  exact hxs₂.symm.trans hxs₁)
          · exfalso; exact siteShift_ne_of_ne_dir hN1 p₁.site p₁.dir2 p₁.dir1 (ne_of_gt p₁.h_lt)
              (((hxs₁.symm.trans hxs₂).trans (hys₂.symm.trans hys₁)).symm)
          · exact siteShift_injective' hd1_eq (hxs₁.symm.trans hxs₂)
        · exact siteShift_injective' hd2_eq (hys₁.symm.trans hys₂)
    exact plaquette_ext_local hsite_eq hd1_eq hd2_eq

-- Shared plaquette bound: two distinct links share at most one plaquette.
-- Requires N ≥ 3: on (ℤ/2ℤ)ᵈ, siteShift wraps in 2 steps.
set_option maxHeartbeats 3200000 in
theorem shared_plaquettes_le_one
    (hN : 2 < N)
    (x y : LatticeLink d N) (hxy : x ≠ y)
    (plaq : Finset (LatticePlaquette d N)) :
    (plaq.filter (fun p =>
      x ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks ∧
      y ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p₁ hp₁ p₂ hp₂
  simp only [Finset.mem_filter] at hp₁ hp₂
  exact plaquette_unique_of_two_links hN x y hxy p₁ p₂ hp₁.2.1 hp₁.2.2 hp₂.2.1 hp₂.2.2

end IncidenceLemmas

/-- Maximum number of plaquettes containing a single link: 2(d-1).
(Also defined in DobrushinVerification; kept here for the incidence lemma.) -/
def maxPlaquettesPerLink' (d : ℕ) : ℕ := 2 * (d - 1)

private theorem plaquette_ext' {d N : ℕ} {p₁ p₂ : LatticePlaquette d N}
    (hs : p₁.site = p₂.site) (h1 : p₁.dir1 = p₂.dir1) (h2 : p₁.dir2 = p₂.dir2) :
    p₁ = p₂ := by
  cases p₁; cases p₂; simp only [LatticePlaquette.mk.injEq]; exact ⟨hs, h1, h2⟩

private theorem boundaryLink_dir_cases' {d N : ℕ} (p : LatticePlaquette d N) (k : Fin 4) :
    (p.boundaryLinks k).dir = p.dir1 ∨ (p.boundaryLinks k).dir = p.dir2 := by
  fin_cases k <;> simp [LatticePlaquette.boundaryLinks]

set_option maxHeartbeats 6400000 in
/-- Each link lies on at most `2*(d-1)` plaquettes. -/
theorem plaquettes_per_link_le' {d N : ℕ}
    (ℓ : LatticeLink d N)
    (plaq : Finset (LatticePlaquette d N)) :
    (plaq.filter (fun p =>
      ℓ ∈ (Finset.univ : Finset (Fin 4)).image p.boundaryLinks)).card
        ≤ maxPlaquettesPerLink' d := by
  open Finset in
  classical
  let S := plaq.filter (fun p =>
    ℓ ∈ (univ : Finset (Fin 4)).image p.boundaryLinks)
  let target := (univ.erase ℓ.dir) ×ˢ (univ : Finset Bool)
  let f : LatticePlaquette d N → Fin d × Bool := fun p =>
    if ℓ.dir = p.dir1 then (p.dir2, decide (p.site = ℓ.site))
    else (p.dir1, decide (p.site = ℓ.site))
  -- Helpers: compute f on each branch
  have hf_eq1 (p : LatticePlaquette d N) (h : ℓ.dir = p.dir1) :
      f p = (p.dir2, decide (p.site = ℓ.site)) := by
    exact if_pos h
  have hf_eq2 (p : LatticePlaquette d N) (h : ℓ.dir ≠ p.dir1) :
      f p = (p.dir1, decide (p.site = ℓ.site)) := by
    exact if_neg h
  -- Helper: if ℓ.dir = p.dir2 then ℓ.dir ≠ p.dir1
  have mk_ne (p : LatticePlaquette d N) (h : ℓ.dir = p.dir2) : ℓ.dir ≠ p.dir1 :=
    -- h.symm : p.dir2 = ℓ.dir; if heq : ℓ.dir = p.dir1 then
    -- heq.symm.trans h : p.dir1 = p.dir2 so p.h_lt contradicted
    fun heq => absurd p.h_lt (not_lt.mpr (le_of_eq (h.symm.trans heq)))
    -- h.symm.trans heq : p.dir2 = p.dir1, le_of_eq : p.dir2 ≤ p.dir1,
    -- not_lt.mpr : ¬(p.dir1 < p.dir2)
  -- Step 1: image lands in target
  have h_image_sub : S.image f ⊆ target := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hx
    obtain ⟨_, hp2⟩ := mem_filter.mp hp
    obtain ⟨k, _, hk⟩ := mem_image.mp hp2
    have hdir := boundaryLink_dir_cases' p k
    rw [hk] at hdir
    -- hdir : ℓ.dir = p.dir1 ∨ ℓ.dir = p.dir2
    show _ ∈ (univ.erase ℓ.dir) ×ˢ (univ : Finset Bool)
    rw [mem_product]
    refine ⟨mem_erase.mpr ⟨?_, mem_univ _⟩, mem_univ _⟩
    rcases hdir with h | h
    · -- h : ℓ.dir = p.dir1, need (f p).1 ≠ ℓ.dir, i.e., p.dir2 ≠ ℓ.dir
      rw [hf_eq1 p h]; dsimp only
      exact fun hab => absurd p.h_lt (not_lt.mpr (le_of_eq (hab.trans h)))
    · -- h : ℓ.dir = p.dir2, need p.dir1 ≠ ℓ.dir
      rw [hf_eq2 p (mk_ne p h)]; dsimp only
      exact fun hab => absurd p.h_lt (not_lt.mpr (le_of_eq (h.symm.trans hab.symm)))
  -- Step 2: f is injective on S
  have h_inj : Set.InjOn f ↑S := by
    intro p₁ hp₁ p₂ hp₂ hfeq
    obtain ⟨_, hp₁'⟩ := mem_filter.mp (mem_coe.mp hp₁)
    obtain ⟨_, hp₂'⟩ := mem_filter.mp (mem_coe.mp hp₂)
    obtain ⟨k₁, _, hk₁⟩ := mem_image.mp hp₁'
    obtain ⟨k₂, _, hk₂⟩ := mem_image.mp hp₂'
    have hd₁ := boundaryLink_dir_cases' p₁ k₁; rw [hk₁] at hd₁
    have hd₂ := boundaryLink_dir_cases' p₂ k₂; rw [hk₂] at hd₂
    -- hd₁ : ℓ.dir = p₁.dir1 ∨ ℓ.dir = p₁.dir2
    -- hd₂ : ℓ.dir = p₂.dir1 ∨ ℓ.dir = p₂.dir2
    rcases hd₁ with h₁₁ | h₁₂ <;> rcases hd₂ with h₂₁ | h₂₂
    -- Case 1: ℓ.dir = p₁.dir1 and ℓ.dir = p₂.dir1
    · rw [hf_eq1 p₁ h₁₁, hf_eq1 p₂ h₂₁] at hfeq
      have hd1 : p₁.dir1 = p₂.dir1 := h₁₁.symm.trans h₂₁
      have hd2 : p₁.dir2 = p₂.dir2 := congr_arg Prod.fst hfeq
      have hsnd : decide (p₁.site = ℓ.site) = decide (p₂.site = ℓ.site) :=
        congr_arg Prod.snd hfeq
      have hsite_iff : p₁.site = ℓ.site ↔ p₂.site = ℓ.site := by
        simp only [decide_eq_decide] at hsnd; exact hsnd
      have hsite : p₁.site = p₂.site := by
        by_cases hs : p₁.site = ℓ.site
        · exact hs.trans (hsite_iff.mp hs).symm
        · have hs₂ : p₂.site ≠ ℓ.site := fun h => hs (hsite_iff.mpr h)
          -- k=2: boundaryLinks 2 = ⟨siteShift site dir2, dir1⟩
          -- so siteShift p.site p.dir2 = ℓ.site
          have hshift₁ : siteShift d N p₁.site p₁.dir2 = ℓ.site := by
            fin_cases k₁ <;> simp only [LatticePlaquette.boundaryLinks] at hk₁ <;>
              first | exact congr_arg LatticeLink.site hk₁
                    | (exfalso; exact hs (congr_arg LatticeLink.site hk₁))
                    | (exfalso; have hd := congr_arg LatticeLink.dir hk₁; simp only at hd; exact absurd p₁.h_lt (by omega))
          have hshift₂ : siteShift d N p₂.site p₂.dir2 = ℓ.site := by
            fin_cases k₂ <;> simp only [LatticePlaquette.boundaryLinks] at hk₂ <;>
              first | exact congr_arg LatticeLink.site hk₂
                    | (exfalso; exact hs₂ (congr_arg LatticeLink.site hk₂))
                    | (exfalso; have hd := congr_arg LatticeLink.dir hk₂; simp only at hd; exact absurd p₂.h_lt (by omega))
          exact siteShift_injective _ (by rw [hd2] at hshift₁; exact hshift₁.trans hshift₂.symm)
      exact plaquette_ext' hsite hd1 hd2
    -- Case 2: ℓ.dir = p₁.dir1 and ℓ.dir = p₂.dir2 (impossible)
    · rw [hf_eq1 p₁ h₁₁, hf_eq2 p₂ (mk_ne p₂ h₂₂)] at hfeq
      exact absurd (calc ℓ.dir = p₁.dir1 := h₁₁
        _ < p₁.dir2 := p₁.h_lt
        _ = p₂.dir1 := congr_arg Prod.fst hfeq
        _ < p₂.dir2 := p₂.h_lt
        _ = ℓ.dir := h₂₂.symm) (lt_irrefl _)
    -- Case 3: ℓ.dir = p₁.dir2 and ℓ.dir = p₂.dir1 (impossible)
    · rw [hf_eq2 p₁ (mk_ne p₁ h₁₂), hf_eq1 p₂ h₂₁] at hfeq
      exact absurd (calc ℓ.dir = p₂.dir1 := h₂₁
        _ < p₂.dir2 := p₂.h_lt
        _ = p₁.dir1 := (congr_arg Prod.fst hfeq).symm
        _ < p₁.dir2 := p₁.h_lt
        _ = ℓ.dir := h₁₂.symm) (lt_irrefl _)
    -- Case 4: ℓ.dir = p₁.dir2 and ℓ.dir = p₂.dir2
    · rw [hf_eq2 p₁ (mk_ne p₁ h₁₂), hf_eq2 p₂ (mk_ne p₂ h₂₂)] at hfeq
      have hd1 : p₁.dir1 = p₂.dir1 := congr_arg Prod.fst hfeq
      have hd2 : p₁.dir2 = p₂.dir2 := h₁₂.symm.trans h₂₂
      have hsnd : decide (p₁.site = ℓ.site) = decide (p₂.site = ℓ.site) :=
        congr_arg Prod.snd hfeq
      have hsite_iff : p₁.site = ℓ.site ↔ p₂.site = ℓ.site := by
        simp only [decide_eq_decide] at hsnd; exact hsnd
      have hsite : p₁.site = p₂.site := by
        by_cases hs : p₁.site = ℓ.site
        · exact hs.trans (hsite_iff.mp hs).symm
        · have hs₂ : p₂.site ≠ ℓ.site := fun h => hs (hsite_iff.mpr h)
          -- k=1: boundaryLinks 1 = ⟨siteShift site dir1, dir2⟩
          have hshift₁ : siteShift d N p₁.site p₁.dir1 = ℓ.site := by
            fin_cases k₁ <;> simp only [LatticePlaquette.boundaryLinks] at hk₁ <;>
              first | exact congr_arg LatticeLink.site hk₁
                    | (exfalso; exact hs (congr_arg LatticeLink.site hk₁))
                    | (exfalso; have hd := congr_arg LatticeLink.dir hk₁; simp only at hd; exact absurd p₁.h_lt (by omega))
          have hshift₂ : siteShift d N p₂.site p₂.dir1 = ℓ.site := by
            fin_cases k₂ <;> simp only [LatticePlaquette.boundaryLinks] at hk₂ <;>
              first | exact congr_arg LatticeLink.site hk₂
                    | (exfalso; exact hs₂ (congr_arg LatticeLink.site hk₂))
                    | (exfalso; have hd := congr_arg LatticeLink.dir hk₂; simp only at hd; exact absurd p₂.h_lt (by omega))
          exact siteShift_injective _ (by rw [hd1] at hshift₁; exact hshift₁.trans hshift₂.symm)
      exact plaquette_ext' hsite hd1 hd2
  -- Step 3: combine
  calc S.card = (S.image f).card := (card_image_of_injOn h_inj).symm
    _ ≤ target.card := card_le_card h_image_sub
    _ = maxPlaquettesPerLink' d := by
        show target.card = _
        rw [show target = (univ.erase ℓ.dir) ×ˢ (univ : Finset Bool) from rfl, card_product, card_erase_of_mem (mem_univ _), card_univ, card_univ,
            Fintype.card_fin, Fintype.card_bool]
        unfold maxPlaquettesPerLink'; omega

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
