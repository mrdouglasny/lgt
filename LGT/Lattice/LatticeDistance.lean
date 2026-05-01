/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Distances on the finite periodic lattice

Collects the torus coordinate distance, the induced site and plaquette
distances, and the ambient shared-plaquette graph distance on links.
-/

import LGT.Lattice.CellComplex
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Tactic

open Classical
open GaussianField

noncomputable section

namespace ZMod

/-- Periodic distance in one coordinate on `ZMod N`. -/
def periodicDist (N : ℕ) (a b : ZMod N) : ℕ :=
  min (ZMod.val (a - b)) (N - ZMod.val (a - b))

lemma periodicDist_eq_natAbs_valMinAbs (N : ℕ) [NeZero N] (a b : ZMod N) :
    periodicDist N a b = (a - b).valMinAbs.natAbs := by
  rw [periodicDist, valMinAbs_natAbs_eq_min]

@[simp]
lemma periodicDist_self (N : ℕ) [NeZero N] (a : ZMod N) :
    periodicDist N a a = 0 := by
  rw [periodicDist_eq_natAbs_valMinAbs]
  simp

lemma periodicDist_comm (N : ℕ) [NeZero N] (a b : ZMod N) :
    periodicDist N a b = periodicDist N b a := by
  rw [periodicDist_eq_natAbs_valMinAbs, periodicDist_eq_natAbs_valMinAbs]
  have h : b - a = -(a - b) := by abel
  rw [h, natAbs_valMinAbs_neg]

lemma periodicDist_triangle (N : ℕ) [NeZero N] (a b c : ZMod N) :
    periodicDist N a c ≤ periodicDist N a b + periodicDist N b c := by
  rw [periodicDist_eq_natAbs_valMinAbs, periodicDist_eq_natAbs_valMinAbs,
    periodicDist_eq_natAbs_valMinAbs]
  have hsub : a - c = (a - b) + (b - c) := by abel
  rw [hsub]
  exact (natAbs_valMinAbs_add_le (a - b) (b - c)).trans (Int.natAbs_add_le _ _)

lemma periodicDist_add_one_self_le_one (N : ℕ) (a : ZMod N) :
    periodicDist N (a + 1) a ≤ 1 := by
  unfold periodicDist
  have hsub : a + 1 - a = (1 : ZMod N) := by abel
  rw [hsub]
  exact (Nat.min_le_left _ _).trans (by
    rw [ZMod.val_one_eq_one_mod]
    exact Nat.mod_le _ _)

end ZMod

/-- L1 distance on the periodic lattice `(ZMod N)^d`. -/
def latticeSiteDist (d N : ℕ) (x y : FinLatticeSites d N) : ℕ :=
  ∑ i : Fin d, ZMod.periodicDist N (x i) (y i)

@[simp]
lemma latticeSiteDist_self (d N : ℕ) [NeZero N] (x : FinLatticeSites d N) :
    latticeSiteDist d N x x = 0 := by
  simp [latticeSiteDist]

lemma latticeSiteDist_comm (d N : ℕ) [NeZero N] (x y : FinLatticeSites d N) :
    latticeSiteDist d N x y = latticeSiteDist d N y x := by
  simp only [latticeSiteDist]
  apply Finset.sum_congr rfl
  intro i _
  exact ZMod.periodicDist_comm N (x i) (y i)

lemma latticeSiteDist_triangle (d N : ℕ) [NeZero N]
    (x y z : FinLatticeSites d N) :
    latticeSiteDist d N x z ≤ latticeSiteDist d N x y + latticeSiteDist d N y z := by
  simp only [latticeSiteDist]
  calc
    ∑ i : Fin d, ZMod.periodicDist N (x i) (z i)
        ≤ ∑ i : Fin d, (ZMod.periodicDist N (x i) (y i) +
            ZMod.periodicDist N (y i) (z i)) := by
          exact Finset.sum_le_sum fun i _ => ZMod.periodicDist_triangle N (x i) (y i) (z i)
    _ = (∑ i : Fin d, ZMod.periodicDist N (x i) (y i)) +
          ∑ i : Fin d, ZMod.periodicDist N (y i) (z i) := by
          rw [Finset.sum_add_distrib]

/-- Distance between plaquettes: L1 distance between anchor sites. -/
def latticePlaquetteDist (d N : ℕ) (p q : LatticePlaquette d N) : ℕ :=
  latticeSiteDist d N p.site q.site

/-- Compatibility name used by existing mass-gap files. -/
def plaquetteDist (d N : ℕ) (p q : LatticePlaquette d N) : ℕ :=
  latticePlaquetteDist d N p q

@[simp]
lemma latticePlaquetteDist_self (d N : ℕ) [NeZero N] (p : LatticePlaquette d N) :
    latticePlaquetteDist d N p p = 0 := by
  simp [latticePlaquetteDist]

lemma latticePlaquetteDist_comm (d N : ℕ) [NeZero N]
    (p q : LatticePlaquette d N) :
    latticePlaquetteDist d N p q = latticePlaquetteDist d N q p := by
  simp [latticePlaquetteDist, latticeSiteDist_comm d N p.site q.site]

lemma latticePlaquetteDist_triangle (d N : ℕ) [NeZero N]
    (p q r : LatticePlaquette d N) :
    latticePlaquetteDist d N p r ≤
      latticePlaquetteDist d N p q + latticePlaquetteDist d N q r :=
  latticeSiteDist_triangle d N p.site q.site r.site

namespace LatticePlaquette

/-- The boundary links of a plaquette as a finset. -/
def boundaryLinkFinset {d N : ℕ} [DecidableEq (LatticeLink d N)]
    (p : LatticePlaquette d N) : Finset (LatticeLink d N) :=
  (Finset.univ : Finset (Fin 4)).image p.boundaryLinks

end LatticePlaquette

lemma latticeSiteDist_siteShift_self_le_one (d N : ℕ) [NeZero N]
    (x : FinLatticeSites d N) (μ : Fin d) :
    latticeSiteDist d N (siteShift d N x μ) x ≤ 1 := by
  classical
  unfold latticeSiteDist
  calc
    ∑ i : Fin d, ZMod.periodicDist N ((siteShift d N x μ) i) (x i)
        ≤ ∑ i : Fin d, (if i = μ then 1 else 0) := by
          apply Finset.sum_le_sum
          intro i _
          by_cases hi : i = μ
          · subst i
            simpa [siteShift] using ZMod.periodicDist_add_one_self_le_one N (x μ)
          · simp [siteShift, hi]
    _ = 1 := by
          simp

lemma boundaryLink_siteDist_le_one (d N : ℕ) [NeZero N]
    (p : LatticePlaquette d N) (k : Fin 4) :
    latticeSiteDist d N ((p.boundaryLinks k).site) p.site ≤ 1 := by
  fin_cases k
  · simp [LatticePlaquette.boundaryLinks]
  · simpa [LatticePlaquette.boundaryLinks] using
      latticeSiteDist_siteShift_self_le_one d N p.site p.dir1
  · simpa [LatticePlaquette.boundaryLinks] using
      latticeSiteDist_siteShift_self_le_one d N p.site p.dir2
  · simp [LatticePlaquette.boundaryLinks]

lemma boundaryLinkFinset_siteDist_le_one (d N : ℕ) [NeZero N]
    [DecidableEq (LatticeLink d N)] (p : LatticePlaquette d N)
    {x : LatticeLink d N} (hx : x ∈ p.boundaryLinkFinset) :
    latticeSiteDist d N x.site p.site ≤ 1 := by
  rcases Finset.mem_image.mp hx with ⟨k, _, hk⟩
  rw [← hk]
  exact boundaryLink_siteDist_le_one d N p k

/-- Plaquette-independent adjacency: two distinct links lie on a common plaquette boundary. -/
def linkAmbientAdj (d N : ℕ) (x y : LatticeLink d N) : Prop :=
  x ≠ y ∧ ∃ p : LatticePlaquette d N,
    (∃ i : Fin 4, p.boundaryLinks i = x) ∧
    (∃ j : Fin 4, p.boundaryLinks j = y)

lemma linkAmbientAdj.symm {d N : ℕ} {x y : LatticeLink d N}
    (h : linkAmbientAdj d N x y) : linkAmbientAdj d N y x := by
  rcases h with ⟨hxy, p, hx, hy⟩
  exact ⟨hxy.symm, p, hy, hx⟩

/-- Ambient shared-plaquette graph on links. -/
def ambientLinkGraph (d N : ℕ) : SimpleGraph (LatticeLink d N) :=
  SimpleGraph.fromRel (linkAmbientAdj d N)

lemma ambientLinkGraph_adj_iff (d N : ℕ) (x y : LatticeLink d N) :
    (ambientLinkGraph d N).Adj x y ↔ linkAmbientAdj d N x y := by
  constructor
  · intro h
    rcases h with ⟨_, hxy | hyx⟩
    · exact hxy
    · exact hyx.symm
  · intro h
    exact ⟨h.1, Or.inl h⟩

/-- Graph distance in the ambient shared-plaquette graph. -/
def linkGraphDist (d N : ℕ) (x y : LatticeLink d N) : ℕ :=
  (ambientLinkGraph d N).dist x y

@[simp]
lemma linkGraphDist_self (d N : ℕ) (x : LatticeLink d N) :
    linkGraphDist d N x x = 0 := by
  simp [linkGraphDist]

lemma linkGraphDist_comm (d N : ℕ) (x y : LatticeLink d N) :
    linkGraphDist d N x y = linkGraphDist d N y x := by
  simp [linkGraphDist, SimpleGraph.dist_comm]

lemma linkAmbientAdj_imp_siteDist_le_two (d N : ℕ) [NeZero N]
    {x y : LatticeLink d N} (h : linkAmbientAdj d N x y) :
    latticeSiteDist d N x.site y.site ≤ 2 := by
  rcases h with ⟨_, p, ⟨i, hi⟩, ⟨j, hj⟩⟩
  have hx : latticeSiteDist d N x.site p.site ≤ 1 := by
    rw [← hi]
    exact boundaryLink_siteDist_le_one d N p i
  have hy : latticeSiteDist d N p.site y.site ≤ 1 := by
    rw [latticeSiteDist_comm d N p.site y.site, ← hj]
    exact boundaryLink_siteDist_le_one d N p j
  have htri := latticeSiteDist_triangle d N x.site p.site y.site
  omega

lemma ambientLinkGraph_adj_imp_siteDist_le_two (d N : ℕ) [NeZero N]
    {x y : LatticeLink d N} (h : (ambientLinkGraph d N).Adj x y) :
    latticeSiteDist d N x.site y.site ≤ 2 :=
  linkAmbientAdj_imp_siteDist_le_two d N ((ambientLinkGraph_adj_iff d N x y).mp h)

lemma ambientLinkGraph_walk_siteDist_bound (d N : ℕ) [NeZero N]
    {x y : LatticeLink d N} (w : (ambientLinkGraph d N).Walk x y) :
    latticeSiteDist d N x.site y.site ≤ 2 * w.length := by
  induction w with
  | nil =>
      simp
  | cons hxy wy ih =>
      rename_i u v w
      have hstep : latticeSiteDist d N u.site v.site ≤ 2 :=
        ambientLinkGraph_adj_imp_siteDist_le_two d N hxy
      have htri := latticeSiteDist_triangle d N u.site v.site w.site
      simp only [SimpleGraph.Walk.length_cons]
      omega

lemma linkGraphDist_triangle_of_connected (d N : ℕ)
    (hconn : (ambientLinkGraph d N).Connected)
    (x y z : LatticeLink d N) :
    linkGraphDist d N x y ≤ linkGraphDist d N x z + linkGraphDist d N z y := by
  simpa [linkGraphDist] using hconn.dist_triangle (u := x) (v := z) (w := y)

lemma linkGraphDist_siteDist_bound_of_connected (d N : ℕ) [NeZero N]
    (hconn : (ambientLinkGraph d N).Connected) (x y : LatticeLink d N) :
    latticeSiteDist d N x.site y.site ≤ 2 * linkGraphDist d N x y := by
  rcases hconn.exists_walk_length_eq_dist x y with ⟨w, hw⟩
  simpa [linkGraphDist, hw] using ambientLinkGraph_walk_siteDist_bound d N w

private lemma siteShift_ne_self_of_one_lt (d N : ℕ) [NeZero N] (hN : 1 < N)
    (x : FinLatticeSites d N) (μ : Fin d) :
    siteShift d N x μ ≠ x := by
  intro h
  have hμ := congr_fun h μ
  simp only [siteShift, Function.update_self] at hμ
  have hzero : ((1 : ℕ) : ZMod N) = 0 := by
    have hsub : x μ + 1 - x μ = (0 : ZMod N) := by
      rw [hμ]
      abel
    simpa using hsub
  rw [ZMod.natCast_eq_zero_iff] at hzero
  exact Nat.not_dvd_of_pos_of_lt (by omega) hN hzero

private lemma linkAmbientAdj_dir_change (d N : ℕ) (s : FinLatticeSites d N)
    {μ ν : Fin d} (hμν : μ ≠ ν) :
    linkAmbientAdj d N ⟨s, μ⟩ ⟨s, ν⟩ := by
  refine ⟨?_, ?_⟩
  · intro h
    exact hμν (congrArg LatticeLink.dir h)
  · rcases lt_or_gt_of_ne hμν with hlt | hgt
    · refine ⟨⟨s, μ, ν, hlt⟩, ?_, ?_⟩
      · exact ⟨0, rfl⟩
      · exact ⟨3, rfl⟩
    · refine ⟨⟨s, ν, μ, hgt⟩, ?_, ?_⟩
      · exact ⟨3, rfl⟩
      · exact ⟨0, rfl⟩

private lemma linkAmbientAdj_transverse_shift (d N : ℕ) [NeZero N] (hN : 1 < N)
    (s : FinLatticeSites d N) {μ ν : Fin d} (hμν : μ ≠ ν) :
    linkAmbientAdj d N ⟨s, μ⟩ ⟨siteShift d N s ν, μ⟩ := by
  refine ⟨?_, ?_⟩
  · intro h
    have hs : s = siteShift d N s ν := congrArg LatticeLink.site h
    exact siteShift_ne_self_of_one_lt d N hN s ν hs.symm
  · rcases lt_or_gt_of_ne hμν with hlt | hgt
    · refine ⟨⟨s, μ, ν, hlt⟩, ?_, ?_⟩
      · exact ⟨0, rfl⟩
      · exact ⟨2, rfl⟩
    · refine ⟨⟨s, ν, μ, hgt⟩, ?_, ?_⟩
      · exact ⟨3, rfl⟩
      · exact ⟨1, rfl⟩

private lemma ambientLinkGraph_reachable_of_linkAmbientAdj (d N : ℕ)
    {x y : LatticeLink d N} (h : linkAmbientAdj d N x y) :
    (ambientLinkGraph d N).Reachable x y :=
  ((ambientLinkGraph_adj_iff d N x y).mpr h).reachable

private lemma exists_fin_ne_of_two_le {d : ℕ} (hd : 2 ≤ d) (μ : Fin d) :
    ∃ ν : Fin d, ν ≠ μ := by
  let z : Fin d := ⟨0, by omega⟩
  let o : Fin d := ⟨1, by omega⟩
  by_cases hμ : μ = z
  · refine ⟨o, ?_⟩
    intro ho
    have hval : (1 : ℕ) = 0 := by
      simpa [o, z] using congrArg Fin.val (ho.trans hμ)
    omega
  · exact ⟨z, fun hz => hμ hz.symm⟩

private lemma link_reachable_siteShift_once (d N : ℕ) [NeZero N]
    (hd : 2 ≤ d) (hN : 2 < N) (s : FinLatticeSites d N) (μ j : Fin d) :
    (ambientLinkGraph d N).Reachable ⟨s, μ⟩ ⟨siteShift d N s j, μ⟩ := by
  by_cases hj : j = μ
  · subst j
    rcases exists_fin_ne_of_two_le hd μ with ⟨ν, hν⟩
    have h1 : (ambientLinkGraph d N).Reachable ⟨s, μ⟩ ⟨s, ν⟩ :=
      ambientLinkGraph_reachable_of_linkAmbientAdj d N
        (linkAmbientAdj_dir_change d N s hν.symm)
    have h2 : (ambientLinkGraph d N).Reachable ⟨s, ν⟩ ⟨siteShift d N s μ, ν⟩ :=
      ambientLinkGraph_reachable_of_linkAmbientAdj d N
        (linkAmbientAdj_transverse_shift d N (by omega : 1 < N) s hν)
    have h3 : (ambientLinkGraph d N).Reachable ⟨siteShift d N s μ, ν⟩
        ⟨siteShift d N s μ, μ⟩ :=
      ambientLinkGraph_reachable_of_linkAmbientAdj d N
        (linkAmbientAdj_dir_change d N (siteShift d N s μ) hν)
    exact h1.trans (h2.trans h3)
  · exact ambientLinkGraph_reachable_of_linkAmbientAdj d N
      (linkAmbientAdj_transverse_shift d N (by omega : 1 < N) s (fun h => hj h.symm))

private def siteShiftN (d N : ℕ) (x : FinLatticeSites d N) (μ : Fin d) : ℕ →
    FinLatticeSites d N
  | 0 => x
  | k + 1 => siteShift d N (siteShiftN d N x μ k) μ

private lemma siteShiftN_apply_self (d N : ℕ) (x : FinLatticeSites d N)
    (μ : Fin d) (k : ℕ) :
    siteShiftN d N x μ k μ = x μ + (k : ZMod N) := by
  induction k with
  | zero =>
      simp [siteShiftN]
  | succ k ih =>
      simp [siteShiftN, siteShift, ih, Nat.cast_succ]
      abel

private lemma siteShiftN_apply_ne (d N : ℕ) (x : FinLatticeSites d N)
    {μ i : Fin d} (h : i ≠ μ) (k : ℕ) :
    siteShiftN d N x μ k i = x i := by
  induction k with
  | zero =>
      simp [siteShiftN]
  | succ k ih =>
      simp [siteShiftN, siteShift, h, ih]

private lemma link_reachable_siteShiftN (d N : ℕ) [NeZero N]
    (hd : 2 ≤ d) (hN : 2 < N) (s : FinLatticeSites d N) (μ j : Fin d) :
    ∀ k : ℕ, (ambientLinkGraph d N).Reachable ⟨s, μ⟩ ⟨siteShiftN d N s j k, μ⟩
  | 0 => by simp [siteShiftN]
  | k + 1 => by
      have ih := link_reachable_siteShiftN d N hd hN s μ j k
      have hstep := link_reachable_siteShift_once d N hd hN (siteShiftN d N s j k) μ j
      exact ih.trans hstep

private def siteMoveToCoord (d N : ℕ) (target x : FinLatticeSites d N)
    (i : Fin d) : FinLatticeSites d N :=
  siteShiftN d N x i ((target i - x i).val)

private lemma siteMoveToCoord_apply_self (d N : ℕ) [NeZero N]
    (target x : FinLatticeSites d N) (i : Fin d) :
    siteMoveToCoord d N target x i i = target i := by
  unfold siteMoveToCoord
  rw [siteShiftN_apply_self]
  rw [ZMod.natCast_zmod_val (target i - x i)]
  abel

private lemma siteMoveToCoord_apply_ne (d N : ℕ)
    (target x : FinLatticeSites d N) {i j : Fin d} (h : j ≠ i) :
    siteMoveToCoord d N target x i j = x j := by
  unfold siteMoveToCoord
  exact siteShiftN_apply_ne d N x h _

private def siteMoveToCoords (d N : ℕ) (target : FinLatticeSites d N) :
    List (Fin d) → FinLatticeSites d N → FinLatticeSites d N
  | [], x => x
  | i :: is, x => siteMoveToCoords d N target is (siteMoveToCoord d N target x i)

private lemma siteMoveToCoords_apply_not_mem (d N : ℕ)
    (target : FinLatticeSites d N) :
    ∀ (is : List (Fin d)) (x : FinLatticeSites d N) (j : Fin d),
      j ∉ is → siteMoveToCoords d N target is x j = x j
  | [], _, _, _ => by simp [siteMoveToCoords]
  | i :: is, x, j, hj => by
      simp only [List.mem_cons, not_or] at hj
      rw [siteMoveToCoords, siteMoveToCoords_apply_not_mem d N target is
        (siteMoveToCoord d N target x i) j hj.2]
      exact siteMoveToCoord_apply_ne d N target x hj.1

private lemma siteMoveToCoords_apply_mem (d N : ℕ) [NeZero N]
    (target : FinLatticeSites d N) :
    ∀ (is : List (Fin d)), is.Nodup → ∀ (x : FinLatticeSites d N) (j : Fin d),
      j ∈ is → siteMoveToCoords d N target is x j = target j
  | [], _, _, _, hj => by simp at hj
  | i :: is, hnodup, x, j, hj => by
      simp only [List.nodup_cons] at hnodup
      rcases List.mem_cons.mp hj with hji | hj'
      · subst j
        rw [siteMoveToCoords, siteMoveToCoords_apply_not_mem d N target is
          (siteMoveToCoord d N target x i) i hnodup.1, siteMoveToCoord_apply_self]
      · exact siteMoveToCoords_apply_mem d N target is hnodup.2
          (siteMoveToCoord d N target x i) j hj'

private lemma siteMoveToCoords_eq_target (d N : ℕ) [NeZero N]
    (target x : FinLatticeSites d N) :
    siteMoveToCoords d N target (Finset.univ.toList : List (Fin d)) x = target := by
  ext j
  exact siteMoveToCoords_apply_mem d N target (Finset.univ.toList : List (Fin d))
    (Finset.nodup_toList _) x j (by simp)

private lemma link_reachable_siteMoveToCoords (d N : ℕ) [NeZero N]
    (hd : 2 ≤ d) (hN : 2 < N) (target : FinLatticeSites d N) (μ : Fin d) :
    ∀ (is : List (Fin d)) (x : FinLatticeSites d N),
      (ambientLinkGraph d N).Reachable ⟨x, μ⟩ ⟨siteMoveToCoords d N target is x, μ⟩
  | [], x => by simp [siteMoveToCoords]
  | i :: is, x => by
      have hfirst := link_reachable_siteShiftN d N hd hN x μ i ((target i - x i).val)
      have hrest := link_reachable_siteMoveToCoords d N hd hN target μ is
        (siteMoveToCoord d N target x i)
      exact hfirst.trans hrest

/-- The ambient shared-plaquette graph is connected for `d ≥ 2` and torus side length `N ≥ 3`.

The proof follows the primitive-move construction from
`docs/mass-gap-completion-plan.md`: a shared-plaquette edge changes link direction at a
fixed anchor, shifts a link transversely, and realizes a parallel shift by a three-step
walk through a transverse direction. Iterating these moves connects arbitrary anchors. -/
theorem ambientLinkGraph_connected (d N : ℕ) [NeZero N] (_hd : 2 ≤ d) (_hN : 2 < N) :
    (ambientLinkGraph d N).Connected := by
  classical
  haveI : Nonempty (LatticeLink d N) := ⟨⟨fun _ => 0, ⟨0, by omega⟩⟩⟩
  refine ⟨?_⟩
  intro x y
  have hsite := link_reachable_siteMoveToCoords d N _hd _hN y.site x.dir
    (Finset.univ.toList : List (Fin d)) x.site
  have hsite_eq : siteMoveToCoords d N y.site (Finset.univ.toList : List (Fin d)) x.site =
      y.site :=
    siteMoveToCoords_eq_target d N y.site x.site
  have hto_site : (ambientLinkGraph d N).Reachable x ⟨y.site, x.dir⟩ := by
    simpa [hsite_eq] using hsite
  by_cases hdir : x.dir = y.dir
  · have hy : ({ site := y.site, dir := x.dir } : LatticeLink d N) = y := by
      cases y
      simp at hdir ⊢
      exact hdir
    simpa [hy] using hto_site
  · have hchange : (ambientLinkGraph d N).Reachable ⟨y.site, x.dir⟩ y :=
      ambientLinkGraph_reachable_of_linkAmbientAdj d N
        (linkAmbientAdj_dir_change d N y.site hdir)
    exact hto_site.trans hchange

lemma linkGraphDist_triangle (d N : ℕ) [NeZero N]
    (hd : 2 ≤ d) (hN : 2 < N) (x y z : LatticeLink d N) :
    linkGraphDist d N x y ≤ linkGraphDist d N x z + linkGraphDist d N z y :=
  linkGraphDist_triangle_of_connected d N (ambientLinkGraph_connected d N hd hN) x y z

lemma linkGraphDist_siteDist_bound (d N : ℕ) [NeZero N]
    (hd : 2 ≤ d) (hN : 2 < N) (x y : LatticeLink d N) :
    latticeSiteDist d N x.site y.site ≤ 2 * linkGraphDist d N x y :=
  linkGraphDist_siteDist_bound_of_connected d N (ambientLinkGraph_connected d N hd hN) x y

lemma boundaryLink_reverse_triangle (d N : ℕ) [NeZero N]
    [DecidableEq (LatticeLink d N)]
    {p q : LatticePlaquette d N} {x y : LatticeLink d N}
    (hx : x ∈ p.boundaryLinkFinset) (hy : y ∈ q.boundaryLinkFinset) :
    latticePlaquetteDist d N p q ≤ latticeSiteDist d N x.site y.site + 2 := by
  have hpx : latticeSiteDist d N p.site x.site ≤ 1 := by
    rw [latticeSiteDist_comm d N p.site x.site]
    exact boundaryLinkFinset_siteDist_le_one d N p hx
  have hyq : latticeSiteDist d N y.site q.site ≤ 1 :=
    boundaryLinkFinset_siteDist_le_one d N q hy
  have htri1 := latticeSiteDist_triangle d N p.site x.site q.site
  have htri2 := latticeSiteDist_triangle d N x.site y.site q.site
  simp only [latticePlaquetteDist] at *
  omega

lemma linkGraphDist_boundary_ge_of_connected (d N : ℕ) [NeZero N]
    [DecidableEq (LatticeLink d N)]
    (hconn : (ambientLinkGraph d N).Connected)
    {p q : LatticePlaquette d N} {x y : LatticeLink d N}
    (hx : x ∈ p.boundaryLinkFinset) (hy : y ∈ q.boundaryLinkFinset) :
    latticePlaquetteDist d N p q ≤ 2 * linkGraphDist d N x y + 2 := by
  have hrev := boundaryLink_reverse_triangle d N hx hy
  have hsite := linkGraphDist_siteDist_bound_of_connected d N hconn x y
  omega

lemma linkGraphDist_boundary_lower_bound_of_connected (d N : ℕ) [NeZero N]
    [DecidableEq (LatticeLink d N)]
    (hconn : (ambientLinkGraph d N).Connected)
    {p q : LatticePlaquette d N} {x y : LatticeLink d N}
    (hx : x ∈ p.boundaryLinkFinset) (hy : y ∈ q.boundaryLinkFinset) :
    (latticePlaquetteDist d N p q - 1) / 2 ≤ linkGraphDist d N x y := by
  have h := linkGraphDist_boundary_ge_of_connected d N hconn hx hy
  omega

lemma linkGraphDist_boundary_ge (d N : ℕ) [NeZero N]
    [DecidableEq (LatticeLink d N)]
    (hd : 2 ≤ d) (hN : 2 < N)
    {p q : LatticePlaquette d N} {x y : LatticeLink d N}
    (hx : x ∈ p.boundaryLinkFinset) (hy : y ∈ q.boundaryLinkFinset) :
    latticePlaquetteDist d N p q ≤ 2 * linkGraphDist d N x y + 2 :=
  linkGraphDist_boundary_ge_of_connected d N (ambientLinkGraph_connected d N hd hN) hx hy

lemma linkGraphDist_boundary_lower_bound (d N : ℕ) [NeZero N]
    [DecidableEq (LatticeLink d N)]
    (hd : 2 ≤ d) (hN : 2 < N)
    {p q : LatticePlaquette d N} {x y : LatticeLink d N}
    (hx : x ∈ p.boundaryLinkFinset) (hy : y ∈ q.boundaryLinkFinset) :
    (latticePlaquetteDist d N p q - 1) / 2 ≤ linkGraphDist d N x y :=
  linkGraphDist_boundary_lower_bound_of_connected d N
    (ambientLinkGraph_connected d N hd hN) hx hy

end
