# Plan: completing the Yang–Mills mass gap in lgt

## Status

One remaining sorry in the repository, at
`LGT/MassGap/StrongCoupling.lean:2065`, inside
`ym_mass_gap_exponential_decay`. The already-proved `ym_mass_gap_UN`
bounds the connected 2-point function by a 16-term sum involving a
coarse link distance `ymLinkDist ∈ {0, 1, 2}`, which does not decay
with geometric separation. This plan replaces that coarse distance
with a genuine graph distance, closing the sorry.

## Inventory — what already exists

**Upstream (`markov-semigroups`)**:

- `neumannSeriesCoeff_nn_dist_bound` (`Dobrushin/NeumannSeries.lean:356`).
  For any `d : I → I → ℕ` with reflexivity, triangle inequality, and
  *nearest-neighbor support* (`d x y > 1 → influenceCoeff γ x y = 0`),
  proves `neumannSeriesCoeff γ x y ≤ α^{d(x,y)} / (1 − α)`.
- `iterateInfluence_dist_zero` (`NeumannSeries.lean:262`). Takes an
  explicit range `R ≥ 1`; we won't need this because we'll hit R=1.
- `covariance_bound_gibbs_multisite_general_nn_dist_nocount`
  (`Dobrushin/CovarianceBoundMultisite.lean:2499`). Given a Gibbs
  measure, bounded local observables `f, g`, locality finsets
  `N_f, N_g`, and the above distance hypotheses, proves
  `|Cov(f, g)| ≤ 2 · Bf · Bg · Σ_{x∈N_f, y∈N_g} α^{d(y,x)} / (1−α)`.
- `ym_mass_gap_2pt_via_multisite` in lgt
  (`MassGap/MassGap3D.lean:253`, already proved). **The genuine
  distance-parameterized wrapper.** Assembles the upstream covariance
  bound with YM Gibbs spec, plaquette observables, and `sharesPlaquette`
  influence bound; takes `(dLink : LatticeLink d N → LatticeLink d N →
  ℕ)` plus refl / triangle / support hypotheses as explicit parameters.
- `ym_mass_gap_strong_coupling` in lgt (`StrongCoupling.lean:1651`,
  already proved). A **hypothesis-discharging wrapper** over
  `ym_mass_gap_2pt_via_multisite`: takes `hRep_cont` and derives ~20
  measurability/integrability hypotheses from it. **Currently hardcodes
  `d := ymLinkDist d N plaq` in its conclusion** (line 1672) and
  derives `ymLinkDist_refl / _triangle / _support` internally at lines
  1823–1826. Not yet distance-parameterized. `ym_mass_gap_UN` (line
  1966) wraps it.
- `dobrushin_sufficient` (`DobrushinVerification.lean:154`). Proves
  `(0 ≤ β) ∧ (β < 1/(4 n · maxNeighbors d)) → dobrushinColumnSum n d β
  < 1`. Used downstream (`YMDobrushin.lean:367`) as the `hα_lt` input
  to `DobrushinCondition`.

**In lgt**:

- `LatticePlaquette`, `LatticeLink`, `boundaryLinks` (`Lattice/CellComplex.lean`).
- `sharesPlaquette d N plaq x y := ∃ p ∈ plaq, x, y ∈ ∂p` and its
  decidability (`Gibbs/YMDobrushin.lean:56`).
- `influenceCoeff γ x y = 0` when `¬ sharesPlaquette x y`, packaged
  as the `hInfluence` hypothesis threaded through every caller.
- A draft `ZMod.periodicDist`, `latticeSiteDist`, and
  `latticePlaquetteDist` in `StrongCoupling.lean:2015–2026` (defined
  but no metric lemmas proved; duplicated by `plaquetteDist` in
  `YMMeasure.lean:224`).

**What is missing**: a distance on `LatticeLink d N` that (i) has
nearest-neighbor support against `sharesPlaquette` (so upstream
applies unmodified) and (ii) grows with geometric separation on
`(ℤ/Nℤ)^d` (so the final bound is a true exponential decay in
plaquette distance, not a coarse constant).

## Target theorem

After the sorry is discharged, `LGT/MassGap/StrongCoupling.lean` will
contain

    theorem ym_mass_gap_exponential_decay
        (n : ℕ) (hn : 1 ≤ n)
        (d N : ℕ) (hd : 2 ≤ d) (hN : 2 < N) [NeZero N]
        [CompactSpace (unitaryGroup (Fin n) ℂ)]
        [SecondCountableTopology (unitaryGroup (Fin n) ℂ)]
        [HasHaarProbability (unitaryGroup (Fin n) ℂ)]
        [Fintype (LatticeLink d N)] [DecidableEq (LatticeLink d N)]
        (β : ℝ) (hβ : 0 ≤ β)
        (hβ_small : β < 1 / (4 * ↑n * ↑(maxNeighbors d)))
        (plaq : Finset (LatticePlaquette d N))
        (p q : LatticePlaquette d N) :
        |connected2pt (unitaryGroup (Fin n) ℂ) n d N β plaq
            (plaqObs (unitaryGroup (Fin n) ℂ) n d N p)
            (plaqObs (unitaryGroup (Fin n) ℂ) n d N q)| ≤
          32 * (↑n : ℝ) ^ 2 / (1 - dobrushinColumnSum n d β) *
            (dobrushinColumnSum n d β)
              ^ ((latticePlaquetteDist d N p q - 1) / 2) := by
      ...

The exponent is `Nat.sub` (saturates at 0) composed with `Nat.div`
(truncating), and is arithmetically equal to
`Nat.ceilDiv (latticePlaquetteDist d N p q - 2) 2` for all
`plaqDist ≥ 0` (case-check: plaqDist ∈ {0, 1, 2} give 0; plaqDist ≥
3 give `(plaqDist − 1) / 2 = (plaqDist − 2 + 1) / 2`, which is the
ceiling of `(plaqDist − 2) / 2`). The `(n − 1) / 2` form is the
concrete target; no ceiling operator appears in the Lean theorem
header.

The companion rate corollary (result L, Phase 6b):

    theorem ym_mass_gap_rate_exists
        (n : ℕ) (hn : 1 ≤ n)
        (d N : ℕ) (hd : 2 ≤ d) (hN : 2 < N) [NeZero N]
        [CompactSpace (unitaryGroup (Fin n) ℂ)]
        [SecondCountableTopology (unitaryGroup (Fin n) ℂ)]
        [HasHaarProbability (unitaryGroup (Fin n) ℂ)]
        [Fintype (LatticeLink d N)] [DecidableEq (LatticeLink d N)]
        (β : ℝ) (hβ_pos : 0 < β)
        (hβ_small : β < 1 / (4 * ↑n * ↑(maxNeighbors d))) :
        ∃ (m : ℝ), 0 < m ∧ ∀ (plaq : Finset (LatticePlaquette d N))
            (p q : LatticePlaquette d N),
          |connected2pt (unitaryGroup (Fin n) ℂ) n d N β plaq
              (plaqObs (unitaryGroup (Fin n) ℂ) n d N p)
              (plaqObs (unitaryGroup (Fin n) ℂ) n d N q)| ≤
            32 * (↑n : ℝ) ^ 2 /
              (dobrushinColumnSum n d β * (1 - dobrushinColumnSum n d β)) *
              Real.exp (-m * ↑(latticePlaquetteDist d N p q)) := by
      ...

with `m := (−Real.log (dobrushinColumnSum n d β)) / 2`. The
existential-`m` shape matches the physics mass-gap form.

with `α = dobrushinColumnSum n d β < 1`. The current sorry-backed
header claims `α^{latticePlaquetteDist p q}` — this is what the
Dobrushin machinery cannot deliver; the corrected exponent is
`(latticePlaquetteDist p q - 1) / 2` (`Nat` subtraction and
division throughout, so the expression saturates at 0 for
plaquettes at close range). The change is flagged as user-visible
in the PR.

For the mass-gap rate form (β > 0 only), with `m := (−log α) / 2 > 0`,
a companion theorem `ym_mass_gap_rate_exists` packages the
existential shape familiar from the physics literature:

    ∃ (m : ℝ), 0 < m ∧ ∀ plaq p q,
        |conn2pt ... plaq p q| ≤
          (32 n² / (α · (1 − α))) · Real.exp (−m · plaqDist(p, q)).

The rate `m = (−log α) / 2` in L¹ plaqDist is dimension-independent.
At `β = 0`, `α = 0` and the base bound gives 0 (correct: connected
correlators vanish when the measure factorizes), but the rate form
is vacuous since `−log α = +∞` and the constant `1/α` blows up; it
must be stated under `0 < β` separately.

## Why the rate is `log α / 2`, not `log α`

The influence graph on links has edge relation `sharesPlaquette`.
Two links `e₁, e₂` share a plaquette iff both lie on the boundary of
some common plaquette `p`. The boundary of a plaquette at anchor
`s` with directions `μ < ν` contains links anchored at
`{s, s+μ, s+ν}`, so the four boundary anchors span L¹ site-diameter
2 (achieved between `(s+μ, ν)` and `(s+ν, μ)`). Therefore one
influence-graph step displaces the link anchor by at most 2 L¹
site-units, and `k` steps by at most `2k`. The exponent of `α` in
the final bound counts graph steps, so in L¹ plaqDist the rate
picks up the factor of 1/2 from this conversion. This is tight:
the (s+μ, ν) vs (s+ν, μ) pair realizes both the 1-graph-step
adjacency and the 2-L¹-units site distance.

## The chain of intermediate results

**Important: adjacency is ambient, not `plaq`-dependent.** The
existing `sharesPlaquette d N plaq x y` in `Gibbs/YMDobrushin.lean`
carries an explicit finset `plaq : Finset (LatticePlaquette d N)` —
the plaquettes active in the Wilson action. A graph built from that
relation has connectivity depending on `plaq`, which is quantified
over arbitrarily in the target theorem. Using it would leave the
geometric lower bound on `linkGraphDist` unprovable when `plaq` is
sparse.

Instead, define an ambient adjacency and an ambient graph distance:

    linkAmbientAdj (x y : LatticeLink d N) : Prop :=
        x ≠ y ∧ ∃ p : LatticePlaquette d N,
          (∃ i, p.boundaryLinks i = x) ∧ (∃ j, p.boundaryLinks j = y)

    ambientLinkGraph (d N : ℕ) : SimpleGraph (LatticeLink d N) :=
        SimpleGraph.fromRel linkAmbientAdj

    linkGraphDist x y : ℕ := (ambientLinkGraph d N).dist x y

This adjacency is independent of `plaq` and symmetric.
Monotonicity: if `sharesPlaquette d N plaq x y` and `x ≠ y`, then
`linkAmbientAdj x y` (the plaquette witnessing the left-hand side
is a plaquette, so it also witnesses the right-hand side). The
contrapositive is what powers step H below.

On Mathlib's convention, `SimpleGraph.dist` returns 0 across
components. Step E below is only true within a connected
component, so we separately prove ambient connectedness of
`(ℤ/Nℤ)^d` for `d ≥ 2`, `N ≥ 3`. The single-step geometry is
asymmetric and a casual connectedness sketch overclaims:

A plaquette anchored at `s` with directions `μ < ν` contains four
boundary links:

    boundaryLinks 0 = (s,      μ)      -- μ-link at s
    boundaryLinks 1 = (s + μ, ν)       -- ν-link at s+μ
    boundaryLinks 2 = (s + ν, μ)       -- μ-link at s+ν
    boundaryLinks 3 = (s,      ν)      -- ν-link at s

So its two μ-links are at anchors `s` and `s+ν`, and its two
ν-links are at anchors `s` and `s+μ`. A single shared-plaquette
step can therefore:

- Change direction at a fixed anchor: `(s, μ) ~ (s, ν)` (via the
  μν-plaquette at `s`).
- Translate a link **transverse** to its own direction:
  `(s, μ) ~ (s + e_j, μ)` for `j ≠ μ` (via the μj-plaquette at
  `s`).

What a single step **cannot** do is translate a link parallel to
itself: no plaquette contains two μ-links at anchors differing by
`e_μ`. So `(s, μ) ↝ (s + e_μ, μ)` requires a multi-step walk, for
example

    (s, μ) ~ (s, ν) ~ (s + e_μ, ν) ~ (s + e_μ, μ)

for any `ν ≠ μ` — a 3-step walk using the μν-plaquette at `s` and
the μν-plaquette at `s + e_μ − e_ν` … (pick any ν ≠ μ, which
exists because `d ≥ 2`).

With these two primitive moves in hand, connectedness follows by
composition: (i) direction change at a fixed anchor reaches
`(s, ν)` from `(s, μ)`, (ii) transverse shifts reach any
`(s', μ)` from `(s, μ)` with `s'` differing from `s` only in
coordinates `j ≠ μ`, (iii) the 3-step parallel-shift construction
covers the remaining μ-coordinate. Iterating coordinate-by-
coordinate (`d` ≥ 2 ensures each coordinate has at least one
transverse direction available) joins any two links.

**A. ZMod periodic distance is a metric on ZMod N.**

    ZMod.periodicDist N a b := min (a − b).val (N − (a − b).val)

    periodicDist_self : periodicDist N a a = 0
    periodicDist_comm : periodicDist N a b = periodicDist N b a
    periodicDist_triangle :
        periodicDist N a c ≤ periodicDist N a b + periodicDist N b c

The triangle inequality is the main technical content of the chain.
Proof by case split on which branch of `min` is active in each of
`periodicDist N a b` and `periodicDist N b c`. A related `torusDist`
exists in `pphi2N/Pphi2N/Thimble/GreenDecay.lean:169` but without a
triangle proof.

**B. latticeSiteDist is a pseudometric on `(ℤ/Nℤ)^d`.**

    latticeSiteDist x y := Σ i : Fin d, ZMod.periodicDist N (x i) (y i)

    latticeSiteDist_self, _comm, _triangle

Immediate from A by summing component-wise.

**B.5. latticePlaquetteDist is a pseudometric on plaquettes.**

    latticePlaquetteDist p q := latticeSiteDist p.site q.site

    latticePlaquetteDist_self, _comm, _triangle

Named explicitly so F, G, J, K can cite it as a metric rather than
unfolding the `latticeSiteDist` on anchor sites each time. Metric
properties transfer from B by function-composition. The existing
draft `plaquetteDist` (YMMeasure.lean:224) and `latticePlaquetteDist`
(StrongCoupling.lean:2024) should be consolidated with this one —
they are the same function under different names.

**C. Boundary-layer lemma.**

    boundaryLink_siteDist_le_one :
        ∀ (p : LatticePlaquette d N) (k : Fin 4),
          latticeSiteDist ((p.boundaryLinks k).site) p.site ≤ 1

Case on `k ∈ {0, 1, 2, 3}`. `boundaryLinks 0` and `boundaryLinks 3`
have anchor `p.site` (distance 0); `boundaryLinks 1` and
`boundaryLinks 2` have anchor `siteShift p.site μ` for some `μ`
(distance 1 in the μ-coordinate, 0 in every other, total 1).

**D. One ambient graph step moves the link anchor by ≤ 2 L¹ site-units.**

    linkAmbientAdj_imp_siteDist_le_two :
        linkAmbientAdj x y →
          latticeSiteDist (x.site) (y.site) ≤ 2

From C applied to both `x` and `y` (both are boundary links of the
shared plaquette, so within L¹ site-distance 1 of its anchor) plus
triangle.

**E. k ambient graph steps move the link anchor by ≤ 2k L¹ site-units.**

    linkGraphDist_siteDist_bound :
        latticeSiteDist (x.site) (y.site) ≤ 2 * linkGraphDist x y

Induction on the length of a shortest walk from `x` to `y` in
`ambientLinkGraph`, using D at each step. Requires that `x, y` lie
in the same component (otherwise `SimpleGraph.dist = 0` by Mathlib
convention, and the bound fails). Ambient connectedness on
`(ℤ/Nℤ)^d` for `d ≥ 2`, `N ≥ 3` is proved as a separate lemma
(see Phase 4), so E holds unconditionally.

**F. Reverse boundary-layer.**

    boundaryLink_reverse_triangle :
        x ∈ boundaryLinks p → y ∈ boundaryLinks q →
          latticePlaquetteDist p q ≤ latticeSiteDist (x.site) (y.site) + 2

From C applied to both sides plus reverse triangle inequality for
the pseudometric.

**G. Combining E and F (Lean-ready Nat form).**

    linkGraphDist_boundary_ge :
        x ∈ boundaryLinks p → y ∈ boundaryLinks q →
          2 * linkGraphDist x y + 2 ≥ latticePlaquetteDist p q

Rearranged to an explicit Nat bound (division and subtraction are
both `Nat` operations, truncating/saturating at 0):

    linkGraphDist x y ≥ (latticePlaquetteDist p q - 1) / 2

Equivalent to `Nat.ceilDiv (latticePlaquetteDist p q − 2) 2` but
writable as a plain `Nat` expression (no `Nat.ceil` operator
needed). Case check:

    plaqDist = 0, 1, 2  →  (plaqDist − 1) / 2 = 0
    plaqDist = 3, 4     →  1
    plaqDist = 5, 6     →  2
    plaqDist = 2k + 1   →  k
    plaqDist = 2k + 2   →  k

Both of the last two match `⌈(plaqDist − 2)/2⌉`.

**H. R = 1 support for `linkGraphDist` against `γ_YM` (holds for any `plaq`).**

    linkGraphDist_support :
        linkGraphDist x y > 1 →
          influenceCoeff γ_YM x y = 0

`linkGraphDist x y > 1` rules out `x = y` (distance 0 in any
SimpleGraph) and `x — y is an edge` (distance 1), so
`¬ linkAmbientAdj x y`. Hence `¬ ∃ p : LatticePlaquette, x, y ∈ ∂p`,
and a fortiori `¬ ∃ p ∈ plaq, x, y ∈ ∂p`, i.e.
`¬ sharesPlaquette d N plaq x y`. The existing `hInfluence`
hypothesis (influence is bounded by 0 off the plaquette-sharing
relation in `plaq`) discharges the conclusion. Critically, this
works **for any `plaq`**, because the ambient adjacency dominates
the `plaq`-restricted one.

**I. Power monotonicity.**

    pow_alpha_ge_of_le :
        0 ≤ α → α ≤ 1 → a ≤ b → α^b ≤ α^a

Standard. Handles `α = 0` cleanly: `0^0 = 1, 0^k = 0` for `k ≥ 1`.

Sourcing the hypotheses: `0 ≤ α` is immediate from nonnegativity of
`dobrushinColumnSum = maxNeighbors(d) · influenceBound(n, β)` (each
factor nonneg when `β ≥ 0`). The strict bound `α < 1` is
`dobrushin_sufficient` at
`LGT/MassGap/DobrushinVerification.lean:154`, which already proves
`(0 ≤ β) ∧ (β < 1/(4 n · maxNeighbors d)) → dobrushinColumnSum n d
β < 1` and is used downstream (`YMDobrushin.lean:367` threads it as
`hα_lt`). No new lemma needed.

**J. Boundary sum bound (Lean-ready Nat form).**

    boundary_sum_bound :
        Σ_{x ∈ ∂p} Σ_{y ∈ ∂q} α^{linkGraphDist y x} / (1 − α)
          ≤ 16 * α^((latticePlaquetteDist p q - 1) / 2) / (1 − α)

Sum over 16 pairs; each pair's exponent has a lower bound
`(plaqDist − 1) / 2` from G; apply I (power monotonicity)
pointwise; aggregate the 16 terms.

**K. Final composition.**

Blocked by a prerequisite refactor: `ym_mass_gap_strong_coupling`
currently hardcodes `ymLinkDist d N plaq` in its conclusion and
derives its refl / triangle / support hypotheses internally from
`ymLinkDist_*`. To instantiate with `linkGraphDist`, we first
**parameterize that wrapper by an arbitrary distance** (see Phase
5.5 below). Then plug `d := linkGraphDist` in with metric
hypotheses supplied by Mathlib's `SimpleGraph.dist_self` /
`SimpleGraph.dist_comm` / `SimpleGraph.dist_triangle` on
`ambientLinkGraph d N`, and R=1 support from H. The `plaq`
quantifier in the target theorem passes through because H does
not depend on which plaquettes are active in the Wilson action.
Output:

    |conn2pt(p, q)| ≤ 2 n² · Σ_{x, y} α^{linkGraphDist y x} / (1 − α).

Apply J:

    |conn2pt(p, q)| ≤
        32 n² / (1 − α) · α^((latticePlaquetteDist p q - 1) / 2).

Done.

**L. Mass-gap rate corollary (β > 0).**

The concrete bound K is the algebraic theorem. Physicists and
formalists alike expect a mass-gap statement of the form

    ∃ (m : ℝ), 0 < m ∧ ∀ plaq p q,
        |conn2pt ... plaq p q| ≤ C * Real.exp (-m * plaqDist p q)

for some `C > 0` depending on `(n, β, d)`. We package this as a
corollary with the additional hypothesis `0 < β` (needed for
`α > 0`, i.e., `−log α < +∞`). Derivation:

- Set `m := (−log α) / 2`. Then `α = exp(−2m)` and `m > 0` because
  `0 < α < 1`.
- From K, for all `plaqDist ≥ 0`:
  `α^((plaqDist − 1) / 2) = exp(−2m · ⌊(plaqDist − 1)/2⌋_ℕ)`.
  Since `2 · ⌊(plaqDist − 1)/2⌋_ℕ ≥ plaqDist − 2` (checkable case by
  case on parity), we have
  `α^((plaqDist − 1) / 2) ≤ exp(−m · (plaqDist − 2)) =
  exp(2m) · exp(−m · plaqDist) = α^(−1) · exp(−m · plaqDist)`.
- Combining: `|conn2pt| ≤ (32 n² / (α · (1 − α))) · exp(−m · plaqDist)`.

So the corollary holds with `C := 32 n² / (α · (1 − α))` and
`m := (−log α) / 2`. Both are finite and positive for
`0 < β < 1/(4 n · maxNeighbors d)`.

This matches the shape of the existing proxy theorem
`MassGap3D.lean:81` (renamed in Phase 7 to `ym_pow_le_exp_*`) but
is the genuine statement — the conclusion now involves
`|connected2pt|`, not just `α^k ≤ exp(−mk)`.

## What this plan avoids (and why)

The previous revision of this plan committed to option (A): prove an
R-generalized Neumann bound locally in lgt at `R = 2` with L¹
linkDist, then re-route through the multisite covariance bound (which
upstream proves with R=1 hard-coded, so the re-routing is either an
upstream refactor or a local inlining of a non-trivial theorem).
That path works mathematically but requires ~30–40 lines of local
Neumann argument plus either an upstream PR or a 100–300-line local
adaptation of the covariance bound.

Using `linkGraphDist` sidesteps both:

- **R = 1 is native** (by definition of graph distance), so upstream
  `neumannSeriesCoeff_nn_dist_bound` applies as-is.
- **The covariance bound is called unmodified**, since its
  `h_support` hypothesis is exactly what H proves.
- **The rate is the same** — `log α / 2` in L¹ plaqDist — because
  the geometry that forced the factor of 2 in option (A) shows up
  here as the step E bound `siteDist ≤ 2 · linkGraphDist`.

A rejected alternative was option (C): use L∞ site distance. `R=1`
support is native, but the final rate degrades to `log α / d` in
L¹ plaqDist (because `plaqDistL1 ≤ d · plaqDistInf`), which is
strictly worse than `log α / 2` for `d ≥ 3`.

## Phases

**Phase 1.** ZMod periodic distance metric (result A). One file,
~50–100 lines. Main content: `periodicDist_triangle`. Proof
strategy: case-split on which branch of `min` is active in each of
`periodicDist N a b` and `periodicDist N b c`, and on modular
wrapping of `(a − c).val`. Most case branches discharge by `omega`
once the `ZMod.val` and `min` conditions are made explicit.

**Phase 2.** Lattice site and plaquette pseudometrics (results B
and B.5). ~40 lines; component-wise sum from Phase 1 and a thin
wrapper on anchor sites. Consolidates the duplicate
`plaquetteDist` (`YMMeasure.lean:224`) and `latticePlaquetteDist`
(`StrongCoupling.lean:2024`).

**Phase 3.** Boundary-layer incidence (result C). ~30 lines; case
split on `boundaryLinks k`.

**Phase 4.** Ambient link graph, connectedness, and distance
properties (results D, E, H). ~150–200 lines — connectedness is
the dominant sub-phase, and Mathlib's `SimpleGraph.Walk` over
periodic ZMod coordinates is notoriously verbose (each primitive
move emits a `Walk.cons` term, the periodic coordinate wrapping
forces explicit `(a + 1 : ZMod N)` arithmetic, and the induction
combining primitive moves into `ambient_connected` type-checks
slowly). Budget more time here than any other phase.

- Define `linkAmbientAdj` (plaq-independent) and
  `ambientLinkGraph := SimpleGraph.fromRel linkAmbientAdj`.
- Two primitive reachability lemmas:
  - `link_dir_change_adj`: `(s, μ) ~ (s, ν)` for `μ ≠ ν` (via the
    μν-plaquette at `s`, rotated so `dir1 < dir2`).
  - `link_transverse_shift_adj`: `(s, μ) ~ (s + e_j, μ)` for
    `j ≠ μ` (via the μj-plaquette at `s`, rotated as above).
- Derived reachability:
  - `link_parallel_shift_reach`: `(s, μ) ↝ (s + e_μ, μ)` by
    direction-change + transverse-shift + direction-change (three
    ambient edges; uses `d ≥ 2` to pick `ν ≠ μ`).
- `ambient_connected`: induction on the componentwise site
  displacement plus direction change, combining the three
  reachability lemmas above.
- Define `linkGraphDist := (ambientLinkGraph d N).dist`.
- D (one-step site bound; from Phase 3).
- E (k-step site bound by induction on a shortest `Walk`).
- H (R=1 support — via monotonicity: `sharesPlaquette d N plaq x y
  ⟹ linkAmbientAdj x y`, so `¬linkAmbientAdj ⟹ ¬sharesPlaquette`
  ⟹ influence = 0 by the existing `hInfluence`).

**Phase 5.** Boundary sum reduction (results F, G, I, J). ~50 lines.
Reverse triangle on boundary; power monotonicity; sum aggregation.

**Phase 5.5 — Distance-parameterize `ym_mass_gap_strong_coupling`.**
~20–30 lines edit at `StrongCoupling.lean:1651–1906`, plus a
~15-line specialization. The current wrapper hardcodes
`ymLinkDist d N plaq` (line 1672) and derives refl / triangle /
support at lines 1823–1826. Refactor as follows:

- Add parameters `(dLink : LatticeLink d N → LatticeLink d N → ℕ)`,
  `(h_refl : ∀ x, dLink x x = 0)`,
  `(h_triangle : ∀ x y z, dLink x y ≤ dLink x z + dLink z y)`,
  and a `h_support`-style hypothesis (matching the `h_support`
  shape already required by `ym_mass_gap_2pt_via_multisite`).
- Replace the conclusion's `ymLinkDist d N plaq y x` with
  `dLink y x`.
- Remove the three internal `ymLinkDist_*` derivations at
  1823–1826; the arguments now come in as hypotheses.
- At line 1902, pass `dLink` and the new hypotheses through to
  `ym_mass_gap_2pt_via_multisite` instead of the `ymLinkDist`
  ones. Everything else in the proof is unchanged.

Then keep the old API surface of `ym_mass_gap_UN` by adding a
~15-line specialization that invokes the new wrapper with
`dLink := ymLinkDist d N plaq` and the three existing
`ymLinkDist_*` lemmas, yielding the original conclusion. No
downstream caller break.

This refactor is the only substantive change to existing code;
Phases 1–5 only add new files/lemmas.

**Phase 6.** Compose into `ym_mass_gap_exponential_decay` (result K).
~30 lines. Instantiate the newly distance-parameterized
`ym_mass_gap_strong_coupling` at `d := linkGraphDist` with refl /
triangle / support coming from Mathlib and from result H. Apply
J; adjust theorem header to the new exponent.

**Phase 6b.** Add the mass-gap rate corollary
`ym_mass_gap_rate_exists` (result L). ~20–30 lines. Additional
hypothesis `0 < β`; conclude
`∃ m > 0, |conn2pt| ≤ C · Real.exp (−m · plaqDist)`.
Key lemma to prove along the way:
`2 * ((k − 1 : ℕ) / 2) ≥ k − 2` (in ℤ, or as a ℕ inequality after
splitting cases on `k ∈ {0, 1, 2}` vs `k ≥ 3`). Everything else is
`Real.log` / `Real.exp` algebra. Can run immediately after Phase 6.

**Phase 7.** Rename `MassGap3D.lean` proxies (`ym_mass_gap`,
`ym_mass_gap_uniform` only prove `α^k ≤ exp(−mk)`, disconnected
from `connected2pt`). Independent of Phases 1–6; can run in
parallel.

**Phase 8.** Documentation updates (README, proof outline,
blueprint). After Phase 6 lands.

**Phase 9.** Verification: `lake build` green; `#print axioms
ym_mass_gap_exponential_decay` shows only standard axioms;
grep shows no `sorry` in `LGT/`.

```
Phase 1 ─► Phase 2 ─► Phase 3 ─► Phase 4 ─► Phase 5 ─► Phase 5.5 ─► Phase 6 ─► Phase 6b ─► Phase 8 ─► Phase 9
                                                                                        ▲
                                                                            Phase 7 ────┘
```

Phase 5.5 (wrapper refactor) can actually run in parallel with
Phases 1–5, since it only touches `ym_mass_gap_strong_coupling`'s
signature and doesn't depend on any of the new lemmas. It just
needs to be done before Phase 6.

## Budget

Per user calibration (sister-project work, upstream infrastructure
already in place): **5–8 active days, 1–2 weeks wall-clock**. The
two dominant uncertainties are Phase 1 (ZMod triangle inequality
— omega-heavy but mechanical) and Phase 4 (`SimpleGraph.Walk`
verbosity over periodic coordinates — the largest single phase by
LoC). All other phases are routine once the metric and the ambient
graph exist.

Residual-sorry budget: 1–2, most plausibly in Phase 1 if ZMod
periodic distance needs Mathlib backfill, or Phase 4 if the
connectedness proof surfaces an unexpected edge case in
`SimpleGraph.fromRel` over disconnected-when-`d = 1` behavior.

## Risks and open questions

1. **ZMod periodic distance triangle inequality.** Single biggest
   technical risk. The proof is a case split on which branch of
   `min` is active on each summand; Mathlib does not have this as
   a metric instance yet (worth a follow-up PR).

2. **Connectedness of the ambient link graph on `(ℤ/Nℤ)^d`,
   `d ≥ 2`, `N ≥ 3`.** Needed for result E to be unconditional.
   A single shared-plaquette step can (i) change direction at a
   fixed anchor or (ii) translate a link transverse to its own
   direction, but cannot translate parallel to its direction —
   parallel translation needs a 3-step walk (dir change +
   transverse shift + dir change back), exploiting `d ≥ 2` to
   pick a transverse direction. Composing these primitives yields
   any-to-any reachability by induction on coordinate-wise site
   displacement. See Phase 4 for the formalization plan.

3. **Theorem statement change is user-visible.** The current header
   at `StrongCoupling.lean:2048–2065` claims
   `α^{latticePlaquetteDist p q}`; the proof delivers
   `α^((latticePlaquetteDist p q - 1) / 2)` (`Nat` subtraction and
   division). Must be flagged in the PR description. The weaker
   form is what the Dobrushin machinery actually produces; the
   stronger form was overclaimed.

4. **β = 0 case.** The algebraic bound K stays valid at `α = 0`
   (gives trivial 0 bound; connected correlators vanish when the
   measure factorizes). The existential rate corollary L
   (`ym_mass_gap_rate_exists`) requires `0 < β` since `α = 0` makes
   both the rate `m = −log α / 2` and the constant `1/α` infinite.
   Stated as a separate lemma with an extra `hβ_pos` hypothesis.

5. **`SimpleGraph.dist` convention across components.** Mathlib
   returns 0 for disconnected pairs. Harmless for the `h_support`
   direction (if `dist > 1` then definitely not adjacent), but the
   `siteDist ≤ 2 · dist` bound (E) would be false across
   components — addressed by proving ambient connectedness in
   Phase 4.

6. **Plaquette-quantifier scope.** The target theorem quantifies
   over arbitrary `plaq : Finset (LatticePlaquette d N)`. An
   earlier draft of this plan defined `linkGraphDist` from the
   `plaq`-dependent `sharesPlaquette`, which made the graph
   connectivity (and hence step E) contingent on `plaq` being
   dense enough — breaking the proof for sparse `plaq`. The
   current plan uses ambient adjacency (plaq-independent) and
   recovers `plaq`-independent R=1 support via monotonicity of
   the ambient-vs-`plaq` adjacency relation. Codex review
   flagged this; fixed in the current revision.

7. **`ym_mass_gap_strong_coupling` is not yet
   distance-parameterized.** At the current API surface
   (`StrongCoupling.lean:1651`), the theorem hardcodes
   `ymLinkDist d N plaq` in its conclusion (line 1672) and derives
   refl / triangle / support internally. The generic-distance
   wrapper is `ym_mass_gap_2pt_via_multisite` at
   `MassGap3D.lean:253`, one level down. Phase 5.5 refactors
   `ym_mass_gap_strong_coupling` to take `dLink` as a parameter
   and thread it through, leaving `ym_mass_gap_UN` as a
   specialization. Codex review flagged this; fixed in the
   current revision.

## Review prompt for downstream agents

This document describes the chain of intermediate results to close
the one remaining sorry in lgt's mass-gap proof. A reviewer should
check:

1. Is every step A–K genuinely provable from the cited Mathlib /
   markov-semigroups lemmas plus the already-proved lgt facts?
2. Does the composition K actually yield the stated target theorem?
3. Is the `log α / 2` rate forced by the geometry, or is there a
   way to recover `log α` (the original, overclaimed rate) without
   strengthening the Dobrushin input?
4. Any step where the plan overclaims the ease of a proof?
5. Anything missing from the chain — a hidden lemma that isn't
   listed but would be needed?

Please be specific about which lemma, step, or phase you're
flagging. "This step is wrong" is actionable; "the plan looks
sketchy" is not.
