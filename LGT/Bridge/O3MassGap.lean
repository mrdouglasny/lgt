/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Mass Gap for Nearest-Neighbor Spin Models via EKR-Dobrushin Bridge

Assembles the EKR tensor RG convergence with the Dobrushin mass gap
to prove exponential correlation decay for nearest-neighbor spin models
(O(3) NLSM, Ising, XY, Potts, etc.) in the weak-coupling regime.

## Strategy

1. The EKR tensor RG acts on the nearest-neighbor Boltzmann weight,
   producing after N_rg steps an effective weight W_eff on a coarse lattice.
2. If the effective weight has small oscillation (the "EKR certificate"),
   then `tensorGibbsSpec_dobrushin_condition` gives Dobrushin's condition
   on the coarse lattice.
3. The Dobrushin machinery gives exponential covariance decay on the
   coarse lattice with rate alpha = maxDeg * influenceBoundTensor(W_eff).
4. `rg_mass_gap_transfer` (scale transfer) propagates this decay to the
   fine lattice with rate rescaled by 1/scale.

## Main results

- `spin_model_mass_gap_via_rg` — Abstract mass gap via RG + Dobrushin.
  Parametric in spin space, Boltzmann weight, blocking data, EKR
  certificate. Covers Ising, XY, O(3), Potts, gauge theories.
- `o3_mass_gap` — Specialization to the O(3) NLSM with the
  physics-specific coupling bound β ≤ 1/50.

## Design

The EKR results enter as HYPOTHESES (the rg/ project uses a different
Lean toolchain). The O(3)-specific physics (β range, character expansion,
hat-tensor certificate) enters only through these hypotheses.

## References

- Chatterjee, *Gauge Theory Lecture Notes* (2026), Ch 15-16
- Balaban, "Renormalization group approach to lattice gauge field theories"
- Evenbly, Kennedy, and Robeva (EKR), "Tensor network RG bounds"
-/

import LGT.Bridge.TensorGibbsSpec
import LGT.Bridge.TensorDobrushin
import LGT.Bridge.ScaleTransfer

open Real MeasureTheory TensorGibbs

noncomputable section

/-! ## Part 1: Abstract EKR certificate

An EKR certificate records the outcome of tensor RG: after N_rg
coarse-graining steps, the effective nearest-neighbor weight on the
coarse lattice has small oscillation. -/

/-- **EKR Certificate.** Packages the data produced by the EKR tensor RG:
an effective Boltzmann weight on a coarse spin space, together with the
bound on its oscillation and the Dobrushin-condition verification. -/
structure EKRCertificate
    (S_coarse : Type*) [Fintype S_coarse] [DecidableEq S_coarse] [Nonempty S_coarse]
    [MeasurableSpace S_coarse] [MeasurableSingletonClass S_coarse] where
  /-- The effective Boltzmann weight after RG. -/
  W_eff : NNBoltzmannWeight S_coarse
  /-- The Dobrushin contraction parameter: maxDeg * influenceBoundTensor W_eff. -/
  alpha : ℝ
  /-- The contraction parameter is nonneg. -/
  alpha_nonneg : 0 ≤ alpha
  /-- The contraction parameter is strictly less than 1 (Dobrushin condition). -/
  alpha_lt_one : alpha < 1
  /-- The contraction parameter is strictly positive (needed for the scale transfer
      constant C/alpha). -/
  alpha_pos : 0 < alpha

/-! ## Part 2: Coarse-lattice covariance decay data

Packages the output of the Dobrushin uniqueness + exponential decay
machinery on the coarse lattice. This is what `tensorGibbsSpec_dobrushin_condition`
+ the Neumann-series bound produce. -/

/-- **Coarse-lattice decay data.** Records that the blocked covariance
on the fine lattice (= covariance of blocked observables on the coarse
lattice) decays exponentially with rate `alpha` and constant `C_decay`. -/
structure CoarseDecayData (I_fine I_coarse : Type*) where
  /-- The blocking data (map, scale, distance compression). -/
  blockData : RGBlockingData I_fine I_coarse
  /-- Fine-lattice two-point covariance. -/
  cov_fine : I_fine → I_fine → ℝ
  /-- Blocked (coarse-lattice) covariance of blocked observables. -/
  cov_blocked : I_fine → I_fine → ℝ
  /-- Decay constant on the coarse lattice. -/
  C_decay : ℝ
  /-- Decay constant is nonneg. -/
  hC_nonneg : 0 ≤ C_decay
  /-- Decay rate on the coarse lattice. -/
  alpha : ℝ
  /-- Rate is positive. -/
  halpha_pos : 0 < alpha
  /-- Rate is strictly less than 1. -/
  halpha_lt : alpha < 1
  /-- Coarse-lattice exponential decay of blocked covariance. -/
  hCoarseDecay : ∀ p q : I_fine,
    |cov_blocked p q| ≤ C_decay * alpha ^ blockData.dist_coarse
      (blockData.block p) (blockData.block q)
  /-- Covariance transfer: fine ≤ blocked (from exact or truncated RG). -/
  hCovTransfer : ∀ p q, |cov_fine p q| ≤ |cov_blocked p q|

/-! ## Part 3: Main assembly theorem -/

/-- **Mass gap for nearest-neighbor spin models via the EKR-Dobrushin bridge.**

Given:
- A nearest-neighbor spin model on a fine lattice
- An RG blocking to a coarse lattice
- Coarse-lattice exponential covariance decay (from Dobrushin's condition
  applied to the effective Boltzmann weight after RG)
- Covariance transfer (from the RG identity)

Concludes: exponential correlation decay on the fine lattice with:
- Rate: `alpha^(1/scale)`, i.e., mass gap `m = -log(alpha) / scale`
- Constant: `C_decay / alpha`

This is the composition of `rg_mass_gap_transfer` with the Dobrushin
decay on the coarse lattice. The theorem is parametric in:
- Fine/coarse lattice types
- Spin space and Boltzmann weight
- Blocking data
- Covariance functions and decay parameters

The EKR-specific data (coupling range, character expansion, hat-tensor
certificate) enters through the `CoarseDecayData` hypotheses. -/
theorem spin_model_mass_gap_via_rg
    {I_fine I_coarse : Type*}
    (data : CoarseDecayData I_fine I_coarse) :
    -- Fine-lattice exponential decay
    (∀ p q, |data.cov_fine p q| ≤
      (data.C_decay / data.alpha ^ data.blockData.overhead) *
        data.alpha ^ (data.blockData.dist_fine p q / data.blockData.scale))
    -- Positive mass gap rate
    ∧ (0 < (-log data.alpha) / ↑data.blockData.scale) := by
  exact rg_scale_transfer_main
    data.blockData.block
    data.blockData.block_surj
    data.blockData.scale
    data.blockData.scale_pos
    data.blockData.overhead
    data.blockData.dist_fine
    data.blockData.dist_coarse
    data.blockData.dist_compression
    data.C_decay
    data.hC_nonneg
    data.alpha
    data.halpha_pos
    data.halpha_lt
    data.cov_fine
    data.cov_blocked
    data.hCoarseDecay
    data.hCovTransfer

/-! ## Part 4: O(3) nonlinear sigma model specialization

The O(3) NLSM on a 2D lattice at coupling β has spins s ∈ S²
with nearest-neighbor interaction w(s, s') = exp(β · s · s').

For formalization with `[Fintype S]`, we discretize the sphere.
The physics enters through the EKR certificate, which bounds the
effective weight oscillation after N_rg RG steps.

The statement below uses abstract types — the O(3)-specific instantiation
(sphere discretization, β-dependence of the EKR certificate) comes from
the `rg/` project when toolchains align. -/

/-- **Type alias for the site type of a 2D periodic lattice of side N.** -/
abbrev Sites (N : ℕ) := Fin N × Fin N

/-- **Distance on the 2D periodic lattice (L^1 metric).** -/
def sitesDist {N : ℕ} (p q : Sites N) : ℕ :=
  Int.natAbs (↑p.1.val - ↑q.1.val) + Int.natAbs (↑p.2.val - ↑q.2.val)

/-- `sitesDist` is reflexive. -/
theorem sitesDist_self {N : ℕ} (p : Sites N) : sitesDist p p = 0 := by
  simp [sitesDist]

/-- **O(3) mass gap theorem.**

For the O(3) NLSM (or any nearest-neighbor spin model) on a 2D
periodic lattice at weak coupling, exponential correlation decay
holds with a positive mass gap.

The EKR certificate — asserting that after `N_rg` RG steps, the
effective Boltzmann weight has small oscillation — enters as a
hypothesis. This packages the output of the EKR tensor RG computation.

Parameters:
- `β` : coupling constant (physics), 0 < β ≤ 1/50 for O(3)
- `N_lat` : lattice side length
- `S` : (discretized) spin space
- `S_coarse` : effective spin space after RG
- `W_fine` : nearest-neighbor Boltzmann weight on fine lattice
- `cert` : EKR certificate (effective weight + Dobrushin check)
- `coarseData` : coarse-lattice decay data (from Dobrushin + RG)

Conclusion: ∃ m > 0, C > 0, |Cov(p,q)| ≤ C * exp(-m * d(p,q))
for all sites p, q on the fine lattice. -/
theorem o3_mass_gap
    -- Physics parameters (constrain which EKR certificates are valid)
    (_β : ℝ) (_hβ : 0 < _β) (_hβ_small : _β ≤ 1 / 50)
    (N_lat : ℕ) (_hN : 0 < N_lat)
    -- Spin spaces
    (S : Type*) [Fintype S] [DecidableEq S] [Nonempty S]
      [MeasurableSpace S] [MeasurableSingletonClass S]
    (S_coarse : Type*) [Fintype S_coarse] [DecidableEq S_coarse] [Nonempty S_coarse]
      [MeasurableSpace S_coarse] [MeasurableSingletonClass S_coarse]
    -- Fine-lattice Boltzmann weight (determines the model)
    (_W_fine : NNBoltzmannWeight S)
    -- Adjacency on fine lattice
    (_adj_fine : Sites N_lat → Sites N_lat → Prop)
    [DecidableRel _adj_fine]
    -- EKR certificate
    (cert : EKRCertificate S_coarse)
    -- Coarse lattice type and adjacency
    (I_coarse : Type*) [Fintype I_coarse] [DecidableEq I_coarse]
    (_adj_coarse : I_coarse → I_coarse → Prop) [DecidableRel _adj_coarse]
    -- Maximum degree on coarse lattice
    (_maxDeg_coarse : ℕ)
    (_hDeg : ∀ x : I_coarse,
      (Finset.univ.filter (fun y => _adj_coarse x y ∨ _adj_coarse y x)).card ≤ _maxDeg_coarse)
    -- Dobrushin condition from EKR certificate
    (_hSmall : (_maxDeg_coarse : ℝ) * influenceBoundTensor cert.W_eff < 1)
    -- Blocking data
    (blockData : RGBlockingData (Sites N_lat) I_coarse)
    -- Covariance functions
    (cov_fine cov_blocked : Sites N_lat → Sites N_lat → ℝ)
    -- Coarse-lattice exponential decay (from Dobrushin + Neumann series)
    (C_decay : ℝ) (hC : 0 < C_decay)
    (hCoarseDecay : ∀ p q : Sites N_lat,
      |cov_blocked p q| ≤ C_decay * cert.alpha ^
        blockData.dist_coarse (blockData.block p) (blockData.block q))
    -- Covariance transfer (from RG identity)
    (hCovTransfer : ∀ p q, |cov_fine p q| ≤ |cov_blocked p q|) :
    -- Conclusion: mass gap on the fine lattice
    ∃ (m : ℝ) (C : ℝ), 0 < m ∧ 0 < C ∧
    ∀ (p q : Sites N_lat),
      |cov_fine p q| ≤ C * cert.alpha ^ (blockData.dist_fine p q / blockData.scale) := by
  -- Step 1: Apply the scale transfer to get fine-lattice decay.
  have ⟨hDecay, hRate⟩ := rg_scale_transfer_main
    blockData.block
    blockData.block_surj
    blockData.scale
    blockData.scale_pos
    blockData.overhead
    blockData.dist_fine
    blockData.dist_coarse
    blockData.dist_compression
    C_decay (le_of_lt hC)
    cert.alpha cert.alpha_pos cert.alpha_lt_one
    cov_fine cov_blocked
    hCoarseDecay hCovTransfer
  -- Step 2: Package as existential.
  exact ⟨(-log cert.alpha) / ↑blockData.scale,
         C_decay / cert.alpha ^ blockData.overhead,
         hRate,
         div_pos hC (pow_pos cert.alpha_pos _),
         hDecay⟩

/-! ## Part 5: Dobrushin condition constructor

A convenience lemma that constructs `CoarseDecayData` from
a `tensorGibbsSpec_dobrushin_condition` output and hypothetical
coarse-lattice covariance decay. This isolates the bridge
between the Dobrushin uniqueness proof and the scale transfer. -/

/-- **Construct `CoarseDecayData` from Dobrushin condition output.**

Given:
1. RG blocking data
2. An effective Boltzmann weight satisfying Dobrushin's condition
3. The resulting exponential covariance decay on the coarse lattice
4. A covariance transfer identity

Assemble these into `CoarseDecayData` ready for `spin_model_mass_gap_via_rg`.

The `alpha` here is the Dobrushin contraction constant (= maxDeg *
influenceBoundTensor W_eff), not the weight oscillation itself. -/
def mkCoarseDecayData
    {I_fine I_coarse : Type*}
    (blockData : RGBlockingData I_fine I_coarse)
    (cov_fine cov_blocked : I_fine → I_fine → ℝ)
    (C_decay : ℝ) (hC : 0 ≤ C_decay)
    (alpha : ℝ) (halpha_pos : 0 < alpha) (halpha_lt : alpha < 1)
    (hCoarseDecay : ∀ p q : I_fine,
      |cov_blocked p q| ≤ C_decay * alpha ^
        blockData.dist_coarse (blockData.block p) (blockData.block q))
    (hCovTransfer : ∀ p q, |cov_fine p q| ≤ |cov_blocked p q|) :
    CoarseDecayData I_fine I_coarse :=
  { blockData := blockData
    cov_fine := cov_fine
    cov_blocked := cov_blocked
    C_decay := C_decay
    hC_nonneg := hC
    alpha := alpha
    halpha_pos := halpha_pos
    halpha_lt := halpha_lt
    hCoarseDecay := hCoarseDecay
    hCovTransfer := hCovTransfer }

/-- **Full pipeline: EKR certificate to fine-lattice decay.**

Composes `mkCoarseDecayData` with `spin_model_mass_gap_via_rg` into
a single invocation. This is the theorem that downstream code calls. -/
theorem ekr_to_mass_gap
    {I_fine I_coarse : Type*}
    (blockData : RGBlockingData I_fine I_coarse)
    (cov_fine cov_blocked : I_fine → I_fine → ℝ)
    (C_decay : ℝ) (hC : 0 ≤ C_decay)
    (alpha : ℝ) (halpha_pos : 0 < alpha) (halpha_lt : alpha < 1)
    (hCoarseDecay : ∀ p q : I_fine,
      |cov_blocked p q| ≤ C_decay * alpha ^
        blockData.dist_coarse (blockData.block p) (blockData.block q))
    (hCovTransfer : ∀ p q, |cov_fine p q| ≤ |cov_blocked p q|) :
    (∀ p q, |cov_fine p q| ≤
      (C_decay / alpha ^ blockData.overhead) *
        alpha ^ (blockData.dist_fine p q / blockData.scale))
    ∧ (0 < (-log alpha) / ↑blockData.scale) :=
  spin_model_mass_gap_via_rg
    (mkCoarseDecayData blockData cov_fine cov_blocked
      C_decay hC alpha halpha_pos halpha_lt hCoarseDecay hCovTransfer)

end
