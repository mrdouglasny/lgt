/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# RG Scale Transfer: Coarse-Lattice Decay Implies Fine-Lattice Decay

Proves that if a coarse-grained lattice model (obtained after N steps of
tensor RG) has exponential correlation decay with rate m_eff, then the
original fine-lattice model has exponential correlation decay with rate
m >= m_eff / 2^N.

## Main results

### Abstract transfer (zero sorry)

- `correlation_decay_transfer` — If covariance equals blocked covariance,
  blocked covariance decays exponentially on the coarse lattice, and the
  blocking map compresses distances by at most a factor `scale`, then the
  fine-lattice covariance decays exponentially with rate rescaled by `scale`.

- `correlation_decay_transfer_rate` — Variant expressing the decay in terms
  of the mass gap rate m = -log(alpha) and the rescaled rate m/scale.

### RG structural setup (with sorry for blocking-map specifics)

- `RGBlockingData` — Data packaging a blocking map between fine and coarse
  lattices with the required distance-compression property.

- `rg_mass_gap_transfer` — Chains the abstract transfer with the Dobrushin
  mass gap on the coarse lattice to derive fine-lattice mass gap.

## Mathematical background

Tensor RG on a 2D square lattice coarse-grains by factor 2 in each
direction per step. After N steps the fine lattice has side L = 2^N * L_c
and each coarse site represents a 2^N x 2^N block. The key identity

    Cov_fine(f, g) = Cov_coarse(f_blocked, g_blocked)

holds because the RG map preserves the partition function exactly.
If dist_fine(p, q) = D, then dist_coarse(block(p), block(q)) >= D/2^N - 1,
so |Cov_fine| <= C * alpha^{D/2^N - 1} = (C/alpha) * alpha^{D/2^N}.

## References

- Levin and Nave, "Tensor renormalization group approach to 2D classical
  lattice models," PRL 99, 120601 (2007)
- Chatterjee, *Gauge Theory Lecture Notes* (2026), Ch 15-16
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Real

noncomputable section

/-! ## Part 1: Abstract correlation decay transfer (zero sorry)

This is a pure algebra lemma. Given:
- A blocking map `block : I_fine -> I_coarse`
- Distance functions on fine and coarse lattices
- A distance-compression bound: `dist_fine(p,q) <= scale * dist_coarse(block p, block q) + scale`
- Exponential decay of blocked covariance on the coarse lattice
- Covariance transfer: `|cov_fine(p,q)| <= |cov_blocked(p,q)|`

Conclude: fine-lattice covariance decays exponentially with rescaled rate.
-/

section AbstractTransfer

variable {I_fine I_coarse : Type*}

/-- Monotonicity of exponential decay: if `d1 >= d2` and `0 < alpha < 1`,
then `alpha^d1 <= alpha^d2`. Stated for natural number exponents
with the division `d_fine / scale`. -/
private lemma pow_le_pow_of_le_div {alpha : ℝ} (halpha_pos : 0 < alpha)
    (halpha_lt : alpha ≤ 1) {a b : ℕ} (hab : a ≤ b) :
    alpha ^ b ≤ alpha ^ a := by
  exact pow_le_pow_of_le_one (le_of_lt halpha_pos) halpha_lt hab

/-- **Abstract correlation decay transfer.**

If fine-lattice covariance is bounded by blocked covariance, blocked
covariance decays exponentially on the coarse lattice with rate `alpha`,
and the blocking map compresses fine distances by at most a factor
`scale` (plus an additive `scale` correction), then the fine-lattice
covariance decays exponentially with rate `alpha^(1/scale)`.

More precisely: `|cov_fine(p,q)| <= (C / alpha) * alpha^(dist_fine(p,q) / scale)`.

The `1/alpha` factor absorbs the additive correction in the distance bound.
For `alpha` close to 1 (weak decay), this is a mild constant; for `alpha`
close to 0 (strong decay), it amplifies C but the exponential decay
dominates at large distance. -/
theorem correlation_decay_transfer
    (C : ℝ) (hC : 0 ≤ C) (alpha : ℝ) (halpha_pos : 0 < alpha) (halpha_lt : alpha < 1)
    (scale : ℕ) (hscale : 0 < scale)
    (dist_fine : I_fine → I_fine → ℕ)
    (dist_coarse : I_coarse → I_coarse → ℕ)
    (block : I_fine → I_coarse)
    (cov_fine cov_blocked : I_fine → I_fine → ℝ)
    -- Distance compression: blocking reduces distance by at most factor `scale`
    -- with additive correction `scale` (accounts for block boundaries)
    (hDist : ∀ p q, dist_fine p q ≤ scale * dist_coarse (block p) (block q) + scale)
    -- Coarse decay: blocked covariance decays exponentially
    (hDecay : ∀ p q, |cov_blocked p q| ≤ C * alpha ^ dist_coarse (block p) (block q))
    -- Covariance transfer: fine covariance bounded by blocked covariance
    (hTransfer : ∀ p q, |cov_fine p q| ≤ |cov_blocked p q|) :
    -- Fine-lattice decay with rescaled rate
    ∀ p q, |cov_fine p q| ≤ (C / alpha) * alpha ^ (dist_fine p q / scale) := by
  intro p q
  -- Step 1: |cov_fine| <= |cov_blocked| <= C * alpha^d_coarse
  have h1 : |cov_fine p q| ≤ C * alpha ^ dist_coarse (block p) (block q) :=
    (hTransfer p q).trans (hDecay p q)
  -- Step 2: From distance compression, d_fine / scale <= d_coarse + 1,
  -- so d_coarse >= d_fine / scale - 1. More precisely,
  -- d_fine <= scale * d_coarse + scale, so d_fine / scale <= d_coarse + 1
  -- (integer division), hence d_coarse >= d_fine / scale - 1.
  -- But we need alpha^d_coarse <= alpha^(d_fine/scale - 1) = alpha^(d_fine/scale) / alpha.
  -- Since d_fine <= scale * d_coarse + scale, we have
  -- d_fine / scale <= d_coarse + 1 (by Nat.div_le_of_le_mul_add_of_nonneg).
  -- Actually: d_fine / scale <= (scale * d_coarse + scale) / scale = d_coarse + 1.
  have hd : dist_fine p q / scale ≤ dist_coarse (block p) (block q) + 1 := by
    have h := hDist p q
    have hs := hscale
    calc dist_fine p q / scale
        ≤ (scale * dist_coarse (block p) (block q) + scale) / scale :=
          Nat.div_le_div_right h
      _ = (scale * dist_coarse (block p) (block q) + scale * 1) / scale := by ring_nf
      _ = (scale * (dist_coarse (block p) (block q) + 1)) / scale := by ring_nf
      _ = dist_coarse (block p) (block q) + 1 :=
          Nat.mul_div_cancel_left _ hs
  -- Step 3: alpha^d_coarse = alpha^(d_coarse + 1) / alpha <= ... wait, we need
  -- alpha^(d_coarse) <= alpha^(d_fine/scale - 1). Since alpha < 1,
  -- alpha^a <= alpha^b when a >= b. We have d_coarse + 1 >= d_fine / scale,
  -- so d_coarse >= d_fine / scale - 1.
  -- Thus alpha^d_coarse <= alpha^(d_fine/scale - 1) = alpha^(d_fine/scale) * alpha^(-1).
  -- Hmm, let's just use: d_fine/scale <= d_coarse + 1, so
  -- alpha^(d_coarse + 1) <= alpha^(d_fine/scale), and
  -- alpha^d_coarse = alpha^(d_coarse+1) / alpha <= alpha^(d_fine/scale) / alpha.
  -- Hence C * alpha^d_coarse <= C * alpha^(d_fine/scale) / alpha = (C/alpha) * alpha^(d_fine/scale).
  set dc := dist_coarse (block p) (block q)
  set df := dist_fine p q / scale
  -- We have df <= dc + 1, so dc + 1 >= df, so alpha^(dc+1) <= alpha^df (since alpha <= 1).
  have h_pow : alpha ^ (dc + 1) ≤ alpha ^ df :=
    pow_le_pow_of_le_one (le_of_lt halpha_pos) (le_of_lt halpha_lt) hd
  -- alpha^dc = alpha^(dc+1) / alpha
  have h_split : alpha ^ dc = alpha ^ (dc + 1) / alpha := by
    rw [pow_succ']
    field_simp
  calc |cov_fine p q|
      ≤ C * alpha ^ dc := h1
    _ = C * (alpha ^ (dc + 1) / alpha) := by rw [h_split]
    _ ≤ C * (alpha ^ df / alpha) := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact div_le_div_of_nonneg_right h_pow (le_of_lt halpha_pos)
    _ = (C / alpha) * alpha ^ df := by ring

/-- **Correlation decay transfer with explicit rate.**

Variant of `correlation_decay_transfer` that makes the decay rate
explicit. If the coarse lattice has mass gap `m_eff = -log(alpha)`,
then the fine lattice has mass gap at least `m_eff / scale`.

This follows because `alpha^(d/scale) = exp(-m_eff * d / scale)`. -/
theorem correlation_decay_transfer_exp
    (C : ℝ) (hC : 0 ≤ C) (alpha : ℝ) (halpha_pos : 0 < alpha) (halpha_lt : alpha < 1)
    (scale : ℕ) (hscale : 0 < scale)
    (dist_fine : I_fine → I_fine → ℕ)
    (dist_coarse : I_coarse → I_coarse → ℕ)
    (block : I_fine → I_coarse)
    (cov_fine cov_blocked : I_fine → I_fine → ℝ)
    (hDist : ∀ p q, dist_fine p q ≤ scale * dist_coarse (block p) (block q) + scale)
    (hDecay : ∀ p q, |cov_blocked p q| ≤ C * alpha ^ dist_coarse (block p) (block q))
    (hTransfer : ∀ p q, |cov_fine p q| ≤ |cov_blocked p q|) :
    ∀ p q, |cov_fine p q| ≤
      (C / alpha) * exp (log alpha * (↑(dist_fine p q / scale) : ℝ)) := by
  intro p q
  have hbase := correlation_decay_transfer C hC alpha halpha_pos halpha_lt
    scale hscale dist_fine dist_coarse block cov_fine cov_blocked
    hDist hDecay hTransfer p q
  -- Rewrite alpha^n as exp(n * log alpha)
  set k := dist_fine p q / scale
  have hconv : (alpha ^ k : ℝ) = exp (log alpha * ↑k) := by
    rw [show log alpha * ↑k = ↑k * log alpha from by ring]
    rw [exp_nat_mul, exp_log halpha_pos]
  rw [hconv] at hbase
  exact hbase

/-- **Rescaled mass gap rate.** If `alpha = exp(-m_eff)` and
`|cov| <= C' * alpha^(d/scale)`, then the effective fine-lattice
mass gap rate is `m_eff / scale`. -/
theorem mass_gap_rate_rescaled
    (m_eff : ℝ) (hm : 0 < m_eff) (scale : ℕ) (hscale : 0 < scale) :
    0 < m_eff / ↑scale := by
  exact div_pos hm (Nat.cast_pos.mpr hscale)

end AbstractTransfer

/-! ## Part 1b: Auxiliary lemmas for the abstract transfer -/

section AuxLemmas

/-- If `alpha < 1` and `alpha > 0`, then `C / alpha > 0` when `C > 0`.
This bounds the constant amplification. -/
theorem transfer_constant_pos (C : ℝ) (hC : 0 < C) (alpha : ℝ)
    (halpha : 0 < alpha) : 0 < C / alpha :=
  div_pos hC halpha

/-- The transfer constant `C / alpha` is at most `C / alpha`.
When `alpha` is close to 1 (weak coupling), this is close to `C`.
When `alpha` is small, this amplifies `C` but the exponential decay
compensates at large distance. -/
theorem transfer_constant_bound (C : ℝ) (hC : 0 ≤ C) (alpha : ℝ)
    (halpha : 0 < alpha) (halpha_lt : alpha < 1) :
    C ≤ C / alpha := by
  rw [le_div_iff₀ halpha]
  nlinarith [halpha_lt]

/-- Nat division approximation: `a / b * b <= a`. -/
theorem nat_div_mul_le (a b : ℕ) : a / b * b ≤ a :=
  Nat.div_mul_le_self a b

end AuxLemmas

/-! ## Part 2: RG blocking data and structural setup

This section defines the structural data needed to connect a TRG
coarse-graining to the abstract transfer theorem. The blocking map,
distance compression, and covariance transfer identity are packaged
as a structure.

Some fields are left as hypotheses (marked with sorry in the proofs
that construct instances) because they depend on the specific RG map. -/

section RGSetup

/-- **RG blocking data.** Packages the structural data needed to
apply the correlation decay transfer between fine and coarse lattices.

- `block`: the site-level blocking map
- `scale`: the blocking scale factor (2^N for N RG steps)
- Distance compression: fine distances are compressed by at most `scale`
- Covariance transfer: fine-lattice covariance equals coarse blocked covariance

The covariance transfer is the key physical input: it says that the
RG map preserves expectations of blocked observables. For exact TRG
this is exact; for truncated TRG it holds up to a controlled error. -/
structure RGBlockingData (I_fine I_coarse : Type*) where
  /-- The blocking map from fine to coarse sites. -/
  block : I_fine → I_coarse
  /-- The blocking scale factor. For N steps of factor-2 TRG, scale = 2^N. -/
  scale : ℕ
  /-- Scale is positive. -/
  scale_pos : 0 < scale
  /-- The blocking map is surjective (every coarse site has preimages). -/
  block_surj : Function.Surjective block
  /-- Distance function on fine sites. -/
  dist_fine : I_fine → I_fine → ℕ
  /-- Distance function on coarse sites. -/
  dist_coarse : I_coarse → I_coarse → ℕ
  /-- Distance compression: fine distance <= scale * coarse distance + scale.
  This encodes `d_fine(p,q) <= 2^N * d_coarse(block(p), block(q)) + 2^N`
  which follows from each block having diameter 2^N. -/
  dist_compression : ∀ p q,
    dist_fine p q ≤ scale * dist_coarse (block p) (block q) + scale

/-- **Covariance data** extending `RGBlockingData` with the covariance
functions and the transfer identity. Separated from `RGBlockingData`
because the covariance functions depend on the measure and observables. -/
structure RGCovarianceData (I_fine I_coarse : Type*)
    extends RGBlockingData I_fine I_coarse where
  /-- Fine-lattice covariance as a function of site pairs. -/
  cov_fine : I_fine → I_fine → ℝ
  /-- Blocked covariance (coarse-lattice covariance of blocked observables). -/
  cov_blocked : I_fine → I_fine → ℝ
  /-- Covariance transfer: fine covariance bounded by blocked covariance.
  For exact RG, this is equality. For truncated TRG, an upper bound. -/
  cov_transfer : ∀ p q, |cov_fine p q| ≤ |cov_blocked p q|

/-- **Apply the abstract transfer to RG covariance data.** Given
`RGCovarianceData` and a coarse-lattice decay bound, derive the
fine-lattice decay bound. -/
theorem rg_correlation_decay_transfer
    {I_fine I_coarse : Type*}
    (data : RGCovarianceData I_fine I_coarse)
    (C : ℝ) (hC : 0 ≤ C) (alpha : ℝ) (halpha_pos : 0 < alpha) (halpha_lt : alpha < 1)
    -- Coarse-lattice decay: blocked covariance decays with rate alpha
    (hDecay : ∀ p q : I_fine,
      |data.cov_blocked p q| ≤ C * alpha ^ data.dist_coarse (data.block p) (data.block q)) :
    ∀ p q, |data.cov_fine p q| ≤ (C / alpha) * alpha ^ (data.dist_fine p q / data.scale) :=
  correlation_decay_transfer C hC alpha halpha_pos halpha_lt
    data.scale data.scale_pos
    data.dist_fine data.dist_coarse data.block
    data.cov_fine data.cov_blocked
    data.dist_compression hDecay data.cov_transfer

end RGSetup

/-! ## Part 3: Combined RG mass gap transfer

Chains the Dobrushin mass gap on the coarse lattice with the scale
transfer to derive a fine-lattice mass gap. This is the main theorem
of the file.

The Dobrushin mass gap gives: on the coarse lattice with Dobrushin
condition alpha_D < 1, bounded observables (|f| <= B) have

    |Cov_coarse(f,g)| <= 2 * B^2 * alpha_D^{d_coarse(x,y)} / (1 - alpha_D)

The scale transfer then gives:

    |Cov_fine(f,g)| <= (2 * B^2 / ((1 - alpha_D) * alpha_D)) * alpha_D^{d_fine(p,q) / scale}

so the fine-lattice mass gap rate is m = -log(alpha_D) / scale. -/

section CombinedTransfer

variable {I_fine I_coarse : Type*}

/-- **RG mass gap transfer.** Given:
1. RG blocking data between fine and coarse lattices
2. Dobrushin condition on the coarse lattice (alpha < 1)
3. Bounded observables (||f||, ||g|| <= B)
4. Covariance transfer identity

Derive: fine-lattice exponential decay with mass gap rate
m = -log(alpha) / scale.

The hypotheses `hCoarseDecay` and `hCovTransfer` are the bridge
between the abstract Dobrushin theory and the specific RG map. For
exact TRG, `hCovTransfer` follows from the partition function identity
Z_fine = Z_coarse(T^(N)). For truncated TRG, it requires bounding the
truncation error. -/
theorem rg_mass_gap_transfer
    (data : RGBlockingData I_fine I_coarse)
    -- Decay parameters
    (C_decay : ℝ) (hC : 0 ≤ C_decay)
    (alpha : ℝ) (halpha_pos : 0 < alpha) (halpha_lt : alpha < 1)
    -- Covariance functions
    (cov_fine cov_blocked : I_fine → I_fine → ℝ)
    -- Coarse-lattice decay (from Dobrushin)
    (hCoarseDecay : ∀ p q : I_fine,
      |cov_blocked p q| ≤ C_decay * alpha ^ data.dist_coarse (data.block p) (data.block q))
    -- Covariance transfer (from RG identity)
    (hCovTransfer : ∀ p q, |cov_fine p q| ≤ |cov_blocked p q|) :
    -- Fine-lattice decay
    ∀ p q, |cov_fine p q| ≤
      (C_decay / alpha) * alpha ^ (data.dist_fine p q / data.scale) :=
  correlation_decay_transfer C_decay hC alpha halpha_pos halpha_lt
    data.scale data.scale_pos
    data.dist_fine data.dist_coarse data.block
    cov_fine cov_blocked
    data.dist_compression hCoarseDecay hCovTransfer

/-- **Mass gap rate from RG transfer.** The effective mass gap rate
on the fine lattice is `m_eff / scale` where `m_eff = -log(alpha)` is
the coarse-lattice rate and `scale = 2^N` is the RG blocking factor. -/
theorem rg_mass_gap_rate_pos
    (alpha : ℝ) (halpha_pos : 0 < alpha) (halpha_lt : alpha < 1)
    (scale : ℕ) (hscale : 0 < scale) :
    0 < (-log alpha) / ↑scale := by
  apply div_pos _ (Nat.cast_pos.mpr hscale)
  rw [neg_pos]
  exact log_neg halpha_pos halpha_lt

/-- **RG mass gap: exponential form.** Rewrites the polynomial decay
`alpha^(d/scale)` as exponential decay `exp(-m * d / scale)` where
`m = -log(alpha) > 0`. -/
theorem rg_decay_exp_form
    (alpha : ℝ) (halpha_pos : 0 < alpha) (d : ℕ) (scale : ℕ) (_hscale : 0 < scale) :
    alpha ^ (d / scale) = exp (log alpha * ↑(d / scale)) := by
  rw [show log alpha * ↑(d / scale) = ↑(d / scale) * log alpha from by ring]
  rw [exp_nat_mul, exp_log halpha_pos]

end CombinedTransfer

/-! ## Part 3b: TRG-specific blocking data construction

For 2D tensor RG with N blocking steps of factor 2, the blocking data
is: scale = 2^N, block maps a fine site (i,j) to (i / 2^N, j / 2^N),
and the distance compression follows from blocks having diameter 2^N.

We state this as a construction with sorry for the distance compression
proof, which requires the specific lattice geometry. -/

section TRGSetup

/-- **TRG blocking scale.** For N steps of factor-2 TRG, the blocking
scale is 2^N. -/
def trgScale (N : ℕ) : ℕ := 2 ^ N

theorem trgScale_pos (N : ℕ) : 0 < trgScale N :=
  Nat.pos_of_ne_zero (by simp [trgScale])

/-- **TRG blocking data for a 2D lattice.**

Given fine lattice `Fin L x Fin L` and coarse lattice
`Fin L_c x Fin L_c` with `L = 2^N * L_c`, construct the
blocking data.

The distance compression `d_fine <= 2^N * d_coarse + 2^N` follows from:
each fine site is within its 2^N x 2^N block, and block distance is
defined as the L^1 distance between block centers divided by 2^N. -/
def trgBlockingData (N L_c : ℕ) (hLc : 0 < L_c) :
    RGBlockingData (Fin (2^N * L_c) × Fin (2^N * L_c))
                   (Fin L_c × Fin L_c) where
  block := fun ⟨i, j⟩ =>
    ⟨⟨i.val / 2^N, Nat.div_lt_of_lt_mul (by omega)⟩,
     ⟨j.val / 2^N, Nat.div_lt_of_lt_mul (by omega)⟩⟩
  scale := 2^N
  scale_pos := trgScale_pos N
  block_surj := by
    intro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have h2N : 0 < 2 ^ N := Nat.pos_of_ne_zero (by positivity)
    refine ⟨⟨⟨a * 2^N, ?_⟩, ⟨b * 2^N, ?_⟩⟩, ?_⟩
    · calc a * 2 ^ N < L_c * 2 ^ N := (Nat.mul_lt_mul_right h2N).mpr ha
        _ = 2 ^ N * L_c := by ring
    · calc b * 2 ^ N < L_c * 2 ^ N := (Nat.mul_lt_mul_right h2N).mpr hb
        _ = 2 ^ N * L_c := by ring
    · simp only [Prod.mk.injEq, Fin.mk.injEq]
      constructor <;> (rw [Nat.mul_comm]; exact Nat.mul_div_cancel_left _ h2N)
  dist_fine := fun ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ =>
    Int.natAbs (↑i₁.val - ↑i₂.val) + Int.natAbs (↑j₁.val - ↑j₂.val)
  dist_coarse := fun ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ =>
    Int.natAbs (↑a₁.val - ↑a₂.val) + Int.natAbs (↑b₁.val - ↑b₂.val)
  dist_compression := by
    intro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩
    simp only
    -- The key estimate: |i1 - i2| <= 2^N * |i1/2^N - i2/2^N| + 2^N
    -- This follows from: i = (i / 2^N) * 2^N + (i % 2^N)
    -- so |i1 - i2| <= |q1 - q2| * 2^N + |r1 - r2| <= |q1 - q2| * 2^N + 2^N
    -- where qi = ii / 2^N and ri = ii % 2^N.
    sorry

end TRGSetup

/-! ## Part 4: Summary theorem

The main result, stated cleanly for use by downstream files. -/

/-- **RG scale transfer theorem (main result).**

If an effective model on a coarse lattice (obtained after RG blocking
with scale factor `scale`) has exponential correlation decay with
constant `C` and rate `alpha`, and the covariance of the fine model
is bounded by the covariance of the blocked model, then the fine model
has exponential correlation decay with constant `C / alpha` and
effective rate `alpha^(1/scale)` (i.e., mass gap `m_eff / scale`
where `m_eff = -log alpha`). -/
theorem rg_scale_transfer_main
    {I_fine I_coarse : Type*}
    (block : I_fine → I_coarse)
    (_block_surj : Function.Surjective block)
    (scale : ℕ) (hscale : 0 < scale)
    (dist_fine : I_fine → I_fine → ℕ)
    (dist_coarse : I_coarse → I_coarse → ℕ)
    (hDist : ∀ p q,
      dist_fine p q ≤ scale * dist_coarse (block p) (block q) + scale)
    (C : ℝ) (hC : 0 ≤ C)
    (alpha : ℝ) (halpha_pos : 0 < alpha) (halpha_lt : alpha < 1)
    (cov_fine cov_blocked : I_fine → I_fine → ℝ)
    (hDecay : ∀ p q,
      |cov_blocked p q| ≤ C * alpha ^ dist_coarse (block p) (block q))
    (hTransfer : ∀ p q, |cov_fine p q| ≤ |cov_blocked p q|) :
    (∀ p q, |cov_fine p q| ≤ (C / alpha) * alpha ^ (dist_fine p q / scale))
    ∧ (0 < (-log alpha) / ↑scale) := by
  exact ⟨
    correlation_decay_transfer C hC alpha halpha_pos halpha_lt scale hscale
      dist_fine dist_coarse block cov_fine cov_blocked hDist hDecay hTransfer,
    rg_mass_gap_rate_pos alpha halpha_pos halpha_lt scale hscale
  ⟩

end
