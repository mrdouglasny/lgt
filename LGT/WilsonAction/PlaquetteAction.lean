/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Wilson Plaquette Action

S(U) = β · Σ_p Re Tr(I - U_p), summed over plaquettes.

## References

- Chatterjee (2026), §15.2
- Wilson, Phys. Rev. D 10 (1974)
-/

import LGT.GaugeField.Connection
import LGT.GaugeField.GaugeGroup

open GaussianField

noncomputable section

/-! ## The Wilson action on the 2D asymmetric lattice -/

variable (G : Type*) (n : ℕ) [Group G] [HasGaugeTrace G n]
variable {Nt Ns : ℕ} [NeZero Nt] [NeZero Ns]

/-- The Wilson action on the asymmetric 2D lattice:
S(U) = β · Σ_p (n - Re Tr(U_p)). -/
def asymWilsonAction (β : ℝ) (U : AsymGaugeConnection G Nt Ns) : ℝ :=
  β * ∑ p : AsymPlaquette Nt Ns,
    wilsonPlaquetteCost G n (asymPlaquetteHolonomy U p)

/-- The Boltzmann weight exp(-S(U)). Always positive. -/
def asymWilsonBoltzmann (β : ℝ) (U : AsymGaugeConnection G Nt Ns) : ℝ :=
  Real.exp (-(asymWilsonAction G n β U))

theorem asymWilsonBoltzmann_pos (β : ℝ) (U : AsymGaugeConnection G Nt Ns) :
    0 < asymWilsonBoltzmann G n β U :=
  Real.exp_pos _

/-! ## Spatial gauge fixing -/

/-- A 2D connection is spatially gauge-fixed: all spatial links = 1. -/
def isSpatiallyGaugeFixed {G : Type*} [Group G] {Nt Ns : ℕ}
    (U : AsymGaugeConnection G Nt Ns) : Prop :=
  ∀ (t : ZMod Nt) (s : ZMod Ns), U ⟨(t, s), Dir2D.space⟩ = 1

/-- In the gauge-fixed theory, the plaquette holonomy simplifies to
U_t(s+1) · U_t(s)⁻¹ — only temporal links contribute. -/
theorem asymPlaquetteHolonomy_gaugeFixed
    (U : AsymGaugeConnection G Nt Ns) (hgf : isSpatiallyGaugeFixed U)
    (p : AsymPlaquette Nt Ns) :
    asymPlaquetteHolonomy U p =
    U ⟨p.site, Dir2D.time⟩ *
    (U ⟨(p.site.1, p.site.2 + 1), Dir2D.time⟩)⁻¹ := by
  simp only [asymPlaquetteHolonomy, AsymPlaquette.boundaryLinks]
  have h1 := hgf (p.site.1 + 1) p.site.2
  have h2 := hgf p.site.1 p.site.2
  simp [h1, h2]

end
