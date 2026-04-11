/-
Copyright (c) 2026 Michael R. Douglas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lattice Gauge Connections

A lattice gauge field assigns a group element G to each oriented link.
This is the discrete analogue of a connection 1-form on a principal
G-bundle: U(link) represents parallel transport along the link.

Provides both symmetric torus and asymmetric torus (2D) versions.

## Main definitions

- `GaugeConnection G d N` — G-valued 1-form on (ℤ/Nℤ)ᵈ
- `AsymGaugeConnection G Nt Ns` — G-valued 1-form on asymmetric lattice
- `plaquetteHolonomy` — ordered product around a plaquette
- `asymPlaquetteHolonomy` — 2D version for the mass gap proof

## References

- Chatterjee (2026), §15.2
- Wilson, Phys. Rev. D 10 (1974)
-/

import LGT.Lattice.CellComplex

/-! ## Gauge connections -/

/-- A gauge connection on the symmetric torus: G-valued function on links. -/
def GaugeConnection (G : Type*) (d : ℕ) (N : ℕ) := LatticeLink d N → G

/-- A gauge connection on the asymmetric 2D lattice. -/
def AsymGaugeConnection (G : Type*) (Nt Ns : ℕ) := AsymLink Nt Ns → G

variable {G : Type*} [Group G] {d N Nt Ns : ℕ}

/-- Holonomy around a plaquette on the symmetric torus:
U_p = U(l₁) · U(l₂) · U(l₃)⁻¹ · U(l₄)⁻¹. -/
def plaquetteHolonomy (U : GaugeConnection G d N) (p : LatticePlaquette d N) : G :=
  let l := p.boundaryLinks
  U (l 0) * U (l 1) * (U (l 2))⁻¹ * (U (l 3))⁻¹

/-- Holonomy around a 2D plaquette on the asymmetric lattice. -/
def asymPlaquetteHolonomy (U : AsymGaugeConnection G Nt Ns)
    (p : AsymPlaquette Nt Ns) : G :=
  let l := p.boundaryLinks
  U (l 0) * U (l 1) * (U (l 2))⁻¹ * (U (l 3))⁻¹

/-! ## Gauge transformations -/

/-- A gauge transformation on the symmetric torus: G-valued function on sites. -/
def GaugeTransform (G : Type*) (d : ℕ) (N : ℕ) := GaussianField.FinLatticeSites d N → G

/-- A gauge transformation on the asymmetric lattice. -/
def AsymGaugeTransform (G : Type*) (Nt Ns : ℕ) := GaussianField.AsymLatticeSites Nt Ns → G

/-- Apply a gauge transformation to a connection:
U'(link) = g(source) · U(link) · g(target)⁻¹. -/
def gaugeTransformConnection (g : GaugeTransform G d N)
    (U : GaugeConnection G d N) : GaugeConnection G d N :=
  fun l => g l.site * U l * (g l.target)⁻¹

/-- Holonomy is gauge-covariant: under g, U_p ↦ g(x) · U_p · g(x)⁻¹. -/
theorem holonomy_gauge_covariant (g : GaugeTransform G d N)
    (U : GaugeConnection G d N) (p : LatticePlaquette d N) :
    plaquetteHolonomy (gaugeTransformConnection g U) p =
    g p.site * plaquetteHolonomy U p * (g p.site)⁻¹ := by
  simp only [plaquetteHolonomy, gaugeTransformConnection, LatticePlaquette.boundaryLinks,
    LatticeLink.target]
  -- Requires: siteShift commutes in different directions (shifts are independent)
  -- Then the intermediate g terms telescope, leaving g(x) · U_p · g(x)⁻¹
  sorry
