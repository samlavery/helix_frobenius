import RequestProject.WarpFieldAssembly

/-!
# The rung capstone: warp data annihilates the polar carrier

The end-to-end composition of the campaign's compiled chain, with every
remaining analytic input a NAMED FIELD.  A `RungWarpData` packages the
centered polar-carrier modes of a rung quotient together with the three
harmonized warp identities and the even-channel scalar; the capstone
theorem returns the empty ledger — every mode coefficient zero, the polar
carrier identically zero.

Field-by-field discharge register (the honest remainder of the program):
* `μ, c` — the simple-mode representation of the rung quotient's polar
  correction (the contour-shift dictionary; simple scope justified at
  simple denominator zeros by the compiled semisimplicity computation,
  Jordan blocks handled by `PolarCorrectionJordan` when needed);
* `warp₁ warp₂ warp₃` — the harmonized warp identities: derived from the
  completed functional equations of the LICENSED factors through the
  stage-1 additive construction with principal-channel restoration
  (`carry_warp_covariance` compiled; fuse #3 assembled as
  `CarryDetection.carry_detects_simple_pole`; the FE-pairing → warp
  packaging compiled as `WarpFieldAssembly.ledger_reflection_warp`, so
  each field is discharged by exhibiting the restored FE's reflection
  pairing on the ledger);
* `w₁ ≠ 1` — the even-channel scalar (`= −1`); discharged parametrically
  by the compiled ε ladder (`WarpFieldAssembly.epsilon_even_form` +
  `even_channel_warp_scalar_ne_one`);
* `κ` — the degree multiplier `r + 1` (conductor law, uniform).

Downstream (all compiled): the vanishing polar carrier feeds
`polar_correction_empties_ledger` / `dichotomy_containment_at_simple_zeros`
(entirety at simple zeros), with the compiled quotient FE this is the
Riemann--Hecke package, i.e. `hfeq` — the single gate of
`CarrierTheta.coefficientTheta_initial_identification` and the CPS
checklist.  The seat, proven, opens the gate.  No `axiom`, no `sorry`.
-/

open CriticalLinePhasor.PolarCorrection
open Polynomial

namespace CriticalLinePhasor.RungCapstone

open CriticalLinePhasor.WarpRigidity
open CriticalLinePhasor.WarpFieldAssembly

/-- The rung's warp package: polar-carrier modes plus the three harmonized
warp identities and the even-channel scalar. -/
structure RungWarpData (n : ℕ) where
  μ : Fin n → ℂ
  c : Fin n → ℂ
  hμ : Function.Injective μ
  κ : ℝ
  hκ : κ ≠ 0
  p : ℕ
  q : ℕ
  r : ℕ
  hp : p.Prime
  hq : q.Prime
  hr : r.Prime
  hpq : p ≠ q
  hpr : p ≠ r
  hqr : q ≠ r
  w₁ : ℂ
  w₂ : ℂ
  w₃ : ℂ
  hw₁ : w₁ ≠ 1
  warp₁ : ∀ u : ℂ, expSum μ c 0 (-u - (κ * Real.log p : ℝ))
    = w₁ * expSum μ c 0 u
  warp₂ : ∀ u : ℂ, expSum μ c 0 (-u - (κ * Real.log q : ℝ))
    = w₂ * expSum μ c 0 u
  warp₃ : ∀ u : ℂ, expSum μ c 0 (-u - (κ * Real.log r : ℝ))
    = w₃ * expSum μ c 0 u

/-- Construct all three stored warp identities from the three arithmetic functional-equation
residue pairings.  The conductor translations are `κ log p`, `κ log q`, and `κ log r`; the
warp scalars are the corresponding `-η`. -/
noncomputable def RungWarpData.ofReflectionPairings
    {n : ℕ} (μ c : Fin n → ℂ) (hμ : Function.Injective μ)
    {κ : ℝ} (hκ : κ ≠ 0)
    {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (η₁ η₂ η₃ : ℂ) (hη₁ : η₁ = 1)
    (τ₁ τ₂ τ₃ : Equiv.Perm (Fin n))
    (hμτ₁ : ∀ i, μ (τ₁ i) = -(μ i))
    (hcτ₁ : ∀ i, c (τ₁ i) =
      -η₁ * Complex.exp (-μ i * ((κ * Real.log p : ℝ) : ℂ)) * c i)
    (hμτ₂ : ∀ i, μ (τ₂ i) = -(μ i))
    (hcτ₂ : ∀ i, c (τ₂ i) =
      -η₂ * Complex.exp (-μ i * ((κ * Real.log q : ℝ) : ℂ)) * c i)
    (hμτ₃ : ∀ i, μ (τ₃ i) = -(μ i))
    (hcτ₃ : ∀ i, c (τ₃ i) =
      -η₃ * Complex.exp (-μ i * ((κ * Real.log r : ℝ) : ℂ)) * c i) :
    RungWarpData n where
  μ := μ
  c := c
  hμ := hμ
  κ := κ
  hκ := hκ
  p := p
  q := q
  r := r
  hp := hp
  hq := hq
  hr := hr
  hpq := hpq
  hpr := hpr
  hqr := hqr
  w₁ := -η₁
  w₂ := -η₂
  w₃ := -η₃
  hw₁ := even_channel_warp_scalar_ne_one hη₁
  warp₁ := ledger_reflection_warp μ c η₁ _ τ₁ hμτ₁ hcτ₁
  warp₂ := ledger_reflection_warp μ c η₂ _ τ₂ hμτ₂ hcτ₂
  warp₃ := ledger_reflection_warp μ c η₃ _ τ₃ hμτ₃ hcτ₃

/-- The higher-order-pole version of the rung warp package.  A polynomial coefficient records the
entire Jordan block at one polar exponent. -/
structure JordanRungWarpData (n : ℕ) where
  μ : Fin n → ℂ
  P : Fin n → ℂ[X]
  hμ : Function.Injective μ
  κ : ℝ
  hκ : κ ≠ 0
  p : ℕ
  q : ℕ
  r : ℕ
  hp : p.Prime
  hq : q.Prime
  hr : r.Prime
  hpq : p ≠ q
  hpr : p ≠ r
  hqr : q ≠ r
  w₁ : ℂ
  w₂ : ℂ
  w₃ : ℂ
  hw₁ : w₁ ≠ 1
  warp₁ : ∀ u : ℂ, expPolySum μ P (-u - (κ * Real.log p : ℝ)) =
    w₁ * expPolySum μ P u
  warp₂ : ∀ u : ℂ, expPolySum μ P (-u - (κ * Real.log q : ℝ)) =
    w₂ * expPolySum μ P u
  warp₃ : ∀ u : ℂ, expPolySum μ P (-u - (κ * Real.log r : ℝ)) =
    w₃ * expPolySum μ P u

/-- Construct the three higher-order/Jordan warp identities from the affine polynomial residue
pairings furnished by the three completed functional equations. -/
noncomputable def JordanRungWarpData.ofReflectionPairings
    {n : ℕ} (μ : Fin n → ℂ) (P : Fin n → ℂ[X]) (hμ : Function.Injective μ)
    {κ : ℝ} (hκ : κ ≠ 0)
    {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (η₁ η₂ η₃ : ℂ) (hη₁ : η₁ = 1)
    (τ₁ τ₂ τ₃ : Equiv.Perm (Fin n))
    (hμτ₁ : ∀ i, μ (τ₁ i) = -(μ i))
    (hPτ₁ : ∀ i u, (P (τ₁ i)).eval (-u - ((κ * Real.log p : ℝ) : ℂ)) =
      -η₁ * Complex.exp (-μ i * ((κ * Real.log p : ℝ) : ℂ)) * (P i).eval u)
    (hμτ₂ : ∀ i, μ (τ₂ i) = -(μ i))
    (hPτ₂ : ∀ i u, (P (τ₂ i)).eval (-u - ((κ * Real.log q : ℝ) : ℂ)) =
      -η₂ * Complex.exp (-μ i * ((κ * Real.log q : ℝ) : ℂ)) * (P i).eval u)
    (hμτ₃ : ∀ i, μ (τ₃ i) = -(μ i))
    (hPτ₃ : ∀ i u, (P (τ₃ i)).eval (-u - ((κ * Real.log r : ℝ) : ℂ)) =
      -η₃ * Complex.exp (-μ i * ((κ * Real.log r : ℝ) : ℂ)) * (P i).eval u) :
    JordanRungWarpData n where
  μ := μ
  P := P
  hμ := hμ
  κ := κ
  hκ := hκ
  p := p
  q := q
  r := r
  hp := hp
  hq := hq
  hr := hr
  hpq := hpq
  hpr := hpr
  hqr := hqr
  w₁ := -η₁
  w₂ := -η₂
  w₃ := -η₃
  hw₁ := even_channel_warp_scalar_ne_one hη₁
  warp₁ := ledger_reflection_warp_jordan μ P η₁ _ τ₁ hμτ₁ hPτ₁
  warp₂ := ledger_reflection_warp_jordan μ P η₂ _ τ₂ hμτ₂ hPτ₂
  warp₃ := ledger_reflection_warp_jordan μ P η₃ _ τ₃ hμτ₃ hPτ₃

variable {n : ℕ}

/-- **The capstone, coefficient form**: the warp package empties the
ledger. -/
theorem rung_ledger_coeffs_zero (D : RungWarpData n) : ∀ i, D.c i = 0 :=
  three_warp_ledger_empty D.μ D.c D.hμ D.hκ D.hp D.hq D.hr D.hpq D.hpr D.hqr
    D.w₁ D.w₂ D.w₃ D.hw₁ D.warp₁ D.warp₂ D.warp₃

/-- **The capstone, carrier form**: the polar carrier vanishes
identically — `R = 0`. -/
theorem rung_polar_carrier_zero (D : RungWarpData n) :
    ∀ u : ℂ, expSum D.μ D.c 0 u = 0 := by
  intro u
  have hzero := rung_ledger_coeffs_zero D
  simp only [expSum]
  apply Finset.sum_eq_zero
  intro i _
  rw [hzero i]
  ring

end CriticalLinePhasor.RungCapstone

#print axioms CriticalLinePhasor.RungCapstone.rung_ledger_coeffs_zero
#print axioms CriticalLinePhasor.RungCapstone.rung_polar_carrier_zero
#print axioms CriticalLinePhasor.RungCapstone.RungWarpData.ofReflectionPairings
#print axioms CriticalLinePhasor.RungCapstone.JordanRungWarpData.ofReflectionPairings
