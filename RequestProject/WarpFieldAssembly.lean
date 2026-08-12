import RequestProject.WarpRigidity
import RequestProject.PolarCorrectionJordan

/-!
# Warp-field assembly: FE residue pairings become warp identities

The packaging half of the warp program (registered 2026-08-10).  The
compiled residue ledger produces, at each restored twisted functional
equation, a *reflection pairing* on the polar modes: the ledger is closed
under `ρ ↦ 1−ρ` (centres `μ ↦ −μ`) and the paired coefficients satisfy
`r(1−ρ) = −η·A^{1/2−ρ}·r(ρ)` (`ResidueLedger.residue_pairing`;
`fe_residue_transport` at simple-pole scope).  This file compiles the
finite algebra that converts exactly that pairing data into the warp
hypothesis shape consumed by `three_warp_ledger_empty`:

* `ledger_reflection_warp` — a reflection-closed ledger with FE pairing at
  log-conductor `L` satisfies the warp identity
  `R(−u−L) = (−η)·R(u)` on the polar carrier `R = expSum μ c 0`.  The
  conductor content cancels mode-by-mode (`e^{−μL}·e^{μL} = 1`): the warp
  scalar is `−η` — pure sign, no modulus data survives.
* the ε ladder — the channel-sign bookkeeping (`channelSign`,
  `sgnChannels`): even forms have sign-free channels at every rung
  (`ε = 1`, so the warp scalar is `−1 ≠ 1`); odd forms carry all `r+1`
  channels, `ε(Sym^r) = (−1)^{(r+1)/2}`, with the central-kill classifier
  `ε = 1 ↔ r ≡ 3 [MOD 4]` (rung 5: `ε = i⁶ = −1`).  The channel-count
  model (parity toggles all `r+1` Γℝ-factors as a block at level 1) is the
  session-pinned derivation; the compiled content is the sign algebra.
* `rung_ledger_empty_of_reflection_pairings` — the constructor: three
  reflection pairings at distinct primes with an even-channel scalar feed
  `three_warp_ledger_empty` directly; the ledger dies, `R ≡ 0`.

Remaining per-rung inputs are exactly the pairing fields: the three
restored twisted FEs (licensed JPSS/Kim–Shahidi factors through the
restoration polynomial identity; conductor `A_χq = A_*·q^{r+1}`, Artin
exponent, `κ = r+1`).  No `axiom`, no `sorry`.
-/

open CriticalLinePhasor.PolarCorrection
open Polynomial

namespace CriticalLinePhasor.WarpFieldAssembly

open CriticalLinePhasor.WarpRigidity

variable {n : ℕ}

/-- **FE pairing ⟹ warp identity.**  If the ledger is closed under the
reflection `τ` (`μ(τi) = −μᵢ`) and the paired coefficients carry the FE
scalar at log-conductor `L` (`c(τi) = −η·e^{−μᵢL}·cᵢ`), then the polar
carrier satisfies the warp identity with translation `L` and scalar `−η`:
the conductor factors cancel mode-by-mode. -/
theorem ledger_reflection_warp (μ c : Fin n → ℂ) (η : ℂ) (L : ℝ)
    (τ : Equiv.Perm (Fin n))
    (hμτ : ∀ i, μ (τ i) = -(μ i))
    (hcτ : ∀ i, c (τ i) = -η * Complex.exp (-(μ i) * (L : ℂ)) * c i) :
    ∀ u : ℂ, expSum μ c 0 (-u - (L : ℝ)) = (-η) * expSum μ c 0 u := by
  intro u
  simp only [expSum, pow_zero, mul_one]
  calc ∑ i, c i * Complex.exp (μ i * (-u - (L : ℂ)))
      = ∑ i, c (τ i) * Complex.exp (μ (τ i) * (-u - (L : ℂ))) :=
        (Equiv.sum_comp τ
          (fun i => c i * Complex.exp (μ i * (-u - (L : ℂ))))).symm
    _ = ∑ i, (-η) * (c i * Complex.exp (μ i * u)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hμτ i, hcτ i]
        have hexp : Complex.exp (-(μ i) * (L : ℂ))
            * Complex.exp (-(μ i) * (-u - (L : ℂ)))
            = Complex.exp (μ i * u) := by
          rw [← Complex.exp_add]
          congr 1
          ring
        calc (-η * Complex.exp (-(μ i) * (L : ℂ)) * c i)
              * Complex.exp (-(μ i) * (-u - (L : ℂ)))
            = -η * c i * (Complex.exp (-(μ i) * (L : ℂ))
                * Complex.exp (-(μ i) * (-u - (L : ℂ)))) := by ring
          _ = -η * c i * Complex.exp (μ i * u) := by rw [hexp]
          _ = -η * (c i * Complex.exp (μ i * u)) := by ring
    _ = (-η) * ∑ i, c i * Complex.exp (μ i * u) := by
        rw [Finset.mul_sum]

/-! ## Higher-order poles / Jordan blocks -/

/-- The polar carrier with polynomial Jordan coefficients. -/
noncomputable def expPolySum (μ : Fin n → ℂ) (P : Fin n → ℂ[X]) (u : ℂ) : ℂ :=
  ∑ i, (P i).eval u * Complex.exp (μ i * u)

/-- **Higher-order FE pairing ⟹ warp identity.**  The polynomial pairing contains the affine
reflection `u ↦ -u-L`; after reindexing the reflected ledger, the conductor exponent again
cancels mode by mode.  Constant polynomials recover `ledger_reflection_warp`. -/
theorem ledger_reflection_warp_jordan
    (μ : Fin n → ℂ) (P : Fin n → ℂ[X]) (η : ℂ) (L : ℝ)
    (τ : Equiv.Perm (Fin n))
    (hμτ : ∀ i, μ (τ i) = -(μ i))
    (hPτ : ∀ i u, (P (τ i)).eval (-u - (L : ℂ)) =
      -η * Complex.exp (-(μ i) * (L : ℂ)) * (P i).eval u) :
    ∀ u : ℂ, expPolySum μ P (-u - (L : ℝ)) = (-η) * expPolySum μ P u := by
  intro u
  simp only [expPolySum]
  calc
    ∑ i, (P i).eval (-u - (L : ℂ)) *
        Complex.exp (μ i * (-u - (L : ℂ)))
      = ∑ i, (P (τ i)).eval (-u - (L : ℂ)) *
          Complex.exp (μ (τ i) * (-u - (L : ℂ))) :=
        (Equiv.sum_comp τ
          (fun i ↦ (P i).eval (-u - (L : ℂ)) *
            Complex.exp (μ i * (-u - (L : ℂ))))).symm
    _ = ∑ i, (-η) * ((P i).eval u * Complex.exp (μ i * u)) := by
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [hμτ i, hPτ i u]
      have hexp : Complex.exp (-(μ i) * (L : ℂ)) *
          Complex.exp (-(μ i) * (-u - (L : ℂ))) =
          Complex.exp (μ i * u) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      calc
        (-η * Complex.exp (-(μ i) * (L : ℂ)) * (P i).eval u) *
            Complex.exp (-(μ i) * (-u - (L : ℂ)))
          = -η * (P i).eval u *
              (Complex.exp (-(μ i) * (L : ℂ)) *
                Complex.exp (-(μ i) * (-u - (L : ℂ)))) := by ring
        _ = -η * ((P i).eval u * Complex.exp (μ i * u)) := by rw [hexp]; ring
    _ = (-η) * ∑ i, (P i).eval u * Complex.exp (μ i * u) := by
      rw [Finset.mul_sum]

/-! ## The ε ladder: channel-sign bookkeeping -/

/-- Channel-sign model: each `sgn`-carrying `Γℝ` channel contributes a
factor `i` to the root sign. -/
noncomputable def channelSign (m : ℕ) : ℂ := Complex.I ^ m

/-- `sgn`-channel count at rung `r`: at level 1 the form's parity toggles
all `r + 1` channels as a block — even forms carry none, odd forms all. -/
def sgnChannels (oddForm : Bool) (r : ℕ) : ℕ := if oddForm then r + 1 else 0

/-- **Even forms: `ε = 1` at every rung** — the clean highway. -/
theorem epsilon_even_form (r : ℕ) : channelSign (sgnChannels false r) = 1 := by
  simp [channelSign, sgnChannels]

/-- **Odd forms: `ε(Sym^r) = (−1)^{(r+1)/2}`** at odd rungs. -/
theorem epsilon_odd_form (r : ℕ) (hr : Odd r) :
    channelSign (sgnChannels true r) = (-1 : ℂ) ^ ((r + 1) / 2) := by
  obtain ⟨k, hk⟩ := hr
  subst hk
  simp only [channelSign, sgnChannels, if_true]
  have h1 : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
  rw [h1, pow_mul, Complex.I_sq]
  congr 1
  omega

/-- Rung 5, odd form: `ε = i⁶ = −1` (the session's pinned value for
1.0.1.1.1). -/
theorem epsilon_rung_five_odd : channelSign (sgnChannels true 5) = -1 := by
  show Complex.I ^ 6 = -1
  rw [show (6 : ℕ) = 2 * 3 from rfl, pow_mul, Complex.I_sq]
  norm_num

/-- **The central-kill classifier for odd forms**: `ε = 1` exactly at
rungs `r ≡ 3 [MOD 4]` — where the central mode dies; it survives at
`r ≡ 1 [MOD 4]` (5, 9, 13, …). -/
theorem epsilon_odd_eq_one_iff (r : ℕ) (hr : Odd r) :
    channelSign (sgnChannels true r) = 1 ↔ r % 4 = 3 := by
  obtain ⟨k, hk⟩ := hr
  subst hk
  rw [epsilon_odd_form _ ⟨k, rfl⟩]
  have h2 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  rw [h2, neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1),
    Nat.even_iff]
  omega

/-- The even-channel warp scalar `−η = −1` is not `1` — the hypothesis
`hw₁` of the keystone, discharged parametrically. -/
theorem even_channel_warp_scalar_ne_one {η : ℂ} (hη : η = 1) :
    -η ≠ 1 := by
  rw [hη]
  norm_num

/-! ## The constructor: pairings in, empty ledger out -/

/-- **The assembled even-channel rung theorem.**  Three FE reflection
pairings at distinct primes (translations `κ·log p`, licensed restored
FEs), with the first channel even (`η₁ = 1`), empty the finite simple
ledger: every mode coefficient is zero.  This is
`three_warp_ledger_empty` with its warp hypotheses *built* from pairing
data by `ledger_reflection_warp` — the *seat* of the rung, awaiting only
the per-rung pairing fields. -/
theorem rung_ledger_empty_of_reflection_pairings
    (μ c : Fin n → ℂ) (hμ : Function.Injective μ)
    {κ : ℝ} (hκ : κ ≠ 0)
    {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (η₁ η₂ η₃ : ℂ) (hη₁ : η₁ = 1)
    (τ₁ τ₂ τ₃ : Equiv.Perm (Fin n))
    (hμτ₁ : ∀ i, μ (τ₁ i) = -(μ i))
    (hcτ₁ : ∀ i, c (τ₁ i)
      = -η₁ * Complex.exp (-(μ i) * ((κ * Real.log p : ℝ) : ℂ)) * c i)
    (hμτ₂ : ∀ i, μ (τ₂ i) = -(μ i))
    (hcτ₂ : ∀ i, c (τ₂ i)
      = -η₂ * Complex.exp (-(μ i) * ((κ * Real.log q : ℝ) : ℂ)) * c i)
    (hμτ₃ : ∀ i, μ (τ₃ i) = -(μ i))
    (hcτ₃ : ∀ i, c (τ₃ i)
      = -η₃ * Complex.exp (-(μ i) * ((κ * Real.log r : ℝ) : ℂ)) * c i) :
    ∀ i, c i = 0 :=
  three_warp_ledger_empty μ c hμ hκ hp hq hr hpq hpr hqr
    (-η₁) (-η₂) (-η₃)
    (even_channel_warp_scalar_ne_one hη₁)
    (ledger_reflection_warp μ c η₁ _ τ₁ hμτ₁ hcτ₁)
    (ledger_reflection_warp μ c η₂ _ τ₂ hμτ₂ hcτ₂)
    (ledger_reflection_warp μ c η₃ _ τ₃ hμτ₃ hcτ₃)

/-- Carrier form of the constructor: the polar carrier vanishes
identically. -/
theorem rung_polar_carrier_zero_of_reflection_pairings
    (μ c : Fin n → ℂ) (hμ : Function.Injective μ)
    {κ : ℝ} (hκ : κ ≠ 0)
    {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (η₁ η₂ η₃ : ℂ) (hη₁ : η₁ = 1)
    (τ₁ τ₂ τ₃ : Equiv.Perm (Fin n))
    (hμτ₁ : ∀ i, μ (τ₁ i) = -(μ i))
    (hcτ₁ : ∀ i, c (τ₁ i)
      = -η₁ * Complex.exp (-(μ i) * ((κ * Real.log p : ℝ) : ℂ)) * c i)
    (hμτ₂ : ∀ i, μ (τ₂ i) = -(μ i))
    (hcτ₂ : ∀ i, c (τ₂ i)
      = -η₂ * Complex.exp (-(μ i) * ((κ * Real.log q : ℝ) : ℂ)) * c i)
    (hμτ₃ : ∀ i, μ (τ₃ i) = -(μ i))
    (hcτ₃ : ∀ i, c (τ₃ i)
      = -η₃ * Complex.exp (-(μ i) * ((κ * Real.log r : ℝ) : ℂ)) * c i) :
    ∀ u : ℂ, expSum μ c 0 u = 0 := by
  intro u
  have hzero := rung_ledger_empty_of_reflection_pairings μ c hμ hκ
    hp hq hr hpq hpr hqr η₁ η₂ η₃ hη₁ τ₁ τ₂ τ₃
    hμτ₁ hcτ₁ hμτ₂ hcτ₂ hμτ₃ hcτ₃
  simp only [expSum]
  apply Finset.sum_eq_zero
  intro i _
  rw [hzero i]
  ring

end CriticalLinePhasor.WarpFieldAssembly

#print axioms CriticalLinePhasor.WarpFieldAssembly.ledger_reflection_warp
#print axioms CriticalLinePhasor.WarpFieldAssembly.ledger_reflection_warp_jordan
#print axioms CriticalLinePhasor.WarpFieldAssembly.epsilon_odd_eq_one_iff
#print axioms CriticalLinePhasor.WarpFieldAssembly.rung_ledger_empty_of_reflection_pairings
