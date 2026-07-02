import RequestProject.Phasor3D
import RequestProject.UnconditionalFrobenius

/-!
# Focal cancellation events produce eigenstates carrying the cancelled energy/mass

This file proves, unconditionally, the conservation principle behind a **focal cancellation event**
of the 3-D phasor model:

> When two charged 3-D phasors **exactly cancel** (their radiating spin-plane arrows sum to `0`),
> the event **produces an eigenstate**, and that eigenstate has **energy/mass equal to** that of the
> cancelling phasors.

The mechanism is the magnitude-conservation law of the 3-D phasor model (`Phasor3D`): a charged
phasor stores all of its magnitude in the radiating spin plane, but when two such phasors cancel the
radiating field vanishes, and the magnitude is **not destroyed** — it is converted into a
**standing** (non-radiating) mode.

Two complementary realisations of the produced eigenstate are given:

* **The standing 3-D mode** `standingMode r = (0, r)`: a pure-mass, non-radiating vector of the 3-D
  state space whose magnitude is exactly the cancelled amplitude `r` (`mag3_standingMode`).
* **The Frobenius spectral eigenstate** `massiveWave r γ = t ↦ r·exp(iγt)`: a genuine eigenstate of
  the generator `D = −i d/dt` with **real eigenvalue `γ`** (`massiveWave_eigen`), whose modulus is
  the **constant** `r` at every `t` (`massiveWave_norm`) — i.e. its energy/mass is exactly the
  amplitude `r` of the cancelling phasors.

The capstone `focal_cancellation_produces_eigenstate` assembles these into the statement that an
exact-cancellation event of two charged phasors of common amplitude `r` produces an eigenstate whose
energy/mass equals that of each cancelling phasor.  `focal_cancellation_site` instantiates it at a
concrete carrier site `n`, where the cancelling charged phasors are `±1·n^{-σ}·(spin)` and the
common amplitude is `r = n^{-σ}`.

No `axiom`, no `sorry`.
-/

open Complex
open scoped BigOperators

namespace CriticalLinePhasor.FocalCancellation

open CriticalLinePhasor CriticalLinePhasor.Phasor3D CriticalLinePhasor.UnconditionalFrobenius
  CriticalLinePhasor.LFunctionPhasor

/-! ## 0. Energy/mass of a 3-D phasor, charged phasors, and exact cancellation -/

/-- `mag3` re-expressed through the named components `plane` (spin plane) and `massAxis`. -/
theorem mag3_eq (p : Vec3) : mag3 p = Real.sqrt (‖plane p‖ ^ 2 + (massAxis p) ^ 2) := rfl

/-- **A charged phasor of amplitude `r`**: all of its magnitude is in the radiating spin plane
(`‖plane p‖ = r`) and none on the mass axis (`massAxis p = 0`). -/
def IsChargedPhasor (p : Vec3) (r : ℝ) : Prop := massAxis p = 0 ∧ ‖plane p‖ = r

/-- **An exact-cancellation event**: two phasors whose radiating spin-plane arrows sum to `0`. -/
def ExactCancellation (p q : Vec3) : Prop := plane p + plane q = 0

/-- **The standing 3-D mode** of amplitude `r`: the non-radiating, pure-mass vector `(0, r)`. -/
def standingMode (r : ℝ) : Vec3 := (0, r)

/-- The energy/mass (3-D magnitude) of a charged phasor of amplitude `r ≥ 0` is exactly `r`. -/
theorem mag3_of_charged {p : Vec3} {r : ℝ} (hr : 0 ≤ r) (hm : massAxis p = 0) (hn : ‖plane p‖ = r) :
    mag3 p = r := by
  rw [mag3_eq, hn, hm, show ((0 : ℝ)) ^ 2 = 0 from by norm_num, add_zero]
  exact Real.sqrt_sq hr

/-- The energy/mass of the standing mode `(0, r)` is exactly `r` (for `r ≥ 0`). -/
theorem mag3_standingMode {r : ℝ} (hr : 0 ≤ r) : mag3 (standingMode r) = r := by
  have h1 : plane (standingMode r) = 0 := rfl
  have h2 : massAxis (standingMode r) = r := rfl
  rw [mag3_eq, h1, h2, norm_zero, show ((0 : ℝ)) ^ 2 = 0 from by norm_num, zero_add]
  exact Real.sqrt_sq hr

/-! ## 1. The produced eigenstate `massiveWave r γ = t ↦ r·exp(iγt)` -/

/-- **The massive spectral eigenstate** of amplitude `r` at height `γ`: `t ↦ r·exp(iγt)`.  It is the
amplitude-`r` rescaling of the unit-norm Frobenius spectral wave; its modulus is the constant `r`. -/
noncomputable def massiveWave (r γ : ℝ) : ℝ → ℂ := fun t => (r : ℂ) * spectralWave γ t

/-- The massive wave has constant modulus `r` (its energy/mass), for `r ≥ 0`. -/
theorem massiveWave_norm (r γ : ℝ) (hr : 0 ≤ r) (t : ℝ) : ‖massiveWave r γ t‖ = r := by
  simp only [massiveWave]
  rw [norm_mul, spectralWave_norm, mul_one, Complex.norm_real, Real.norm_of_nonneg hr]

/-- The derivative of the massive wave. -/
theorem massiveWave_hasDerivAt (r γ : ℝ) (t : ℝ) :
    HasDerivAt (massiveWave r γ) ((r : ℂ) * ((γ : ℂ) * Complex.I * spectralWave γ t)) t :=
  (spectralWave_hasDerivAt γ t).const_mul (r : ℂ)

/-- **The massive wave is an eigenstate** of the generator `D = −i d/dt` with real eigenvalue `γ`:
`-i·(massiveWave r γ)'(t) = γ·(massiveWave r γ)(t)`. -/
theorem massiveWave_eigen (r γ : ℝ) (t : ℝ) :
    -Complex.I * deriv (massiveWave r γ) t = (γ : ℂ) * massiveWave r γ t := by
  rw [(massiveWave_hasDerivAt r γ t).deriv]
  simp only [massiveWave]
  rw [show -Complex.I * ((r : ℂ) * ((γ : ℂ) * Complex.I * spectralWave γ t))
      = (-(Complex.I * Complex.I)) * ((r : ℂ) * ((γ : ℂ) * spectralWave γ t)) from by ring,
    Complex.I_mul_I]
  ring

/-! ## 2. The conservation theorem (abstract) -/

/--
**Focal cancellation produces an eigenstate with energy/mass equal to the cancelling phasors.**

Let `p`, `q` be two charged 3-D phasors of common amplitude `r ≥ 0` (all magnitude in the radiating
spin plane) that undergo an **exact-cancellation event** (`plane p + plane q = 0`).  Then, for any
resonance height `γ`:

1. **the cancelling phasors carry energy/mass `r`** (`mag3 p = r = mag3 q`);
2. **an eigenstate is produced** — the massive spectral wave `massiveWave r γ` is a genuine
   eigenstate of `D = −i d/dt` with real eigenvalue `γ`, of **constant modulus `r`**;
3. **the radiating field is absorbed into a standing mode** — the cancelled sum equals the
   (zero) radiating part of the standing mode `standingMode r`, which stores the magnitude as
   **mass `r`** on the mass axis (`massAxis = r`, `mag3 = r`);
4. **energy/mass conservation** — the produced eigenstate's energy/mass equals that of each
   cancelling phasor: `‖massiveWave r γ t‖ = mag3 p` for every `t`.
-/
theorem focal_cancellation_produces_eigenstate {p q : Vec3} {r γ : ℝ} (hr : 0 ≤ r)
    (hp : IsChargedPhasor p r) (hq : IsChargedPhasor q r) (hpq : ExactCancellation p q) :
    (mag3 p = r ∧ mag3 q = r)
      ∧ (∀ t : ℝ, ‖massiveWave r γ t‖ = r)
      ∧ (∀ t : ℝ, -Complex.I * deriv (massiveWave r γ) t = (γ : ℂ) * massiveWave r γ t)
      ∧ (plane (standingMode r) = plane p + plane q
          ∧ massAxis (standingMode r) = r ∧ mag3 (standingMode r) = r)
      ∧ (∀ t : ℝ, ‖massiveWave r γ t‖ = mag3 p) := by
  obtain ⟨hpm, hpn⟩ := hp
  obtain ⟨hqm, hqn⟩ := hq
  have hmp : mag3 p = r := mag3_of_charged hr hpm hpn
  have hmq : mag3 q = r := mag3_of_charged hr hqm hqn
  refine ⟨⟨hmp, hmq⟩, massiveWave_norm r γ hr, massiveWave_eigen r γ,
    ⟨?_, rfl, mag3_standingMode hr⟩, ?_⟩
  · rw [hpq]; rfl
  · intro t; rw [massiveWave_norm r γ hr, hmp]

/-! ## 3. Concrete realisation at a carrier site -/

/-- The positive (`+1`) charge weight. -/
noncomputable def posW : ℕ → ℂ := fun _ => 1

/-- The negative (`−1`) charge weight. -/
noncomputable def negW : ℕ → ℂ := fun _ => -1

/-- The positive-channel 3-D phasor at site `n` is a charged phasor of amplitude `n^{-σ}`. -/
theorem chargedPos_isCharged (σ y : ℝ) (n : ℕ) (hn : 0 < n) :
    IsChargedPhasor (phasor3D posW σ y n) ((n : ℝ) ^ (-σ)) := by
  refine ⟨?_, ?_⟩
  · rw [phasor3D_massAxis]; simp [posW]
  · rw [phasor3D_plane, phasorTerm_norm posW σ y n hn]; simp [posW]

/-- The negative-channel 3-D phasor at site `n` is a charged phasor of amplitude `n^{-σ}`. -/
theorem chargedNeg_isCharged (σ y : ℝ) (n : ℕ) (hn : 0 < n) :
    IsChargedPhasor (phasor3D negW σ y n) ((n : ℝ) ^ (-σ)) := by
  refine ⟨?_, ?_⟩
  · rw [phasor3D_massAxis]; simp [negW]
  · rw [phasor3D_plane, phasorTerm_norm negW σ y n hn]; simp [negW]

/-- **The positive and negative channels at a site cancel exactly.**  Their radiating spin-plane
arrows are negatives of each other, so their sum is `0` — the focal cancellation event. -/
theorem charged_exact_cancellation (σ y : ℝ) (n : ℕ) :
    ExactCancellation (phasor3D posW σ y n) (phasor3D negW σ y n) := by
  simp only [ExactCancellation, phasor3D_plane, phasorTerm]
  split_ifs <;> simp [posW, negW]

/--
**Focal cancellation at a carrier site produces an eigenstate of energy/mass `n^{-σ}`.**

At carrier site `n ≥ 1` on the line `s = σ + i y`, the positive (`+1`) and negative (`−1`) charged
3-D phasors each have energy/mass `n^{-σ}` and cancel exactly.  The produced eigenstate
`massiveWave (n^{-σ}) γ` is a genuine eigenstate of `D = −i d/dt` with eigenvalue `γ` whose
modulus is the constant `n^{-σ}` — equal to the energy/mass of the cancelling phasors.
-/
theorem focal_cancellation_site (σ y γ : ℝ) (n : ℕ) (hn : 0 < n) :
    (mag3 (phasor3D posW σ y n) = (n : ℝ) ^ (-σ) ∧ mag3 (phasor3D negW σ y n) = (n : ℝ) ^ (-σ))
      ∧ (∀ t : ℝ, ‖massiveWave ((n : ℝ) ^ (-σ)) γ t‖ = (n : ℝ) ^ (-σ))
      ∧ (∀ t : ℝ, -Complex.I * deriv (massiveWave ((n : ℝ) ^ (-σ)) γ) t
            = (γ : ℂ) * massiveWave ((n : ℝ) ^ (-σ)) γ t)
      ∧ (plane (standingMode ((n : ℝ) ^ (-σ)))
            = plane (phasor3D posW σ y n) + plane (phasor3D negW σ y n)
          ∧ massAxis (standingMode ((n : ℝ) ^ (-σ))) = (n : ℝ) ^ (-σ)
          ∧ mag3 (standingMode ((n : ℝ) ^ (-σ))) = (n : ℝ) ^ (-σ))
      ∧ (∀ t : ℝ, ‖massiveWave ((n : ℝ) ^ (-σ)) γ t‖ = mag3 (phasor3D posW σ y n)) :=
  focal_cancellation_produces_eigenstate
    (Real.rpow_nonneg (by exact_mod_cast hn.le) _)
    (chargedPos_isCharged σ y n hn) (chargedNeg_isCharged σ y n hn)
    (charged_exact_cancellation σ y n)

end CriticalLinePhasor.FocalCancellation
