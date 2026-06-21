import RequestProject.AreaLaw
import RequestProject.ClosedForm
import RequestProject.LFunctionPhasor

/-!
# Spec update: constant height law `z_n = n`, L-dependent growth `e^(mod q)`, active fraction

Additive companion to the geometric model, matching the updated `PHASOR_HELIX_SPEC.md` §2.
Everything here is new; the existing files are untouched and stay `sorry`-free.

* **Constant height law `z_n = n`** (Δz = 1 per integer `n`, NOT per phasor: the neutral bucket
  `χ(n)=0` carries no arrow but still occupies its slot and still ticks the height; counting per
  active phasor would climb by `φ(q)/q` per integer and miss `e^γ` by the active fraction).  Since
  `spin y n = exp(-(y·log n)·i)` spins at rate `log n`, integer `n` sits at `z_n = n = e^{log n}` —
  the height of its own resonant frequency.  So a zero of `L` at frequency `γ` (resonant term
  `n* = e^γ`) lands at height `z = e^γ`, for **every** `L`-function (it rides only on `spin = log n`).
* **L-dependent radial growth `g = e^(mod q)`** (eta `e²`, chi3 `e³`, chi4 `e⁴`, …): the radial gap
  per turn, used as the area-law radius parameter `r`.  The general `radius ~ √n` specializes to
  `carrierRadius / √n → √(e^q / 3)`; same shape for every `L`, only the constant differs.
* **Active fraction `#{a : χ(a) ≠ 0}/q = φ(q)/q`**: only the unit residues carry a spinning arrow,
  so the *live* phasors-per-turn is the geometric count times this fraction.
-/

open scoped BigOperators Real Topology Classical
open Filter Topology

namespace CriticalLinePhasor.Geometry

open Real

/-! ## 1. Constant height law `z_n = n` -/

/-- The **spin rate** of phasor `n`: `log n` (the rate of `spin y n = exp(-(y·log n)·i)` in `y`). -/
noncomputable def spinRate (n : ℕ) : ℝ := Real.log n

/-- The spin phasor really spins at `spinRate`: `spin y n = exp(-(y · spinRate n)·i)`. -/
theorem spin_eq_spinRate (y : ℝ) (n : ℕ) :
    CriticalLinePhasor.LFunctionPhasor.spin y n
      = Complex.exp (-(y * spinRate n) * Complex.I) := rfl

/-- **Constant height law** `z_n = n`: every integer slot rises by the same `Δz = 1`, per
integer `n` (every slot, including `χ(n)=0`), not per active phasor (spec §2). -/
def heightLaw (n : ℕ) : ℝ := n

/-- `Δz = 1` per integer `n`: consecutive heights differ by exactly `1`. -/
theorem heightLaw_step (n : ℕ) : heightLaw (n + 1) - heightLaw n = 1 := by
  unfold heightLaw; push_cast; ring

/-- **Each phasor sits at the height of its own resonant frequency**: `z_n = e^{spinRate n}`
(i.e. `n = e^{log n}`). -/
theorem heightLaw_eq_exp_spinRate (n : ℕ) (hn : 0 < n) :
    heightLaw n = Real.exp (spinRate n) := by
  unfold heightLaw spinRate
  rw [Real.exp_log (by exact_mod_cast hn : (0:ℝ) < n)]

/-- **Zeros land at `z = e^γ`.**  If phasor `n` resonates at frequency `γ` (`spinRate n = γ`), its
height is `e^γ`.  At a zero `γ_k` of `L` the resonant term is `n* = e^{γ_k}`, so the cancellation
sits at height `z = e^{γ_k}` — for every `L`-function (it rides on `spin = log n`). -/
theorem resonance_height {γ : ℝ} {n : ℕ} (hn : 0 < n) (hres : spinRate n = γ) :
    heightLaw n = Real.exp γ := by
  rw [heightLaw_eq_exp_spinRate n hn, hres]

/-! ## 2. L-dependent radial growth `g = e^(mod q)` -/

/-- **L-dependent radial growth** `g = e^(mod q)` (eta `e²`, chi3 `e³`, chi4 `e⁴`, …): the radial
gap per turn, used as the area-law radius parameter `r`. -/
noncomputable def radialGrowth (q : ℕ) : ℝ := Real.exp q

theorem radialGrowth_pos (q : ℕ) : 0 < radialGrowth q := Real.exp_pos _

/-- **Turn gap = `e^(mod q)`.**  The cylindrical radius `(e^q)·k` of the carrier grows by exactly
`e^q` per turn (`k → k+1`). -/
theorem radialGrowth_turn_gap (q : ℕ) (k : ℝ) :
    radialGrowth q * (k + 1) - radialGrowth q * k = radialGrowth q := by ring

/-- **Radius `~ √n` at growth `e^q`.**  Specializing the area law to `r = e^q`:
`carrierRadius p (e^q) n / √n → √(e^q / 3)`.  The `√n` shape is shared by every `L`-function;
only the constant `√(e^q/3)` — hence the per-turn count — is `L`-dependent. -/
theorem carrierRadius_growth_div_sqrt_tendsto (p : ℝ) (q : ℕ) :
    Tendsto (fun n : ℕ => carrierRadius p (radialGrowth q) n / Real.sqrt n) atTop
      (𝓝 (Real.sqrt (Real.exp q / 3))) := by
  have h := carrierRadius_div_sqrt_tendsto p (radialGrowth q) (radialGrowth_pos q)
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have he : radialGrowth q * (Real.pi / 3) / Real.pi = Real.exp q / 3 := by
    unfold radialGrowth; field_simp
  rwa [he] at h

/-! ## 3. Active fraction `#{a : χ(a) ≠ 0}/q = φ(q)/q` -/

variable {q : ℕ} [NeZero q]

/-- The **active residues** of a Dirichlet character (those with `χ(a) ≠ 0`) are exactly the units. -/
theorem active_iff_isUnit (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    χ a ≠ 0 ↔ IsUnit a := by
  constructor
  · intro h; by_contra hu; exact h (χ.map_nonunit hu)
  · intro hu h0
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have h1 : χ a * χ b = 1 := by rw [← map_mul, hb, map_one]
    rw [h0, zero_mul] at h1
    exact one_ne_zero h1.symm

/-- The equivalence between the unit residues of `ZMod q` and its group of units. -/
noncomputable def isUnitSubtypeEquivUnits : {a : ZMod q // IsUnit a} ≃ (ZMod q)ˣ where
  toFun x := x.2.unit
  invFun u := ⟨(u : ZMod q), u.isUnit⟩
  left_inv x := Subtype.ext x.2.unit_spec
  right_inv u := Units.ext u.isUnit.unit_spec

/-- **The active residues number `φ(q)`.**  `#{a : χ(a) ≠ 0} = φ(q)` (the units of `ZMod q`). -/
theorem active_card (χ : DirichletCharacter ℂ q) :
    (Finset.univ.filter (fun a : ZMod q => χ a ≠ 0)).card = Nat.totient q := by
  have hfilter : (Finset.univ.filter (fun a : ZMod q => χ a ≠ 0))
      = (Finset.univ.filter (fun a : ZMod q => IsUnit a)) :=
    Finset.filter_congr (fun a _ => by simp [active_iff_isUnit χ a])
  rw [hfilter, ← Fintype.card_subtype, ← ZMod.card_units_eq_totient q]
  exact Fintype.card_congr isUnitSubtypeEquivUnits

/-- **Active fraction** of a modulus-`q` character: `#{a : χ(a) ≠ 0}/q`. -/
noncomputable def activeFraction (χ : DirichletCharacter ℂ q) : ℝ :=
  ((Finset.univ.filter (fun a : ZMod q => χ a ≠ 0)).card : ℝ) / q

/-- The active fraction equals `φ(q)/q`. -/
theorem activeFraction_eq_totient (χ : DirichletCharacter ℂ q) :
    activeFraction χ = (Nat.totient q : ℝ) / q := by
  unfold activeFraction; rw [active_card χ]

/-- **Live phasors-per-turn = geometric × active fraction.**  The neutral bucket `χ(n)=0` contributes
no spinning arrow, so the live count is the geometric `2π R/u` times `φ(q)/q`. -/
theorem live_per_turn (geo : ℝ) (χ : DirichletCharacter ℂ q) :
    geo * activeFraction χ = geo * (Nat.totient q / q) := by
  rw [activeFraction_eq_totient χ]

end CriticalLinePhasor.Geometry
