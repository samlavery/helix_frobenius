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

/-! ## 4. The height encoding is faithful: real `e^γ`, no branch, no information lost

The height of a vanishing is `z = e^γ` with `γ` **real** (the resonant ordinate, `spinRate n = γ`).
This is the *real* exponential `Real.exp`, NOT the periodic phasor `e^{iγ}` on the unit circle.  The
spin `spin y n = e^{-(y·log n)·i}` is what lives on the circle; the *carrier height* it resonates at
is the real number `e^γ`.  Because `Real.exp : ℝ → ℝ` is a single-valued, globally defined, strictly
monotone injection with the everywhere-defined inverse `Real.log`, the encoding `γ ↦ e^γ` needs no
branch choice and loses no information — `γ` is recovered exactly as `log z`.  By contrast, the
imaginary phasor `y ↦ e^{iy}` is `2π`-periodic, hence not injective, so *that* map would lose
information; the height law deliberately uses the real exponential instead. -/

/-- **The resonance-height map `γ ↦ e^γ` is injective.**  Distinct resonant ordinates land at
distinct heights, so the height encoding loses no information: it is the *real* exponential, with no
winding/branch ambiguity to fix. -/
theorem resonanceHeight_injective : Function.Injective (fun γ : ℝ => Real.exp γ) :=
  Real.exp_injective

/-- **The ordinate is recovered from the height by `log`** — a global, single-valued inverse, so
there is no branch cut: `log (e^γ) = γ`. -/
theorem spinRate_of_resonanceHeight (γ : ℝ) : Real.log (Real.exp γ) = γ :=
  Real.log_exp γ

/-- **The resonance-height map `γ ↦ e^γ` is surjective onto the positive heights.**  Every positive
carrier height `z` is realized by exactly one ordinate, namely `γ = log z` (so `e^{log z} = z`).
Combined with `resonanceHeight_injective` this makes `γ ↦ e^γ` a bijection `ℝ ≃ ℝ_{>0}`: nothing is
lost (injective) and nothing is missed (surjective onto positives). -/
theorem resonanceHeight_surjective_pos {z : ℝ} (hz : 0 < z) :
    ∃ γ : ℝ, Real.exp γ = z :=
  ⟨Real.log z, Real.exp_log hz⟩

/-- **The resonance-height map as an explicit bijection `ℝ ≃ ℝ_{>0}`.**  Forward: ordinate `γ ↦ e^γ`;
inverse: height `z ↦ log z`.  This packages injectivity + surjectivity: the height encoding is a
perfect, branch-free, information-preserving correspondence. -/
noncomputable def resonanceHeightEquiv : ℝ ≃ {z : ℝ // 0 < z} where
  toFun γ := ⟨Real.exp γ, Real.exp_pos γ⟩
  invFun z := Real.log z.1
  left_inv γ := Real.log_exp γ
  right_inv z := Subtype.ext (Real.exp_log z.2)

/-- **No information is lost passing from ordinate to height.**  If two resonant ordinates produce
the same carrier height, they were equal. -/
theorem resonance_ordinate_of_height {γ δ : ℝ}
    (h : Real.exp γ = Real.exp δ) : γ = δ :=
  resonanceHeight_injective h

/-- **The height law itself is faithful**: distinct positive integer slots sit at distinct heights
(`z_n = n`), so reading a height back to its integer slot loses nothing. -/
theorem heightLaw_injective {m n : ℕ} (h : heightLaw m = heightLaw n) : m = n := by
  unfold heightLaw at h; exact_mod_cast h

/-- **Contrast: the imaginary phasor `y ↦ e^{iy}` is NOT injective** (it is `2π`-periodic), so an
`e^{iy}` height would lose information — exactly the branch/winding problem the *real* height law
`z = e^γ` avoids. -/
theorem imaginaryPhasor_not_injective :
    ¬ Function.Injective (fun y : ℝ => Complex.exp (Complex.I * y)) := by
  intro hinj
  have h2 : Complex.exp (Complex.I * (2 * Real.pi : ℝ)) = 1 := by
    rw [mul_comm]; push_cast; exact Complex.exp_two_pi_mul_I
  have h0 : Complex.exp (Complex.I * (0 : ℝ)) = 1 := by simp
  have h : Complex.exp (Complex.I * (0 : ℝ)) = Complex.exp (Complex.I * (2 * Real.pi : ℝ)) := by
    rw [h0, h2]
  have hcon := hinj h
  exact (mul_ne_zero two_ne_zero Real.pi_ne_zero) hcon.symm

/-! ## 5. Completeness of the encoding: the on-line zeros are exhausted, none invented

The height encoding `gamma |-> e^gamma` (`resonanceHeightEquiv`) is combined with the
*definitional* zero-set identity `CarrierZeros_eq` to record the precise completeness statement:
every on-line zero ordinate is represented by a unique cancellation height, and every cancellation
height comes from exactly one genuine on-line zero.  This is a statement about the *encoding*
of the on-line zeros that exist; it says nothing about whether all nontrivial zeros lie on the
line (that is the Riemann hypothesis, which this project deliberately leaves open). -/

/-- **The on-line zero ordinates are exactly the carrier zeros.**  This is the definitional
zero-set identity `CriticalLinePhasor.EtaTrivial.CarrierZeros_eq` read as "no spurious, no missing"
cancellations: the carrier vanishes exactly on the critical-line zeros of `zeta`. -/
theorem online_zero_eq_carrierZeros :
    {gamma : ℝ | riemannZeta ((1 / 2 : ℂ) + (gamma : ℂ) * Complex.I) = 0}
      = CriticalLinePhasor.EtaTrivial.CarrierZeros :=
  (CriticalLinePhasor.EtaTrivial.CarrierZeros_eq).symm

/-- **Completeness of the height encoding (the exhaustion bijection).**  Transporting the
on-line-zero predicate along the branch-free bijection `resonanceHeightEquiv` (`gamma |-> e^gamma`,
inverse `log`) gives an `Equiv` between the on-line zero ordinates and the positive cancellation
heights `z > 0` whose recovered ordinate `log z` is again an on-line zero.  No on-line zero is
missed (every ordinate maps to a height) and none is invented (every such height comes from an
ordinate, recovered uniquely as `gamma = log z`).  This says nothing about RH: it quantifies only
over the on-line zeros that exist. -/
noncomputable def online_zeros_exhausted :
    {gamma : ℝ // riemannZeta ((1 / 2 : ℂ) + (gamma : ℂ) * Complex.I) = 0} ≃
      {z : ℝ // 0 < z ∧
        riemannZeta ((1 / 2 : ℂ) + ((Real.log z : ℝ) : ℂ) * Complex.I) = 0} :=
  (Equiv.subtypeEquiv resonanceHeightEquiv (fun gamma => by
      simp only [resonanceHeightEquiv, Equiv.coe_fn_mk, Real.log_exp])).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun z : ℝ => 0 < z)
      (fun z : ℝ => riemannZeta ((1 / 2 : ℂ) + ((Real.log z : ℝ) : ℂ) * Complex.I) = 0))

/-- **Each on-line zero ordinate has exactly one cancellation height.**  For every ordinate
`gamma` with `zeta(1/2 + i gamma) = 0`, there is a unique height `z`, namely `z = e^gamma`, which is
positive and whose recovered ordinate `log z` is again an on-line zero.  Uniqueness is forced
because `e^gamma` pins `z` down; the on-line-zero hypothesis is what makes the height a genuine
cancellation height. -/
theorem online_zero_unique_height (gamma : ℝ)
    (h : riemannZeta ((1 / 2 : ℂ) + (gamma : ℂ) * Complex.I) = 0) :
    ∃! z : ℝ, 0 < z ∧ Real.exp gamma = z ∧
      riemannZeta ((1 / 2 : ℂ) + ((Real.log z : ℝ) : ℂ) * Complex.I) = 0 := by
  refine ⟨Real.exp gamma, ⟨Real.exp_pos gamma, rfl, ?_⟩, ?_⟩
  · rw [Real.log_exp]; exact h
  · rintro z ⟨_, hz, _⟩; exact hz.symm

end CriticalLinePhasor.Geometry
