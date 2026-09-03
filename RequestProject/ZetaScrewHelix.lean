import RequestProject.HilbertPolyaResolventTrace

/-!
# The zero-side screw function and the helix through the origin (Track E1)

Suzuki (arXiv:2206.03682, Thm 1.1) proves unconditionally that the explicit prime-side
function `Ψ(t)` equals `Σ_γ (1 − cos γt)/γ²` over the zeros of `ξ(½ − iz)` with multiplicity,
and (Krein) that `−Ψ(|t|)` is a screw function — the chordal profile of a helix in a Hilbert
space — exactly when RH holds.  This file compiles the zero side in the house coordinates:

* `screwTerm t ρ = m_ρ (1 − e^{i t_ρ t})/t_ρ²`, `t_ρ = spectralCoord ρ = −i(ρ − ½)`;
  `zetaScrew t = Σ' screwTerm t ρ` over the compiled zero subtype, summable at every `t`
  from the compiled counting majorant `ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros`
  and the strip bound `|Im t_ρ| < ½` (`screwTerm_summable`).
* `helixVec t ρ = √m_ρ (e^{i t_ρ t} − 1)/t_ρ` — one circle per zero, radius `1/t_ρ`, angular
  speed `t_ρ`, through the origin at `t = 0`; the conjugate zero gives the anti-helix.
* `helix_chordal_term_online`: for an on-line zero the squared chord equals `2 Re screwTerm`.
* `helix_chordal_profile_of_online`: **if every zero is on the line, the helix
  `t ↦ (helixVec t ρ)_ρ ∈ ℓ²(Zeros)` has chordal profile `2 Re zetaScrew(t − u)`**, its
  profile the explicit prime-side kinked ramp by Suzuki's identity.  This ℓ²(Zeros) helix is
  indexed by the zeros: it is the spectral shadow of the carrier, not the carrier (whose
  state space is `CarrierThreeDMode`, indexed by height) — RH_LEDGER 529 retracts the earlier
  identification of it with the house double-ended helix.

The converse (an off-line zero makes the screw kernel indefinite) is the Krein/Hilbert
dichotomy of `FoliatedPolarization` and Suzuki's Thm 1.2 of [13]; not compiled here.
No `sorry`, no `axiom`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.HilbertPolya

open CriticalLinePhasor.StBridge

/-- The compiled zero subtype. -/
abbrev Zeros := {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}

/-- The spectral coordinate's imaginary part is `½ − Re ρ`. -/
theorem spectralCoord_im' (ρ : ℂ) : (spectralCoord ρ).im = 1 / 2 - ρ.re := by
  unfold spectralCoord
  simp [Complex.mul_im, Complex.sub_re]

/-- In the strip the spectral coordinate has `|Im| < ½`. -/
theorem spectralCoord_im_abs_lt_half {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    |(spectralCoord ρ).im| < 1 / 2 := by
  rw [spectralCoord_im']
  have h1 : 0 < ρ.re := hρ.1
  have h2 : ρ.re < 1 := hρ.2.1
  rw [abs_lt]
  constructor <;> linarith

/-- The zero-side phasor is bounded by `e^{|t|/2}` on the strip. -/
theorem screwPhasor_norm_le {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) (t : ℝ) :
    ‖Complex.exp (Complex.I * spectralCoord ρ * t)‖ ≤ Real.exp (|t| / 2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (Complex.I * spectralCoord ρ * (t : ℂ)).re = -((spectralCoord ρ).im * t) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  have h := spectralCoord_im_abs_lt_half hρ
  have hprod : |(spectralCoord ρ).im * t| ≤ |t| / 2 := by
    rw [abs_mul]
    have := mul_le_mul_of_nonneg_right h.le (abs_nonneg t)
    linarith
  linarith [neg_le_abs ((spectralCoord ρ).im * t)]

/-- Far out, the spectral coordinate is at least half the modulus of the zero. -/
theorem spectralCoord_norm_ge {ρ : ℂ} (h : 1 ≤ ‖ρ‖) : ‖ρ‖ / 2 ≤ ‖spectralCoord ρ‖ := by
  unfold spectralCoord
  rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
  have h12 : ‖((1 : ℂ) / 2)‖ = 1 / 2 := by norm_num
  have := norm_sub_norm_le ρ ((1 : ℂ) / 2)
  linarith

/-- **The zero-side screw term**: `m_ρ (1 − e^{i t_ρ t})/t_ρ²`. -/
def screwTerm (t : ℝ) (ρ : Zeros) : ℂ :=
  (ZD.xiOrderNat ρ.val : ℂ) * (1 - Complex.exp (Complex.I * spectralCoord ρ.val * t))
    / (spectralCoord ρ.val) ^ 2

/-- **Summability at every `t`**, from the compiled counting majorant. -/
theorem screwTerm_summable (t : ℝ) : Summable (screwTerm t) := by
  have hg : Summable (fun ρ : Zeros =>
      (4 * (1 + Real.exp (|t| / 2))) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2)) :=
    (ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros).mul_left _
  apply Summable.of_norm_bounded_eventually hg
  filter_upwards [eventually_cofinite_norm_ge 1] with ρ hbig
  have hsc := spectralCoord_norm_ge hbig
  have hsc0 : 0 < ‖spectralCoord ρ.val‖ := by linarith
  have hm : (0 : ℝ) ≤ (ZD.xiOrderNat ρ.val : ℝ) := Nat.cast_nonneg _
  have hnum : ‖(1 : ℂ) - Complex.exp (Complex.I * spectralCoord ρ.val * t)‖
      ≤ 1 + Real.exp (|t| / 2) := by
    calc ‖(1 : ℂ) - Complex.exp (Complex.I * spectralCoord ρ.val * t)‖
        ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (Complex.I * spectralCoord ρ.val * t)‖ := norm_sub_le _ _
      _ ≤ 1 + Real.exp (|t| / 2) := by
          rw [norm_one]
          linarith [screwPhasor_norm_le ρ.2 t]
  unfold screwTerm
  rw [norm_div, norm_mul, Complex.norm_natCast, norm_pow]
  rw [div_le_iff₀ (pow_pos hsc0 2)]
  have h4 : ‖ρ.val‖ ^ 2 / 4 ≤ ‖spectralCoord ρ.val‖ ^ 2 := by
    nlinarith [hsc, norm_nonneg ρ.val]
  have hpos : 0 < ‖ρ.val‖ := by linarith
  calc (ZD.xiOrderNat ρ.val : ℝ) * ‖(1 : ℂ) - Complex.exp (Complex.I * spectralCoord ρ.val * t)‖
      ≤ (ZD.xiOrderNat ρ.val : ℝ) * (1 + Real.exp (|t| / 2)) :=
        mul_le_mul_of_nonneg_left hnum hm
    _ = (4 * (1 + Real.exp (|t| / 2))) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2)
          * (‖ρ.val‖ ^ 2 / 4) := by
        field_simp
    _ ≤ (4 * (1 + Real.exp (|t| / 2))) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2)
          * ‖spectralCoord ρ.val‖ ^ 2 := by
        gcongr

/-- **The zero-side screw function** `Ψ(t) = Σ_ρ m_ρ (1 − e^{i t_ρ t})/t_ρ²`. -/
def zetaScrew (t : ℝ) : ℂ := ∑' ρ : Zeros, screwTerm t ρ

/-- **The helix vector of a zero**: `√m_ρ (e^{i t_ρ t} − 1)/t_ρ` — a circle of radius `1/t_ρ`
traversed at angular speed `t_ρ`, through the origin at `t = 0`. -/
def helixVec (t : ℝ) (ρ : Zeros) : ℂ :=
  (Real.sqrt (ZD.xiOrderNat ρ.val : ℝ) : ℂ)
    * (Complex.exp (Complex.I * spectralCoord ρ.val * t) - 1) / spectralCoord ρ.val

/-- Squared chord of a unit circular motion: `|e^{iax} − 1|² = 2 − 2 cos(ax)`. -/
theorem normSq_exp_sub_one (a x : ℝ) :
    Complex.normSq (Complex.exp (Complex.I * (a : ℂ) * (x : ℂ)) - 1) = 2 - 2 * Real.cos (a * x) := by
  have hre : (Complex.I * (a : ℂ) * (x : ℂ)).re = 0 := by simp [Complex.mul_re, Complex.mul_im]
  have him : (Complex.I * (a : ℂ) * (x : ℂ)).im = a * x := by simp [Complex.mul_re, Complex.mul_im]
  rw [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.exp_re, Complex.exp_im, hre, him]
  simp only [Real.exp_zero, one_mul, Complex.one_re, Complex.one_im, sub_zero]
  nlinarith [Real.sin_sq_add_cos_sq (a * x)]

/-- A unit circular phasor has `normSq = 1`. -/
theorem normSq_exp_I_real (a u : ℝ) :
    Complex.normSq (Complex.exp (Complex.I * (a : ℂ) * (u : ℂ))) = 1 := by
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp]
  have hre : (Complex.I * (a : ℂ) * (u : ℂ)).re = 0 := by simp [Complex.mul_re, Complex.mul_im]
  rw [hre, Real.exp_zero, one_pow]

/-- **On-line chord = twice the real part of the screw term.**  For a zero on the critical
line the squared chord of its helix circle between times `t` and `u` is `2 Re screwTerm (t−u)`. -/
theorem helix_chordal_term_online {ρ : Zeros} (hre : ρ.val.re = 1 / 2) (t u : ℝ) :
    Complex.normSq (helixVec t ρ - helixVec u ρ) = 2 * (screwTerm (t - u) ρ).re := by
  set a : ℝ := (spectralCoord ρ.val).re with ha
  have him : (spectralCoord ρ.val).im = 0 := by rw [spectralCoord_im', hre]; ring
  have hsc : spectralCoord ρ.val = (a : ℂ) := by
    apply Complex.ext
    · simp [ha]
    · simp [him]
  set m : ℝ := (ZD.xiOrderNat ρ.val : ℝ) with hm
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  -- the two phasors
  have hsplit : Complex.exp (Complex.I * (a : ℂ) * (t : ℂ))
      = Complex.exp (Complex.I * (a : ℂ) * (u : ℂ)) * Complex.exp (Complex.I * (a : ℂ) * ((t - u : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- left side
  have hL : helixVec t ρ - helixVec u ρ
      = (Real.sqrt m : ℂ) * (Complex.exp (Complex.I * (a : ℂ) * (u : ℂ))
          * (Complex.exp (Complex.I * (a : ℂ) * ((t - u : ℝ) : ℂ)) - 1)) / (a : ℂ) := by
    unfold helixVec
    rw [hsc, hm, hsplit]
    ring
  rw [hL, Complex.normSq_div, Complex.normSq_mul, Complex.normSq_mul, normSq_exp_I_real,
    normSq_exp_sub_one, Complex.normSq_ofReal, Complex.normSq_ofReal,
    Real.mul_self_sqrt hm0]
  -- right side
  unfold screwTerm
  rw [hsc]
  have hr : (((ZD.xiOrderNat ρ.val : ℕ) : ℂ)
        * (1 - Complex.exp (Complex.I * (a : ℂ) * ((t - u : ℝ) : ℂ))) / ((a : ℂ) ^ 2)).re
      = m * (1 - Real.cos (a * (t - u))) / (a * a) := by
    have hre2 : (Complex.I * (a : ℂ) * ((t - u : ℝ) : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    have him2 : (Complex.I * (a : ℂ) * ((t - u : ℝ) : ℂ)).im = a * (t - u) := by
      simp [Complex.mul_re, Complex.mul_im]
    have hpow : ((a : ℂ) ^ 2) = (((a * a : ℝ)) : ℂ) := by push_cast; ring
    rw [hpow, Complex.div_ofReal_re, ← Complex.ofReal_natCast, Complex.re_ofReal_mul,
      Complex.sub_re, Complex.one_re, Complex.exp_re, hre2, him2, Real.exp_zero, one_mul]
  rw [hr]
  ring

/-- **The helix through the origin has chordal profile `2 Re Ψ`, given every zero on the
line.**  The zero-side helix `t ↦ (helixVec t ρ)_ρ ∈ ℓ²(Zeros)` — one circle per zero, radius
`1/t_ρ`, speed `t_ρ`, conjugate zeros the anti-helix — has squared chord between times `t`
and `u` equal to `2 Re zetaScrew (t − u)`; by Suzuki's Thm 1.1 that is the explicit
prime-side kinked ramp.  This is the on-line (Hilbert-space) branch of the Krein/Hilbert
dichotomy of `FoliatedPolarization`. -/
theorem helix_chordal_profile_of_online (hRH : ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2)
    (t u : ℝ) :
    ∑' ρ : Zeros, Complex.normSq (helixVec t ρ - helixVec u ρ) = 2 * (zetaScrew (t - u)).re := by
  unfold zetaScrew
  rw [Complex.re_tsum (screwTerm_summable (t - u)), ← tsum_mul_left]
  exact tsum_congr (fun ρ => helix_chordal_term_online (hRH ρ.val ρ.2) t u)

end CriticalLinePhasor.HilbertPolya

#print axioms CriticalLinePhasor.HilbertPolya.screwTerm_summable
#print axioms CriticalLinePhasor.HilbertPolya.helix_chordal_term_online
#print axioms CriticalLinePhasor.HilbertPolya.helix_chordal_profile_of_online
