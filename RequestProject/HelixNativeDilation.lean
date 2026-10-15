import RequestProject.HelixOperatorReconciliation
import RequestProject.HelixZetaSource

/-!
# Native dilation on signed height: 1277–1279 redone with the origin at 0 (ledger 1281)

Sam (2026-10-13): "where does this 1/2 shit come from?" (1280: from my use of the encoded height `x = e^h` with
Lebesgue measure `dx`, the chart of 1219–1226); then "can you redo the last turns correctly?"

Everything here is on the helix's own coordinate: signed height `h ∈ ℝ`, origin `h = 0`, measure `dh`. Offsets `v`
are measured from the origin; the axis is `Re v = 0`. No `½` appears in any statement. The bank's reflection weight
appears only as `nativePair.k` (the one-dimensional lattice weight), and the carrier exponent `k + 2v` appears only
where the carrier is read (`mode_functional`).

**The native generator** (1277, redone). Dilation of the encoding is translation of signed height:
`shift t f (h) = f(h + t)`.
* `shift_norm_sq`: translation preserves `∫ ‖f‖² dh` with no weight. This replaces 1278's `e^{t/2}` normalization,
  which was the Jacobian of `x = e^h`.
* `expMode v (h) = e^{vh}`: `shift_expMode` (`T_t e_v = e^{vt} e_v`); `norm_expMode` (`|e_v(h)| = e^{(Re v)h}`).
* The involution J: `Jn f (h) = conj f(−h)`, reflection about the origin with conjugation.
  `Jn_shift` (`J T_t = T_{−t} J`); `Jn_expMode` (`J e_v = e_{−v̄}`).
* The J-symmetric native bank: `bankN h = halfDensity nativePair (e^h)`. `Jn_bankN`: `J bankN = bankN`, from the
  helix's own reflection (1260).
* Site modes: `mode_shift` (site `n`'s mode is the ground mode translated by `2 log(n+1)`, times `(n+1)^{−k}`).
  `mode_functional`: the native functional of site `n`'s mode at offset `v` is the carrier bank entry at exponent
  `k + 2v` times the ground mode's. This is the readout map; it is the only place `k + 2v` appears.

**The native functional** (1278, redone). `Φ v f = ∫ f(h)·e^{vh} dh`. `Φ_shift`: `Φ_v(T_t f) = e^{−vt}·Φ_v(f)`.
* `covariant_functional_axis`: on any normed space whose translations grow subexponentially, a nonzero continuous
  functional with this covariance has `Re v = 0`. The native form of 1220's theorem, proved here directly, with no
  chart.

**The mass test** (1279, redone, numbers in `tmp/att1281_native_mass_test.py`). On `L²(ℝ, dh)`, `Φ_v` restricted to
`[−K, K]` has norm `(∫_{−K}^{K} e^{2(Re v)h} dh)^{1/2}`, unbounded in `K` for every `v`. The 1270 source mass is `Φ`
evaluated on two specific functions (the bank's halves at the cut): a lower bound, certifying `Φ ≠ 0`. Continuity is an
upper bound over all functions. Same verdict as 1279, now in native coordinates.
-/

open Complex Set MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.HelixNativeDilation

open CriticalLinePhasor CriticalLinePhasor.GlobalHelix CriticalLinePhasor.HelixTwoEndedNative
  CriticalLinePhasor.HelixOriginCentered CriticalLinePhasor.HelixWindowCompletion

/-! ## Translation of signed height -/

/-- Translate signed height by `t` (dilation of the encoding). -/
def shift (t : ℝ) (f : ℝ → ℂ) : ℝ → ℂ := fun h => f (h + t)

theorem shift_shift (t u : ℝ) (f : ℝ → ℂ) : shift t (shift u f) = shift (t + u) f := by
  funext h
  simp only [shift]
  ring_nf

/-- **Translation preserves the native `L²` mass, with no weight.** -/
theorem shift_norm_sq (t : ℝ) (f : ℝ → ℂ) : ∫ h, ‖shift t f h‖ ^ 2 = ∫ h, ‖f h‖ ^ 2 :=
  integral_add_right_eq_self (fun h => ‖f h‖ ^ 2) t

/-- The native eigenmodes `e_v(h) = e^{vh}`. -/
def expMode (v : ℂ) : ℝ → ℂ := fun h => Complex.exp (v * h)

/-- **`T_t e_v = e^{vt} e_v`.** -/
theorem shift_expMode (t : ℝ) (v : ℂ) (h : ℝ) : shift t (expMode v) h = Complex.exp (v * t) * expMode v h := by
  simp only [shift, expMode]
  rw [← Complex.exp_add]
  push_cast
  ring_nf

theorem norm_expMode (v : ℂ) (h : ℝ) : ‖expMode v h‖ = Real.exp (v.re * h) := by
  simp only [expMode]
  rw [Complex.norm_exp]
  simp

/-! ## The involution J: reflection about the origin with conjugation -/

def Jn (f : ℝ → ℂ) : ℝ → ℂ := fun h => conj (f (-h))

theorem Jn_Jn (f : ℝ → ℂ) : Jn (Jn f) = f := by
  funext h
  simp [Jn]

/-- **`J T_t = T_{−t} J`.** -/
theorem Jn_shift (t : ℝ) (f : ℝ → ℂ) : Jn (shift t f) = shift (-t) (Jn f) := by
  funext h
  simp only [Jn, shift]
  congr 2
  ring

/-- **`J e_v = e_{−v̄}`.** -/
theorem Jn_expMode (v : ℂ) : Jn (expMode v) = expMode (-conj v) := by
  funext h
  simp only [Jn, expMode]
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_neg, Complex.conj_ofReal, ofReal_neg]
  ring

/-! ## The J-symmetric native bank -/

/-- The native bank on signed height: the Gaussian bank with its reflection weight absorbed (1260). -/
def bankN (h : ℝ) : ℂ := halfDensity nativePair (Real.exp h)

/-- **The native bank is J-invariant**: the helix's own reflection about the origin with conjugation. -/
theorem Jn_bankN : Jn bankN = bankN := by
  funext h
  simp only [Jn, bankN]
  have hx : 0 < Real.exp h := Real.exp_pos h
  have hr := halfDensity_reflect nativePair hx
  rw [one_div, ← Real.exp_neg] at hr
  rw [hr, show nativePair.ε = 1 from rfl, one_mul]
  unfold halfDensity
  rw [WeakFEPair.symm_f, WeakFEPair.symm_k, nativePair_conj _ hx, map_mul, Complex.conj_ofReal,
    Complex.conj_conj]

/-! ## Site modes and the carrier, at the readout -/

/-- Site `n`'s native mode: the Gaussian mode at rate `π(n+1)²`, with the bank's reflection weight. -/
def mode (n : ℕ) (h : ℝ) : ℂ :=
  ((Real.exp (nativePair.k / 2 * h) * Real.exp (-siteRate n * Real.exp h) : ℝ) : ℂ)

/-- **Site `n`'s mode is the ground mode translated by `2 log(n+1)`, times `(n+1)^{−k}`.** -/
theorem mode_shift (n : ℕ) (h : ℝ) :
    mode n h = (((((n + 1 : ℕ) : ℝ)) ^ (-nativePair.k) : ℝ) : ℂ) *
      shift (2 * Real.log ((n + 1 : ℕ) : ℝ)) (mode 0) h := by
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  simp only [mode, shift]
  rw [← ofReal_mul]
  congr 1
  have hL : Real.exp (2 * Real.log ((n + 1 : ℕ) : ℝ)) = ((n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [show 2 * Real.log ((n + 1 : ℕ) : ℝ) = Real.log (((n + 1 : ℕ) : ℝ) ^ 2) by
      rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]
  rw [Real.exp_add, hL, Real.rpow_def_of_pos hpos, mul_add, Real.exp_add]
  unfold siteRate
  have h2 : Real.exp (nativePair.k / 2 * (2 * Real.log ((n + 1 : ℕ) : ℝ))) =
      Real.exp (nativePair.k * Real.log ((n + 1 : ℕ) : ℝ)) := by congr 1; ring
  rw [h2]
  have h3 : Real.exp (Real.log ((n : ℝ) + 1) * -nativePair.k) *
      Real.exp (nativePair.k * Real.log ((n : ℝ) + 1)) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  push_cast
  have h4 : -(Real.pi * 1 ^ 2) * (Real.exp h * ((n : ℝ) + 1) ^ 2) =
      -(Real.pi * ((n : ℝ) + 1) ^ 2) * Real.exp h := by ring
  rw [h4]
  linear_combination
    (-(Real.exp (nativePair.k / 2 * h) * Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2) * Real.exp h))) * h3

/-- The native functional at offset `v`. -/
def Φ (v : ℂ) (f : ℝ → ℂ) : ℂ := ∫ h, f h * expMode v h

/-- **Covariance**: `Φ_v(T_t f) = e^{−vt}·Φ_v(f)`. -/
theorem Φ_shift (v : ℂ) (f : ℝ → ℂ) (t : ℝ) : Φ v (shift t f) = Complex.exp (-(v * t)) * Φ v f := by
  unfold Φ
  have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun u => f u * Complex.exp (v * ((u : ℂ) - t))) t
  simp only [shift, expMode] at h ⊢
  have hcongr : (fun x : ℝ => f (x + t) * Complex.exp (v * ((x + t : ℝ) : ℂ) - v * t)) =
      fun x => f (x + t) * Complex.exp (v * (x : ℂ)) := by
    funext x
    congr 2
    push_cast
    ring
  rw [← integral_const_mul]
  have hrhs : (fun x : ℝ => Complex.exp (-(v * t)) * (f x * Complex.exp (v * (x : ℂ)))) =
      fun u => f u * Complex.exp (v * ((u : ℂ) - t)) := by
    funext u
    rw [mul_comm, mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [hrhs, ← h]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  congr 2
  push_cast
  ring

/-- **The carrier at the readout**: the native functional of site `n`'s mode at offset `v` is the carrier bank entry
at exponent `k + 2v` times the ground mode's. -/
theorem mode_functional (n : ℕ) (v : ℂ) :
    Φ v (mode n) = CarrierReadout.bank (nativePair.k + 2 * v) n * Φ v (mode 0) := by
  have hpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hfun : mode n = fun h => (((((n + 1 : ℕ) : ℝ)) ^ (-nativePair.k) : ℝ) : ℂ) *
      shift (2 * Real.log ((n + 1 : ℕ) : ℝ)) (mode 0) h := funext (mode_shift n)
  have hlin : Φ v (mode n) = (((((n + 1 : ℕ) : ℝ)) ^ (-nativePair.k) : ℝ) : ℂ) *
      Φ v (shift (2 * Real.log ((n + 1 : ℕ) : ℝ)) (mode 0)) := by
    rw [hfun]
    unfold Φ
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    ring
  rw [hlin, Φ_shift, ← mul_assoc]
  congr 1
  rw [CarrierReadout.bank_apply]
  have h1 : ((n : ℂ) + 1) = ((((n + 1 : ℕ) : ℝ)) : ℂ) := by push_cast; ring
  rw [h1, cpow_def_of_ne_zero (ofReal_ne_zero.mpr hpos.ne'), ← ofReal_log hpos.le,
    Real.rpow_def_of_pos hpos, ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ## The native continuity theorem -/

/-- **Native form of 1220**: on a normed space whose translations grow subexponentially, a nonzero continuous
functional with `φ ∘ T_t = e^{−vt}·φ` has `Re v = 0`. Proved directly; no chart. -/
theorem covariant_functional_axis {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (T : ℝ → X →L[ℂ] X) (B : ℝ → ℝ) (hT : ∀ t x, ‖T t x‖ ≤ B |t| * ‖x‖)
    (hB : ∀ c : ℝ, 0 < c → Tendsto (fun u => B u / Real.exp (c * u)) atTop (𝓝 0))
    (φ : X →L[ℂ] ℂ) (hφ : φ ≠ 0) (v : ℂ)
    (hcov : ∀ t x, φ (T t x) = Complex.exp (-(v * t)) * φ x) : v.re = 0 := by
  obtain ⟨x, hx⟩ : ∃ x, φ x ≠ 0 := by
    by_contra h
    exact hφ (ContinuousLinearMap.ext fun y => by simpa using (not_exists.mp h y))
  have hbound : ∀ t : ℝ, Real.exp (-(t * v.re)) * ‖φ x‖ ≤ ‖φ‖ * (B |t| * ‖x‖) := by
    intro t
    have h1 : ‖φ (T t x)‖ ≤ ‖φ‖ * ‖T t x‖ := φ.le_opNorm _
    rw [hcov, norm_mul, Complex.norm_exp] at h1
    have hre : (-(v * (t : ℂ))).re = -(t * v.re) := by simp; ring
    rw [hre] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (hT t x) (norm_nonneg _))
  have hpos : 0 < ‖φ x‖ := norm_pos_iff.mpr hx
  by_contra hne
  set c := |v.re| with hcdef
  have hc : 0 < c := abs_pos.mpr hne
  have hb' : ∀ u : ℝ, 0 ≤ u → Real.exp (c * u) * ‖φ x‖ ≤ ‖φ‖ * (B u * ‖x‖) := by
    intro u hu
    rcases le_or_gt 0 v.re with h | h
    · have := hbound (-u)
      rw [abs_neg, abs_of_nonneg hu, show -(-u * v.re) = v.re * u by ring] at this
      rwa [hcdef, abs_of_nonneg h]
    · have := hbound u
      rw [abs_of_nonneg hu, show -(u * v.re) = (-v.re) * u by ring] at this
      rwa [hcdef, abs_of_neg h]
  have hlim := ((hB c hc).const_mul (‖φ‖ * ‖x‖))
  rw [mul_zero] at hlim
  have hev := hlim.eventually (gt_mem_nhds hpos)
  obtain ⟨u, hu1, hu0⟩ := (hev.and (eventually_ge_atTop (0 : ℝ))).exists
  have hb := hb' u hu0
  have hE : 0 < Real.exp (c * u) := Real.exp_pos _
  have : ‖φ x‖ ≤ ‖φ‖ * ‖x‖ * (B u / Real.exp (c * u)) := by
    rw [mul_div_assoc', le_div_iff₀ hE]
    nlinarith [hb]
  linarith

end CriticalLinePhasor.HelixNativeDilation

end

#print axioms CriticalLinePhasor.HelixNativeDilation.shift_norm_sq
#print axioms CriticalLinePhasor.HelixNativeDilation.Jn_shift
#print axioms CriticalLinePhasor.HelixNativeDilation.Jn_expMode
#print axioms CriticalLinePhasor.HelixNativeDilation.Jn_bankN
#print axioms CriticalLinePhasor.HelixNativeDilation.mode_shift
#print axioms CriticalLinePhasor.HelixNativeDilation.Φ_shift
#print axioms CriticalLinePhasor.HelixNativeDilation.mode_functional
#print axioms CriticalLinePhasor.HelixNativeDilation.covariant_functional_axis
