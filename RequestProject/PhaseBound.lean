import RequestProject.GrowthDisplacementLaw

/-!
# The phase bound `|Φ| < π/2` (ledger 651), compiled without `arg`

The growth-displacement direction at a simple on-line zero is (ledger 652, `growth_direction_eta`)
`η(ρ−2)/η′(ρ) = B·P·(ζ(ρ+2)/ζ′(ρ))‾`, with `B = (1−2^{3−ρ})/(1−2^{1−ρ})`, `P = (1−ρ)(2−ρ)/(4π²) = −q/(4π²)`,
`q = (γ²−¾) + 2iγ`.  The registration phase lives in `ζ′(ρ)‾`; the bounded phase `Φ` is the argument of
`B · q · ζ(ρ+2)‾`, and `|Φ| < π/2` is exactly `0 < Re(B · q · ζ(ρ+2)‾)`.

Sectors replace `arg`: `InSector c z` means `0 < Re z ∧ |Im z| ≤ c·Re z` (`|arg z| ≤ arctan c`), and sectors
multiply by the tangent-addition rule.  Three prongs:
* the conduction clock: `w = 2^{1−ρ}` lies on the circle `|w| = √2`, and `(1−4w)(1−w)‾ = (9−5x) − 3iy`
  lies in the sector `c = 4/5` by Cauchy–Schwarz (`(3|y| + 4x)² ≤ 25·2 < (36/5)²`);
* the quadratic: `q = (γ²−¾) + 2iγ` lies in the sector `c = 3/20` once `|γ| ≥ 14`;
* the Euler product (the fiber's own object): `ζ(s) = exp Σ_p −log(1 − p^{−s})` on `Re s = 5/2`, and the
  imaginary part of the sum is at most `0.79·Σ_{n≥2} n^{−2} = 0.79(π²/6 − 1) < 0.51`, so `ζ(s)` lies in
  the sector `c = 0.59`.
-/

open Complex Real Filter Topology
open CriticalLinePhasor.EtaTrivial CriticalLinePhasor.GrowthDisplacement

namespace CriticalLinePhasor.PhaseBound

/-- The closed sector `|arg z| ≤ arctan c` (for `c ≥ 0`), stated without `arg`. -/
def InSector (c : ℝ) (z : ℂ) : Prop := 0 < z.re ∧ |z.im| ≤ c * z.re

theorem InSector.re_pos {c : ℝ} {z : ℂ} (h : InSector c z) : 0 < z.re := h.1

theorem InSector.mono {c c' : ℝ} {z : ℂ} (h : InSector c z) (hc : c ≤ c') : InSector c' z :=
  ⟨h.1, h.2.trans (by gcongr; exact h.1.le)⟩

theorem InSector.conj {c : ℝ} {z : ℂ} (h : InSector c z) : InSector c ((starRingEnd ℂ) z) := by
  refine ⟨by simpa using h.1, ?_⟩
  simpa [abs_neg] using h.2

theorem InSector.mul_ofReal_pos {c : ℝ} {z : ℂ} (h : InSector c z) {r : ℝ} (hr : 0 < r) :
    InSector c (z * (r : ℂ)) := by
  have hre : (z * (r : ℂ)).re = z.re * r := by
    simp [Complex.mul_re]
  have him : (z * (r : ℂ)).im = z.im * r := by
    simp [Complex.mul_im]
  refine ⟨?_, ?_⟩
  · rw [hre]; exact mul_pos h.1 hr
  · rw [hre, him, abs_mul, abs_of_pos hr]
    calc |z.im| * r ≤ (c * z.re) * r := by gcongr; exact h.2
      _ = c * (z.re * r) := by ring

/-- Tangent addition: sectors multiply. -/
theorem InSector.mul {a b : ℝ} {z w : ℂ} (hz : InSector a z) (hw : InSector b w)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a * b < 1) :
    InSector ((a + b) / (1 - a * b)) (z * w) := by
  obtain ⟨hz1, hz2⟩ := hz
  obtain ⟨hw1, hw2⟩ := hw
  have hre : (z * w).re = z.re * w.re - z.im * w.im := Complex.mul_re z w
  have him : (z * w).im = z.re * w.im + z.im * w.re := Complex.mul_im z w
  have hzi : z.im * w.im ≤ |z.im| * |w.im| := by
    rw [← abs_mul]; exact le_abs_self _
  have hprod : |z.im| * |w.im| ≤ (a * z.re) * (b * w.re) :=
    mul_le_mul hz2 hw2 (abs_nonneg _) (by positivity)
  have h1 : (1 - a * b) * (z.re * w.re) ≤ (z * w).re := by
    rw [hre]; nlinarith
  have hpos : 0 < (1 - a * b) * (z.re * w.re) := by
    have : 0 < 1 - a * b := by linarith
    positivity
  refine ⟨by linarith, ?_⟩
  have habs : |(z * w).im| ≤ z.re * |w.im| + |z.im| * w.re := by
    rw [him]
    calc |z.re * w.im + z.im * w.re| ≤ |z.re * w.im| + |z.im * w.re| := abs_add_le _ _
      _ = z.re * |w.im| + |z.im| * w.re := by
        rw [abs_mul, abs_mul, abs_of_pos hz1, abs_of_pos hw1]
  have hb' : z.re * |w.im| + |z.im| * w.re ≤ (a + b) * (z.re * w.re) := by
    have e1 : z.re * |w.im| ≤ z.re * (b * w.re) := by gcongr
    have e2 : |z.im| * w.re ≤ (a * z.re) * w.re := by gcongr
    nlinarith
  have hc : 0 ≤ (a + b) / (1 - a * b) := by
    apply div_nonneg (by linarith); linarith
  have hne : (1 - a * b) ≠ 0 := ne_of_gt (by linarith)
  calc |(z * w).im| ≤ (a + b) * (z.re * w.re) := habs.trans hb'
    _ = ((a + b) / (1 - a * b)) * ((1 - a * b) * (z.re * w.re)) := by
        rw [show (a + b) / (1 - a * b) * ((1 - a * b) * (z.re * w.re))
            = ((a + b) / (1 - a * b) * (1 - a * b)) * (z.re * w.re) by ring,
          div_mul_cancel₀ _ hne]
    _ ≤ ((a + b) / (1 - a * b)) * (z * w).re := by gcongr

/-! ### Prong 1: the conduction clock on the circle `|w| = √2` -/

/-- `(1 − 4w)·(1 − w)‾` lies in the sector `c = 4/5` when `|w|² = 2`. -/
theorem clock_factor_inSector {w : ℂ} (hw : w.re ^ 2 + w.im ^ 2 = 2) :
    InSector (4 / 5) ((1 - 4 * w) * (starRingEnd ℂ) (1 - w)) := by
  set x := w.re with hx
  set y := w.im with hy
  have hre : ((1 - 4 * w) * (starRingEnd ℂ) (1 - w)).re = 9 - 5 * x := by
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.mul_im, Complex.re_ofNat,
      Complex.im_ofNat, ← hx, ← hy]
    nlinarith [hw]
  have him : ((1 - 4 * w) * (starRingEnd ℂ) (1 - w)).im = -3 * y := by
    simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.mul_im, Complex.re_ofNat,
      Complex.im_ofNat, ← hx, ← hy]
    ring
  have hx2 : x ^ 2 ≤ 2 := by nlinarith [sq_nonneg y]
  have hxb : x < 3 / 2 := by nlinarith
  refine ⟨?_, ?_⟩
  · rw [hre]; linarith
  · rw [hre, him, abs_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 3)]
    have hcs : (3 * |y| + 4 * x) ^ 2 ≤ 50 := by
      nlinarith [sq_nonneg (3 * x - 4 * |y|), sq_abs y, hw]
    nlinarith [abs_nonneg y, sq_nonneg (3 * |y| + 4 * x)]

/-- `2^{1−ρ}` on the line lies on the circle `|w|² = 2`. -/
theorem two_cpow_normSq {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    ((2 : ℂ) ^ (1 - ρ)).re ^ 2 + ((2 : ℂ) ^ (1 - ρ)).im ^ 2 = 2 := by
  have hn : ‖((2 : ℝ) : ℂ) ^ (1 - ρ)‖ = (2 : ℝ) ^ (1 - ρ).re :=
    Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num) _
  simp only [Complex.ofReal_ofNat] at hn
  have hre : (1 - ρ).re = 1 / 2 := by simp [hρ]; norm_num
  rw [hre] at hn
  have h2 : ‖(2 : ℂ) ^ (1 - ρ)‖ ^ 2 = 2 := by
    rw [hn, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by norm_num)]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at h2
  nlinarith [h2]

/-- The conduction-clock factor `B = (1 − 2^{3−ρ})/(1 − 2^{1−ρ})` lies in the sector `c = 4/5`. -/
theorem B_inSector {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    InSector (4 / 5) ((1 - (2 : ℂ) ^ (3 - ρ)) / (1 - (2 : ℂ) ^ (1 - ρ))) := by
  set w := (2 : ℂ) ^ (1 - ρ) with hw
  have h4 : (2 : ℂ) ^ (3 - ρ) = 4 * w := by
    rw [hw, show (3 : ℂ) - ρ = (1 - ρ) + 2 by ring, Complex.cpow_add _ _ two_ne_zero]
    norm_num; ring
  have hw1 : 1 - w ≠ 0 := by
    intro h
    have := two_cpow_normSq hρ
    rw [← hw] at this
    have hw' : w = 1 := by linear_combination -h
    rw [hw'] at this; simp at this
  have hns : 0 < Complex.normSq (1 - w) := Complex.normSq_pos.mpr hw1
  have key : (1 - 4 * w) / (1 - w)
      = (1 - 4 * w) * (starRingEnd ℂ) (1 - w) * (((Complex.normSq (1 - w))⁻¹ : ℝ) : ℂ) := by
    rw [div_eq_mul_inv, Complex.inv_def, mul_assoc]
  rw [h4, key]
  exact (clock_factor_inSector (w := w) (by rw [hw]; exact two_cpow_normSq hρ)).mul_ofReal_pos
    (inv_pos.mpr hns)

/-! ### Prong 2: the quadratic `q = −(1−ρ)(2−ρ) = (γ² − ¾) + 2iγ` -/

theorem q_re {ρ : ℂ} (hρ : ρ.re = 1 / 2) : (-((1 - ρ) * (2 - ρ))).re = ρ.im ^ 2 - 3 / 4 := by
  simp only [Complex.neg_re, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.re_ofNat, Complex.im_ofNat, hρ]
  ring

theorem q_im {ρ : ℂ} (hρ : ρ.re = 1 / 2) : (-((1 - ρ) * (2 - ρ))).im = 2 * ρ.im := by
  simp only [Complex.neg_im, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.re_ofNat, Complex.im_ofNat, hρ]
  ring

/-- For `|γ| ≥ 14` the quadratic lies in the sector `c = 3/20`. -/
theorem q_inSector {ρ : ℂ} (hρ : ρ.re = 1 / 2) (hγ : 14 ≤ |ρ.im|) :
    InSector (3 / 20) (-((1 - ρ) * (2 - ρ))) := by
  rw [InSector, q_re hρ, q_im hρ]
  have hsq : ρ.im ^ 2 = |ρ.im| ^ 2 := (sq_abs _).symm
  rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), hsq]
  constructor <;> nlinarith [hγ]

/-! ### Prong 3: the Euler product on `Re s = 5/2` — the fiber's own object -/

/-- Per prime: `‖log(1 − p^{−s})‖ ≤ 0.79 / p²` on `Re s = 5/2`. -/
theorem prime_log_bound {s : ℂ} (hs : s.re = 5 / 2) (p : Nat.Primes) :
    ‖Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s))‖ ≤ 0.79 / ((p : ℕ) : ℝ) ^ 2 := by
  have hp2 : (2 : ℕ) ≤ (p : ℕ) := p.2.two_le
  have hp2r : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast hp2
  have hp0 : 0 < ((p : ℕ) : ℝ) := by linarith
  have hn : ‖((p : ℕ) : ℂ) ^ (-s)‖ = ((p : ℕ) : ℝ) ^ (-s).re :=
    Complex.norm_natCast_cpow_of_pos p.2.pos _
  have hre : (-s).re = -(5 / 2 : ℝ) := by simp [hs]
  rw [hre] at hn
  set t := ((p : ℕ) : ℝ) ^ (-(5 / 2 : ℝ)) with ht
  have ht_split : t = ((p : ℕ) : ℝ) ^ (-(2 : ℝ)) * ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [ht, ← Real.rpow_add hp0]; norm_num
  have hhalf : ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hp2r (by norm_num)
  have h2half : (2 : ℝ) ^ (-(1 / 2 : ℝ)) ≤ 0.7072 := by
    have hsq : ((2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    have h0 : 0 ≤ (2 : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (by norm_num) _
    nlinarith [hsq, h0]
  have hp2inv : ((p : ℕ) : ℝ) ^ (-(2 : ℝ)) = 1 / ((p : ℕ) : ℝ) ^ 2 := by
    rw [Real.rpow_neg hp0.le, Real.rpow_two]; ring
  have htle : t ≤ 0.7072 / ((p : ℕ) : ℝ) ^ 2 := by
    rw [ht_split, hp2inv]
    calc 1 / ((p : ℕ) : ℝ) ^ 2 * ((p : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))
        ≤ 1 / ((p : ℕ) : ℝ) ^ 2 * 0.7072 := by gcongr; exact hhalf.trans h2half
      _ = 0.7072 / ((p : ℕ) : ℝ) ^ 2 := by ring
  have hp2sq : (4 : ℝ) ≤ ((p : ℕ) : ℝ) ^ 2 := by nlinarith
  have ht_small : t ≤ 0.1768 := by
    calc t ≤ 0.7072 / ((p : ℕ) : ℝ) ^ 2 := htle
      _ ≤ 0.7072 / 4 := by gcongr
      _ = 0.1768 := by norm_num
  have ht_nonneg : 0 ≤ t := Real.rpow_nonneg hp0.le _
  have ht_lt : t < 1 := by linarith
  have hlog := Complex.norm_log_one_add_le (z := -(((p : ℕ) : ℂ) ^ (-s)))
    (by rw [norm_neg, hn]; exact ht_lt)
  rw [norm_neg, hn, show (1 : ℂ) + -(((p : ℕ) : ℂ) ^ (-s)) = 1 - ((p : ℕ) : ℂ) ^ (-s) by ring] at hlog
  have hquad : t ^ 2 * (1 - t)⁻¹ / 2 ≤ 0.11 * t := by
    have h1t : 0 < 1 - t := by linarith
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2), mul_inv_le_iff₀ h1t]
    nlinarith
  calc ‖Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s))‖ ≤ t ^ 2 * (1 - t)⁻¹ / 2 + t := hlog
    _ ≤ 0.11 * t + t := by linarith
    _ = 1.11 * t := by ring
    _ ≤ 1.11 * (0.7072 / ((p : ℕ) : ℝ) ^ 2) := by gcongr
    _ ≤ 0.79 / ((p : ℕ) : ℝ) ^ 2 := by
        rw [← mul_div_assoc]; gcongr; norm_num

/-- `Σ_p 1/p² ≤ π²/6 − 1`: the primes sit inside `n ≥ 2`. -/
theorem primes_inv_sq_le :
    ∑' p : Nat.Primes, (1 : ℝ) / ((p : ℕ) : ℝ) ^ 2 ≤ π ^ 2 / 6 - 1 := by
  set f : ℕ → ℝ := fun n => if n = 1 then 0 else 1 / (n : ℝ) ^ 2 with hf
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n; simp only [hf]; split_ifs <;> positivity
  have hf_le : ∀ n, f n ≤ 1 / (n : ℝ) ^ 2 := by
    intro n; simp only [hf]; split_ifs
    · positivity
    · exact le_rfl
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := hasSum_zeta_two.summable
  have hf_summable : Summable f := Summable.of_nonneg_of_le hf_nonneg hf_le hsum
  have hf_tsum : ∑' n, f n = π ^ 2 / 6 - 1 := by
    have hpt : ∀ n, f n = 1 / (n : ℝ) ^ 2 - (if n = 1 then (1 : ℝ) else 0) := by
      intro n; simp only [hf]; split_ifs with h <;> simp [h]
    rw [tsum_congr hpt, Summable.tsum_sub hsum (hasSum_ite_eq 1 (1 : ℝ)).summable,
      hasSum_zeta_two.tsum_eq, (hasSum_ite_eq 1 (1 : ℝ)).tsum_eq]
  have hprime : ∀ p : Nat.Primes, (1 : ℝ) / ((p : ℕ) : ℝ) ^ 2 = f p := by
    intro p; simp only [hf]; rw [if_neg p.2.one_lt.ne']
  calc ∑' p : Nat.Primes, (1 : ℝ) / ((p : ℕ) : ℝ) ^ 2 = ∑' p : Nat.Primes, f p := tsum_congr hprime
    _ ≤ ∑' n, f n := Summable.tsum_subtype_le f {n | Nat.Prime n} hf_nonneg hf_summable
    _ = π ^ 2 / 6 - 1 := hf_tsum

/-- The imaginary part of `Σ_p −log(1 − p^{−s})` on `Re s = 5/2` is at most `0.52`. -/
theorem euler_log_im_bound {s : ℂ} (hs : s.re = 5 / 2) :
    |(∑' p : Nat.Primes, -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s))).im| ≤ 0.52 := by
  have hmaj : Summable (fun p : Nat.Primes => 0.79 / ((p : ℕ) : ℝ) ^ 2) := by
    have h := hasSum_zeta_two.summable.subtype (fun n : ℕ => Nat.Prime n)
    have h2 : (fun p : Nat.Primes => 0.79 / ((p : ℕ) : ℝ) ^ 2)
        = fun p : Nat.Primes => 0.79 * ((fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) ∘ Subtype.val) p := by
      funext p; simp only [Function.comp]; ring
    rw [h2]; exact h.mul_left _
  have hterm : ∀ p : Nat.Primes,
      ‖-Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s))‖ ≤ 0.79 / ((p : ℕ) : ℝ) ^ 2 := by
    intro p; rw [norm_neg]; exact prime_log_bound hs p
  have hnorm_summable : Summable (fun p : Nat.Primes => ‖-Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hmaj
  have hpi : π < 3.15 := Real.pi_lt_d2
  have hpi0 : 0 < π := Real.pi_pos
  calc |(∑' p : Nat.Primes, -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s))).im|
      ≤ ‖∑' p : Nat.Primes, -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s))‖ := Complex.abs_im_le_norm _
    _ ≤ ∑' p : Nat.Primes, ‖-Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s))‖ :=
        norm_tsum_le_tsum_norm hnorm_summable
    _ ≤ ∑' p : Nat.Primes, 0.79 / ((p : ℕ) : ℝ) ^ 2 :=
        Summable.tsum_le_tsum hterm hnorm_summable hmaj
    _ = 0.79 * ∑' p : Nat.Primes, (1 : ℝ) / ((p : ℕ) : ℝ) ^ 2 := by
        rw [← tsum_mul_left]; congr 1; funext p; ring
    _ ≤ 0.79 * (π ^ 2 / 6 - 1) := by gcongr; exact primes_inv_sq_le
    _ ≤ 0.52 := by nlinarith

/-- **The Euler prong:** on `Re s = 5/2`, `ζ(s)` lies in the sector `c = 0.61`. -/
theorem zeta_inSector {s : ℂ} (hs : s.re = 5 / 2) : InSector 0.61 (riemannZeta s) := by
  have hs1 : 1 < s.re := by rw [hs]; norm_num
  rw [← riemannZeta_eulerProduct_exp_log hs1]
  set L := ∑' p : Nat.Primes, -Complex.log (1 - ((p : ℕ) : ℂ) ^ (-s)) with hL
  have hIm : |L.im| ≤ 0.52 := euler_log_im_bound hs
  have hcos : 0.8648 ≤ Real.cos L.im := by
    have h1 := Real.one_sub_sq_div_two_le_cos (x := L.im)
    have hsq : L.im ^ 2 ≤ 0.52 ^ 2 := by
      rw [← sq_abs]; gcongr
    nlinarith
  have hsin : |Real.sin L.im| ≤ 0.52 := Real.abs_sin_le_abs.trans hIm
  have hexp : 0 < Real.exp L.re := Real.exp_pos _
  refine ⟨?_, ?_⟩
  · rw [Complex.exp_re]; exact mul_pos hexp (by linarith)
  · rw [Complex.exp_re, Complex.exp_im, abs_mul, abs_of_pos hexp]
    calc Real.exp L.re * |Real.sin L.im| ≤ Real.exp L.re * 0.52 := by gcongr
      _ ≤ Real.exp L.re * (0.61 * Real.cos L.im) := by gcongr; linarith
      _ = 0.61 * (Real.exp L.re * Real.cos L.im) := by ring

/-! ### Assembly -/

/-- **The phase bound `|Φ| < π/2`**, stated as `0 < Re(B · q · ζ(ρ+2)‾)` for `ρ` on the line, `|γ| ≥ 14`. -/
theorem phase_bound {ρ : ℂ} (hρ : ρ.re = 1 / 2) (hγ : 14 ≤ |ρ.im|) :
    0 < (((1 - (2 : ℂ) ^ (3 - ρ)) / (1 - (2 : ℂ) ^ (1 - ρ))) * (-((1 - ρ) * (2 - ρ)))
          * (starRingEnd ℂ) (riemannZeta (ρ + 2))).re := by
  have hB := B_inSector hρ
  have hq := q_inSector hρ hγ
  have hz : InSector 0.61 ((starRingEnd ℂ) (riemannZeta (ρ + 2))) :=
    (zeta_inSector (s := ρ + 2) (by simp [hρ]; norm_num)).conj
  have h1 := hB.mul hq (by norm_num) (by norm_num) (by norm_num)
  have h2 := h1.mul hz (by norm_num) (by norm_num) (by norm_num)
  exact h2.re_pos

/-- **The growth displacement points up the carrier.**  For a simple on-line zero with `|γ| ≥ 14`,
`Re( η(ρ−2)/η′(ρ) · ζ′(ρ)‾ ) < 0`: once the registration phase `ζ′(ρ)‾/|ζ′(ρ)| = i·e^{−iπS(γ⁺)}` is
absorbed, the finite-head displacement `Z^{−2}·η(ρ−2)/η′(ρ)` has positive vertical component. -/
theorem growth_direction_re_neg {ρ : ℂ} (hρ : ρ.re = 1 / 2) (h0 : riemannZeta ρ = 0)
    (hsimple : deriv riemannZeta ρ ≠ 0) (hγ : 14 ≤ |ρ.im|) :
    (etaTrivial (ρ - 2) / deriv etaTrivial ρ * (starRingEnd ℂ) (deriv riemannZeta ρ)).re < 0 := by
  rw [growth_direction_eta hρ h0 hsimple]
  have hc : (starRingEnd ℂ) (deriv riemannZeta ρ) ≠ 0 := by rwa [map_ne_zero]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have key : ((1 - (2 : ℂ) ^ (3 - ρ)) / (1 - (2 : ℂ) ^ (1 - ρ))) * ((1 - ρ) * (2 - ρ) / (4 * (π : ℂ) ^ 2))
        * (starRingEnd ℂ) (riemannZeta (ρ + 2) / deriv riemannZeta ρ) * (starRingEnd ℂ) (deriv riemannZeta ρ)
      = ((-(1 / (4 * π ^ 2)) : ℝ) : ℂ) * (((1 - (2 : ℂ) ^ (3 - ρ)) / (1 - (2 : ℂ) ^ (1 - ρ)))
          * (-((1 - ρ) * (2 - ρ))) * (starRingEnd ℂ) (riemannZeta (ρ + 2))) := by
    rw [map_div₀]; push_cast; field_simp
  rw [key, Complex.re_ofReal_mul]
  have hpos := phase_bound hρ hγ
  have : 0 < 1 / (4 * π ^ 2) := by positivity
  nlinarith

end CriticalLinePhasor.PhaseBound

#print axioms CriticalLinePhasor.PhaseBound.zeta_inSector
#print axioms CriticalLinePhasor.PhaseBound.phase_bound
#print axioms CriticalLinePhasor.PhaseBound.growth_direction_re_neg
