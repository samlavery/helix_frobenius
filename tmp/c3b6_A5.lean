import c3b6_A4
import c3b5_A1
import RequestProject.JKernelSignLaw

/-!
# C3 batch 6, block A5 — obligation B, part 1: the exact `(n,m)` cross term

The cell density in the pairing variable is, up to a positive normalisation,

  `C(u,x) = ∫_ℝ Φ(u+p)·Φ(u−p)·cos(2xp) dp`,   `Φ = riemannXiKernel = 4·Σ_n riemannXiKernelTerm n`.

This file computes **one `(n,m)` cross term exactly**, with all constants, and with the
`p`-integral evaluated in closed form against the compiled Macdonald function of blocks
A1–A4.  Nothing is dropped, nothing is asymptotic.

With `a = n+1`, `b = m+1`, and

  `A_{nm}(u) = 2π a b e^{2u}`,   `w = 2p + log(a/b)`,

the pointwise identity is

  `Φ_n(u+p)·Φ_m(u−p) = π²a²b²·e^{5u}·(A² − 6A cosh w + 9)·e^{−A cosh w}`   (`modePair_eq`)

— the exponent collapse is `C3B5.A1.theta_pair_cosh`, the polynomial collapse is
`C3B5.A1.bracket_product`, both compiled in batch 5 and here *applied* to the repository's
actual `riemannXiKernelTerm` rather than to an abstract pair.

Integrating in `p` (change of variables `w = 2p + log(a/b)`, `dp = dw/2`) gives

  `∫_ℝ Φ_n(u+p)Φ_m(u−p)cos(2xp) dp
     = π²a²b²·e^{5u}·cos(x·log(a/b))·[(A²+9)K_{ix}(A) + 6A K′_{ix}(A)]`   (`modePair_integral`)

i.e. exactly `C3B5.A2.radial A (kix 0 x A) (kix 1 x A)` times the arithmetic phase.  This
is the object whose positivity block A4 proved above `A > max(8, 4(|x|+1)²)`.

The two structural facts that make the double sum collapse are recorded here as well:
`A_{nm}` depends on `(n,m)` only through the product `ab`, and the polynomial weight
`a²b²` equals `(ab)²` — so the `(n,m)` sum is a sum over the hyperbola `ab = k`, with the
arithmetic phase `Σ_{ab=k} cos(x log(a/b)) = C3B5.A2.divisorPhase x k`.

SCOPE: nothing here mentions `Ξ`, zeros, positivity of any quadratic form, or RH.
-/

open MeasureTheory Set Filter Topology

noncomputable section

namespace C3B6.Theta

open C3B6.Bessel
open CriticalLinePhasor.ThetaWronskianSuzukiGram

/-! ### 1. Full-line integrability of the Macdonald integrands -/

/-- `exp(c·w − b·w²)` is integrable for `b > 0`. -/
theorem integrable_exp_lin_quad {b c : ℝ} (hb : 0 < b) :
    Integrable (fun w : ℝ => Real.exp (c * w - b * w ^ 2)) := by
  have hbne : b ≠ 0 := hb.ne'
  have hg : Integrable (fun w : ℝ => Real.exp (-b * w ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  have hgt : Integrable (fun w : ℝ => Real.exp (-b * (w - c / (2 * b)) ^ 2)) := by
    simpa using hg.comp_sub_right (c / (2 * b))
  have hscaled := hgt.const_mul (Real.exp (c ^ 2 / (4 * b)))
  have hfun : (fun w : ℝ => Real.exp (c * w - b * w ^ 2))
      = fun w : ℝ => Real.exp (c ^ 2 / (4 * b)) * Real.exp (-b * (w - c / (2 * b)) ^ 2) := by
    funext w
    rw [← Real.exp_add, Real.exp_eq_exp]
    field_simp
    ring
  rw [hfun]
  exact hscaled

/-- The two-sided majorant: `coshMaj` reflected and added to itself. -/
def coshMajTwo (j : ℕ) (δ w : ℝ) : ℝ :=
  Real.exp (-(δ / 2)) *
    (Real.exp (((j : ℝ) - δ / 2) * w - (δ / 4) * w ^ 2)
      + Real.exp (-((j : ℝ) - δ / 2) * w - (δ / 4) * w ^ 2))

theorem coshMajTwo_integrable (j : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (coshMajTwo j δ) := by
  have hb : (0 : ℝ) < δ / 4 := by linarith
  have h1 := integrable_exp_lin_quad (b := δ / 4) (c := (j : ℝ) - δ / 2) hb
  have h2 := integrable_exp_lin_quad (b := δ / 4) (c := -((j : ℝ) - δ / 2)) hb
  exact (h1.add h2).const_mul _

/-- **The two-sided domination**, valid for every real `w` (no sign condition). -/
theorem cosh_pow_exp_le_two {j : ℕ} {A δ w : ℝ} (hδ : 0 < δ) (hA : δ ≤ A) :
    Real.cosh w ^ j * Real.exp (-(A * Real.cosh w)) ≤ coshMajTwo j δ w := by
  have hpos1 : (0 : ℝ) ≤ Real.exp (((j : ℝ) - δ / 2) * w - (δ / 4) * w ^ 2) :=
    (Real.exp_pos _).le
  have hpos2 : (0 : ℝ) ≤ Real.exp (-((j : ℝ) - δ / 2) * w - (δ / 4) * w ^ 2) :=
    (Real.exp_pos _).le
  have hE : (0 : ℝ) < Real.exp (-(δ / 2)) := Real.exp_pos _
  rcases le_total 0 w with hw | hw
  · have h := cosh_pow_exp_le (j := j) hδ hA hw
    unfold coshMaj at h
    unfold coshMajTwo
    nlinarith [h, hpos2, hE]
  · have hw' : (0 : ℝ) ≤ -w := by linarith
    have h := cosh_pow_exp_le (j := j) hδ hA hw'
    rw [Real.cosh_neg] at h
    unfold coshMaj at h
    have hrw : Real.exp (((j : ℝ) - δ / 2) * -w - (δ / 4) * (-w) ^ 2)
        = Real.exp (-((j : ℝ) - δ / 2) * w - (δ / 4) * w ^ 2) := by
      rw [Real.exp_eq_exp]; ring
    rw [hrw] at h
    unfold coshMajTwo
    nlinarith [h, hpos1, hE]

/-- A `cos`/`sin`-weighted Macdonald integrand is integrable on the whole line. -/
theorem kixLike_integrable (j : ℕ) {A : ℝ} (hA : 0 < A) {g : ℝ → ℝ}
    (hg : Continuous g) (hgb : ∀ w, |g w| ≤ 1) :
    Integrable (fun w : ℝ =>
      (-Real.cosh w) ^ j * Real.exp (-(A * Real.cosh w)) * g w) := by
  have hcont : Continuous (fun w : ℝ =>
      (-Real.cosh w) ^ j * Real.exp (-(A * Real.cosh w)) * g w) :=
    (((Real.continuous_cosh.neg).pow j).mul
      (Real.continuous_exp.comp ((continuous_const.mul Real.continuous_cosh).neg))).mul hg
  refine Integrable.mono (coshMajTwo_integrable j hA) hcont.aestronglyMeasurable ?_
  filter_upwards with w
  have hc0 : (0 : ℝ) < Real.cosh w := lt_of_lt_of_le one_pos (one_le_cosh w)
  have hbase : |(-Real.cosh w) ^ j * Real.exp (-(A * Real.cosh w)) * g w|
      ≤ Real.cosh w ^ j * Real.exp (-(A * Real.cosh w)) := by
    rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_of_nonneg hc0.le,
      abs_of_nonneg (Real.exp_pos _).le]
    calc Real.cosh w ^ j * Real.exp (-(A * Real.cosh w)) * |g w|
        ≤ Real.cosh w ^ j * Real.exp (-(A * Real.cosh w)) * 1 :=
          mul_le_mul_of_nonneg_left (hgb w) (by positivity)
      _ = Real.cosh w ^ j * Real.exp (-(A * Real.cosh w)) := by ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (le_trans (by positivity) (cosh_pow_exp_le_two (j := j) hA le_rfl))]
  exact hbase.trans (cosh_pow_exp_le_two hA le_rfl)

theorem kixTerm_integrable (j : ℕ) (x : ℝ) {A : ℝ} (hA : 0 < A) :
    Integrable (kixTerm j x A) := by
  have := kixLike_integrable j hA
    (g := fun w => Real.cos (x * w))
    (Real.continuous_cos.comp (continuous_const.mul continuous_id))
    (fun w => Real.abs_cos_le_one _)
  exact this

/-! ### 2. Evenness: the full line is twice the half line -/

theorem kixTerm_even (j : ℕ) (x A w : ℝ) : kixTerm j x A (-w) = kixTerm j x A w := by
  unfold kixTerm
  rw [Real.cosh_neg, show x * -w = -(x * w) by ring, Real.cos_neg]

theorem kixFull_eq (j : ℕ) (x : ℝ) {A : ℝ} (hA : 0 < A) :
    (∫ w : ℝ, kixTerm j x A w) = 2 * kix j x A := by
  have hint := kixTerm_integrable j x hA
  have hsym : (∫ w in Iic (0 : ℝ), kixTerm j x A w)
      = ∫ w in Ioi (0 : ℝ), kixTerm j x A w := by
    have hneg := integral_comp_neg_Iic (0 : ℝ) (kixTerm j x A)
    rw [neg_zero] at hneg
    rw [← hneg]
    refine setIntegral_congr_fun measurableSet_Iic fun w _ => ?_
    exact (kixTerm_even j x A w).symm
  have hsplit := intervalIntegral.integral_Iic_add_Ioi (f := kixTerm j x A) (b := (0 : ℝ))
    hint.integrableOn hint.integrableOn
  rw [hsym] at hsplit
  rw [← hsplit]
  unfold kix
  ring

/-! ### 3. The odd part vanishes -/

def kixTermSin (j : ℕ) (x A w : ℝ) : ℝ :=
  (-Real.cosh w) ^ j * Real.exp (-(A * Real.cosh w)) * Real.sin (x * w)

theorem kixTermSin_odd (j : ℕ) (x A w : ℝ) :
    kixTermSin j x A (-w) = -kixTermSin j x A w := by
  unfold kixTermSin
  rw [Real.cosh_neg, show x * -w = -(x * w) by ring, Real.sin_neg]
  ring

theorem kixTermSin_integrable (j : ℕ) (x : ℝ) {A : ℝ} (hA : 0 < A) :
    Integrable (kixTermSin j x A) :=
  kixLike_integrable j hA (g := fun w => Real.sin (x * w))
    (Real.continuous_sin.comp (continuous_const.mul continuous_id))
    (fun w => Real.abs_sin_le_one _)

theorem integral_kixTermSin (j : ℕ) (x A : ℝ) :
    (∫ w : ℝ, kixTermSin j x A w) = 0 := by
  have h := MeasureTheory.Measure.integral_comp_mul_left (kixTermSin j x A) (-1)
  have hL : (∫ w : ℝ, kixTermSin j x A (-1 * w))
      = ∫ w : ℝ, -kixTermSin j x A w := by
    refine integral_congr_ae ?_
    filter_upwards with w
    rw [show (-1 : ℝ) * w = -w by ring, kixTermSin_odd]
  rw [hL, integral_neg] at h
  simp only [abs_of_nonneg, smul_eq_mul] at h
  have h2 : -(∫ w : ℝ, kixTermSin j x A w) = ∫ w : ℝ, kixTermSin j x A w := by
    simpa using h
  linarith

/-! ### 4. The shifted-cosine full-line integral -/

/-- `(-cosh w)^j · e^{−A cosh w} · cos(x(w − λ))`. -/
def kixTermShift (j : ℕ) (x A lam w : ℝ) : ℝ :=
  (-Real.cosh w) ^ j * Real.exp (-(A * Real.cosh w)) * Real.cos (x * (w - lam))

theorem kixTermShift_integrable (j : ℕ) (x : ℝ) {A : ℝ} (hA : 0 < A) (lam : ℝ) :
    Integrable (kixTermShift j x A lam) :=
  kixLike_integrable j hA (g := fun w => Real.cos (x * (w - lam)))
    (Real.continuous_cos.comp (continuous_const.mul (continuous_id.sub continuous_const)))
    (fun w => Real.abs_cos_le_one _)

/-- **The shifted-cosine evaluation.**  The `sin` half is odd and dies; the `cos` half is
even and doubles the half-line integral. -/
theorem integral_kixTermShift (j : ℕ) (x : ℝ) {A : ℝ} (hA : 0 < A) (lam : ℝ) :
    (∫ w : ℝ, kixTermShift j x A lam w) = 2 * Real.cos (x * lam) * kix j x A := by
  have hpt : ∀ w : ℝ, kixTermShift j x A lam w
      = Real.cos (x * lam) * kixTerm j x A w
        + Real.sin (x * lam) * kixTermSin j x A w := by
    intro w
    unfold kixTermShift kixTerm kixTermSin
    rw [show x * (w - lam) = x * w - x * lam by ring, Real.cos_sub]
    ring
  have hcongr : (∫ w : ℝ, kixTermShift j x A lam w)
      = ∫ w : ℝ, (Real.cos (x * lam) * kixTerm j x A w
          + Real.sin (x * lam) * kixTermSin j x A w) := by
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [hcongr,
    integral_add ((kixTerm_integrable j x hA).const_mul _)
      ((kixTermSin_integrable j x hA).const_mul _),
    integral_const_mul, integral_const_mul, integral_kixTermSin, kixFull_eq j x hA]
  ring

/-! ### 5. The mode data -/

/-- `A_{nm}(u) = 2π(n+1)(m+1)e^{2u}` — the radial variable of the `(n,m)` mode pair.
It depends on `(n,m)` only through the **product** `(n+1)(m+1)`. -/
def modeA (n m : ℕ) (u : ℝ) : ℝ :=
  2 * Real.pi * ((n : ℝ) + 1) * ((m : ℝ) + 1) * Real.exp (2 * u)

/-- `w = 2p + log((n+1)/(m+1))` — the hyperbolic angle of the `(n,m)` mode pair. -/
def modeW (n m : ℕ) (p : ℝ) : ℝ := 2 * p + Real.log (((n : ℝ) + 1) / ((m : ℝ) + 1))

theorem modeA_pos (n m : ℕ) (u : ℝ) : 0 < modeA n m u := by
  unfold modeA
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have := Real.pi_pos
  positivity

theorem modeA_exp_w (n m : ℕ) (u p : ℝ) :
    modeA n m u * Real.exp (modeW n m p)
      = 2 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * (u + p)) := by
  have ha : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hb : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hab : (0 : ℝ) < ((n : ℝ) + 1) / ((m : ℝ) + 1) := div_pos ha hb
  unfold modeA modeW
  rw [Real.exp_add, Real.exp_log hab,
    show (2 : ℝ) * (u + p) = 2 * u + 2 * p by ring, Real.exp_add]
  field_simp

theorem modeA_exp_neg_w (n m : ℕ) (u p : ℝ) :
    modeA n m u * Real.exp (-(modeW n m p))
      = 2 * Real.pi * ((m : ℝ) + 1) ^ 2 * Real.exp (2 * (u - p)) := by
  have ha : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hb : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hab : (0 : ℝ) < ((n : ℝ) + 1) / ((m : ℝ) + 1) := div_pos ha hb
  have hba : (0 : ℝ) < ((m : ℝ) + 1) / ((n : ℝ) + 1) := div_pos hb ha
  have hlog : Real.log (((m : ℝ) + 1) / ((n : ℝ) + 1))
      = -Real.log (((n : ℝ) + 1) / ((m : ℝ) + 1)) := by
    rw [← Real.log_inv]
    congr 1
    field_simp
  unfold modeA modeW
  rw [show -(2 * p + Real.log (((n : ℝ) + 1) / ((m : ℝ) + 1)))
        = -(2 * p) + Real.log (((m : ℝ) + 1) / ((n : ℝ) + 1)) by rw [hlog]; ring,
    Real.exp_add, Real.exp_log hba,
    show (2 : ℝ) * (u - p) = 2 * u + -(2 * p) by ring, Real.exp_add]
  field_simp

/-! ### 6. The exact `(n,m)` cross term -/

/-- Riemann's kernel term, factored: `Φ_n(t) = π a² e^{5t/2}(2π a² e^{2t} − 3)e^{−π a² e^{2t}}`. -/
theorem kernelTerm_factor (n : ℕ) (t : ℝ) :
    riemannXiKernelTerm n t
      = Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * t / 2)
        * (2 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * t) - 3)
        * Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * t))) := by
  unfold riemannXiKernelTerm
  have hexp : Real.exp (9 * t / 2) = Real.exp (5 * t / 2) * Real.exp (2 * t) := by
    rw [← Real.exp_add]; congr 1; ring
  have hneg : Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * t))
      = Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * t))) := by
    congr 1; ring
  dsimp only
  rw [hexp, hneg]
  ring

/-- **THE EXACT `(n,m)` CROSS TERM.**  Every constant retained; no term dropped. -/
theorem modePair_eq (n m : ℕ) (u p : ℝ) :
    riemannXiKernelTerm n (u + p) * riemannXiKernelTerm m (u - p)
      = Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 * Real.exp (5 * u)
        * (modeA n m u ^ 2 - 6 * modeA n m u * Real.cosh (modeW n m p) + 9)
        * Real.exp (-(modeA n m u * Real.cosh (modeW n m p))) := by
  have ha : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hb : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  -- the exponent collapse (batch 5, applied)
  have hcosh : Real.pi * (((n : ℝ) + 1) ^ 2 * Real.exp (2 * (u + p))
        + ((m : ℝ) + 1) ^ 2 * Real.exp (2 * (u - p)))
      = modeA n m u * Real.cosh (modeW n m p) := by
    have := C3B5.A1.theta_pair_cosh (n := (n : ℝ) + 1) (m := (m : ℝ) + 1) ha hb u p
    unfold modeA modeW
    rw [this]
  -- the two polynomial factors, in `A e^{±w}` form
  have hA1 : 2 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * (u + p))
      = modeA n m u * Real.exp (modeW n m p) := (modeA_exp_w n m u p).symm
  have hA2 : 2 * Real.pi * ((m : ℝ) + 1) ^ 2 * Real.exp (2 * (u - p))
      = modeA n m u * Real.exp (-(modeW n m p)) := (modeA_exp_neg_w n m u p).symm
  have hbracket := C3B5.A1.bracket_product (modeA n m u) (modeW n m p)
  -- the `e^{5t/2}` factors
  have h5 : Real.exp (5 * (u + p) / 2) * Real.exp (5 * (u - p) / 2) = Real.exp (5 * u) := by
    rw [← Real.exp_add]; congr 1; ring
  -- the two Gaussian factors
  have hgauss : Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * (u + p))))
      * Real.exp (-(Real.pi * ((m : ℝ) + 1) ^ 2 * Real.exp (2 * (u - p))))
      = Real.exp (-(modeA n m u * Real.cosh (modeW n m p))) := by
    rw [← Real.exp_add]
    congr 1
    rw [← hcosh]
    ring
  rw [kernelTerm_factor, kernelTerm_factor]
  calc Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (5 * (u + p) / 2)
          * (2 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * (u + p)) - 3)
          * Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * (u + p))))
        * (Real.pi * ((m : ℝ) + 1) ^ 2 * Real.exp (5 * (u - p) / 2)
          * (2 * Real.pi * ((m : ℝ) + 1) ^ 2 * Real.exp (2 * (u - p)) - 3)
          * Real.exp (-(Real.pi * ((m : ℝ) + 1) ^ 2 * Real.exp (2 * (u - p)))))
      = (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2)
          * (Real.exp (5 * (u + p) / 2) * Real.exp (5 * (u - p) / 2))
          * ((2 * Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * (u + p)) - 3)
             * (2 * Real.pi * ((m : ℝ) + 1) ^ 2 * Real.exp (2 * (u - p)) - 3))
          * (Real.exp (-(Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * (u + p))))
             * Real.exp (-(Real.pi * ((m : ℝ) + 1) ^ 2 * Real.exp (2 * (u - p))))) := by
        ring
    _ = (Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2) * Real.exp (5 * u)
          * (modeA n m u ^ 2 - 6 * modeA n m u * Real.cosh (modeW n m p) + 9)
          * Real.exp (-(modeA n m u * Real.cosh (modeW n m p))) := by
        rw [h5, hgauss, hA1, hA2, hbracket]
    _ = Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 * Real.exp (5 * u)
          * (modeA n m u ^ 2 - 6 * modeA n m u * Real.cosh (modeW n m p) + 9)
          * Real.exp (-(modeA n m u * Real.cosh (modeW n m p))) := by ring

/-! ### 7. The `p`-integral of one cross term -/

/-- The arithmetic phase offset of the `(n,m)` mode pair: `λ = log((n+1)/(m+1))`. -/
def modeLam (n m : ℕ) : ℝ := Real.log (((n : ℝ) + 1) / ((m : ℝ) + 1))

theorem modeW_eq (n m : ℕ) (p : ℝ) : modeW n m p = 2 * p + modeLam n m := rfl

/-- The mode-pair integrand in the `w` variable: a linear combination of two shifted
Macdonald integrands, with the exact coefficients `(A²+9)` and `6A`. -/
def modeIntegrandW (n m : ℕ) (x u w : ℝ) : ℝ :=
  (modeA n m u ^ 2 + 9) * kixTermShift 0 x (modeA n m u) (modeLam n m) w
    + 6 * modeA n m u * kixTermShift 1 x (modeA n m u) (modeLam n m) w

/-- The pointwise rewrite: the bracket `A² − 6A cosh w + 9` against `e^{−A cosh w}` and the
shifted cosine IS that linear combination. -/
theorem modeIntegrandW_eq (n m : ℕ) (x u w : ℝ) :
    modeIntegrandW n m x u w
      = (modeA n m u ^ 2 - 6 * modeA n m u * Real.cosh w + 9)
        * Real.exp (-(modeA n m u * Real.cosh w))
        * Real.cos (x * (w - modeLam n m)) := by
  unfold modeIntegrandW kixTermShift
  rw [pow_zero, pow_one]
  ring

/-- **THE EXACT `(n,m)` MODE INTEGRAL.**

`∫_ℝ Φ_n(u+p)·Φ_m(u−p)·cos(2xp) dp
   = π²(n+1)²(m+1)²·e^{5u}·cos(x·log((n+1)/(m+1)))·radial(A_{nm}(u))`

with `radial A K K' = (A²+9)K + 6A·K'` the compiled `C3B5.A2.radial`, evaluated at the
Macdonald function `K_{ix}` and its genuine derivative. -/
theorem modePair_integral (n m : ℕ) (x u : ℝ) :
    (∫ p : ℝ, riemannXiKernelTerm n (u + p) * riemannXiKernelTerm m (u - p)
        * Real.cos (2 * x * p))
      = Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 * Real.exp (5 * u)
        * Real.cos (x * modeLam n m)
        * C3B5.A2.radial (modeA n m u) (kix 0 x (modeA n m u)) (kix 1 x (modeA n m u)) := by
  have hA : 0 < modeA n m u := modeA_pos n m u
  have hpt : ∀ p : ℝ, riemannXiKernelTerm n (u + p) * riemannXiKernelTerm m (u - p)
      * Real.cos (2 * x * p)
      = Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 * Real.exp (5 * u)
        * modeIntegrandW n m x u (2 * p + modeLam n m) := by
    intro p
    rw [modePair_eq n m u p, modeW_eq, modeIntegrandW_eq,
      show x * (2 * p + modeLam n m - modeLam n m) = 2 * x * p by ring]
    ring
  have hcongr : (∫ p : ℝ, riemannXiKernelTerm n (u + p) * riemannXiKernelTerm m (u - p)
        * Real.cos (2 * x * p))
      = ∫ p : ℝ, Real.pi ^ 2 * ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 * Real.exp (5 * u)
          * modeIntegrandW n m x u (2 * p + modeLam n m) :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hscale : (∫ p : ℝ, modeIntegrandW n m x u (2 * p + modeLam n m))
      = |(2 : ℝ)⁻¹| • ∫ q : ℝ, modeIntegrandW n m x u (q + modeLam n m) := by
    have h := MeasureTheory.Measure.integral_comp_mul_left
      (fun q : ℝ => modeIntegrandW n m x u (q + modeLam n m)) 2
    simpa using h
  have hshift : (∫ q : ℝ, modeIntegrandW n m x u (q + modeLam n m))
      = ∫ w : ℝ, modeIntegrandW n m x u w :=
    integral_add_right_eq_self (modeIntegrandW n m x u) (modeLam n m)
  have hFint : (∫ w : ℝ, modeIntegrandW n m x u w)
      = 2 * Real.cos (x * modeLam n m)
        * ((modeA n m u ^ 2 + 9) * kix 0 x (modeA n m u)
           + 6 * modeA n m u * kix 1 x (modeA n m u)) := by
    unfold modeIntegrandW
    rw [integral_add ((kixTermShift_integrable 0 x hA (modeLam n m)).const_mul _)
      ((kixTermShift_integrable 1 x hA (modeLam n m)).const_mul _),
      integral_const_mul, integral_const_mul,
      integral_kixTermShift 0 x hA (modeLam n m),
      integral_kixTermShift 1 x hA (modeLam n m)]
    ring
  rw [hcongr, integral_const_mul, hscale, hshift, hFint, C3B5.A2.radial,
    show |(2 : ℝ)⁻¹| = 2⁻¹ from abs_of_nonneg (by norm_num)]
  simp only [smul_eq_mul]
  ring

/-! ### 8. The hyperbola: why the double sum collapses -/

/-- **`A_{nm}` depends only on the product.**  `(n+1)(m+1) = (n'+1)(m'+1)` implies the two
mode pairs have the *same* radial variable — this is the hyperbola collapse. -/
theorem modeA_eq_of_prod_eq {n m n' m' : ℕ} (u : ℝ)
    (h : ((n : ℝ) + 1) * ((m : ℝ) + 1) = ((n' : ℝ) + 1) * ((m' : ℝ) + 1)) :
    modeA n m u = modeA n' m' u := by
  unfold modeA
  rw [show 2 * Real.pi * ((n : ℝ) + 1) * ((m : ℝ) + 1) * Real.exp (2 * u)
        = 2 * Real.pi * (((n : ℝ) + 1) * ((m : ℝ) + 1)) * Real.exp (2 * u) by ring,
    show 2 * Real.pi * ((n' : ℝ) + 1) * ((m' : ℝ) + 1) * Real.exp (2 * u)
        = 2 * Real.pi * (((n' : ℝ) + 1) * ((m' : ℝ) + 1)) * Real.exp (2 * u) by ring, h]

/-- **The polynomial weight is the hyperbola weight.**  `a²b² = (ab)²`, so the `(n,m)`
weight is constant along `ab = k` — `C3B5.A2.hyperbola_weight`, at the actual modes. -/
theorem modePair_weight (n m : ℕ) :
    ((n : ℝ) + 1) ^ 2 * ((m : ℝ) + 1) ^ 2 = (((n : ℝ) + 1) * ((m : ℝ) + 1)) ^ 2 := by
  ring

/-- **The arithmetic phase is the divisor phase.**  For `ab = k` the mode phase
`cos(x log(a/b))` is the summand of `C3B5.A2.divisorPhase x k`, because
`a/b = a²/k`. -/
theorem modePair_phase (x : ℝ) {a b k : ℝ} (ha : 0 < a) (hb : 0 < b) (hk : a * b = k) :
    Real.cos (x * Real.log (a / b)) = Real.cos (x * Real.log (a ^ 2 / k)) := by
  congr 2
  rw [← hk]
  congr 1
  field_simp

end C3B6.Theta

section AxiomAudit
#print axioms C3B6.Theta.integrable_exp_lin_quad
#print axioms C3B6.Theta.coshMajTwo_integrable
#print axioms C3B6.Theta.cosh_pow_exp_le_two
#print axioms C3B6.Theta.kixLike_integrable
#print axioms C3B6.Theta.kixTerm_integrable
#print axioms C3B6.Theta.kixFull_eq
#print axioms C3B6.Theta.integral_kixTermSin
#print axioms C3B6.Theta.integral_kixTermShift
#print axioms C3B6.Theta.modeA_exp_w
#print axioms C3B6.Theta.modeA_exp_neg_w
#print axioms C3B6.Theta.kernelTerm_factor
#print axioms C3B6.Theta.modeIntegrandW_eq
#print axioms C3B6.Theta.modePair_eq
#print axioms C3B6.Theta.modePair_integral
#print axioms C3B6.Theta.modeA_eq_of_prod_eq
#print axioms C3B6.Theta.modePair_phase
end AxiomAudit
