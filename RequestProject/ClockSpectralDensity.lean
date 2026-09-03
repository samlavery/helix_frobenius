import RequestProject.BankDoorFaceLaw

/-!
# The spectral density of the barycenter-clock operator, and its DC split
(HP_SKELETON [HP-trace], fiber side; att532, ledger 532)

The unitary-clock direct integral of prime `p` at Poisson radius `r = p^{−½}` (the compiled
barycenter law, `ClockPoissonBarycenter`) has, on the height axis `z` (the line `s = ½ + iz`),
the spectral density

  `clockDensity p z = (log p / 2π) · poissonKernel 0 r (e^{iθ})`,  `θ = z log p`.

Two exact identities make this the fiber side of the HP trace:

* `clockDensity_eq_re_logDeriv` — the density is `(1/π)·Re` of the compiled clock's
  log-derivative in `s` on the line: the operator's spectral measure IS the real part of the
  clock face, read where the door law reads it.
* `clockDensity_hasSum` — the DC split
  `clockDensity p z = log p/2π + (1/π) Σ_{k≥1} log p · p^{−k/2} cos(k z log p)`:
  the clock DC plus the von Mangoldt oscillation of the powers of `p`.

The att532 object `ϑ′/π + DC_Q − Σ_p clockDensity + END_Q` therefore has its clock DC cancel
exactly, leaving the Γ-clock density, the end term, and minus the `Q`-smooth von Mangoldt
oscillation (`bankDensity_sub_dc`).  Its identification with the zero-counting measure is the
truncated explicit formula, not compiled here.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.BankLimit

open CriticalLinePhasor.ChiralityHB

/-- The Euler radius of `p`: `p^{−½}`. -/
def eulerRadius (p : ℕ) : ℝ := (p : ℝ) ^ (-(1 / 2 : ℝ))

theorem eulerRadius_pos {p : ℕ} (hp : 0 < p) : 0 < eulerRadius p := by
  unfold eulerRadius
  exact Real.rpow_pos_of_pos (by exact_mod_cast hp) _

theorem eulerRadius_lt_one {p : ℕ} (hp : 1 < p) : eulerRadius p < 1 := by
  unfold eulerRadius
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp) (by norm_num)

/-- The clock angle on the height axis: `θ = z log p`. -/
def clockAngle (p : ℕ) (z : ℝ) : ℝ := z * Real.log p

/-- **The spectral density of the barycenter clock of `p` on the height axis**:
`(log p / 2π)` times the Poisson kernel at radius `p^{−½}`, at the circle point `e^{iθ}`. -/
def clockDensity (p : ℕ) (z : ℝ) : ℝ :=
  (Real.log p / (2 * Real.pi))
    * poissonKernel 0 (eulerRadius p : ℂ) (Complex.exp (Complex.I * (clockAngle p z : ℂ)))

/-- The disk point `w = r e^{−iθ}` of the clock on the line. -/
def lineDiskPoint (p : ℕ) (z : ℝ) : ℂ :=
  (eulerRadius p : ℂ) * Complex.exp (-(Complex.I * (clockAngle p z : ℂ)))

theorem norm_exp_I_mul_ofReal' (θ : ℝ) : ‖Complex.exp (Complex.I * (θ : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem norm_exp_neg_I_mul_ofReal (θ : ℝ) : ‖Complex.exp (-(Complex.I * (θ : ℂ)))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem lineDiskPoint_norm {p : ℕ} (hp : 0 < p) (z : ℝ) :
    ‖lineDiskPoint p z‖ = eulerRadius p := by
  unfold lineDiskPoint
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (eulerRadius_pos hp),
    norm_exp_neg_I_mul_ofReal, mul_one]

theorem lineDiskPoint_norm_lt_one {p : ℕ} (hp : 1 < p) (z : ℝ) :
    ‖lineDiskPoint p z‖ < 1 := by
  rw [lineDiskPoint_norm (by omega) z]
  exact eulerRadius_lt_one hp

theorem one_sub_lineDiskPoint_ne_zero {p : ℕ} (hp : 1 < p) (z : ℝ) :
    1 - lineDiskPoint p z ≠ 0 := by
  intro h
  have h1 : lineDiskPoint p z = 1 := by linear_combination -h
  have hn := lineDiskPoint_norm_lt_one hp z
  rw [h1, norm_one] at hn
  exact lt_irrefl _ hn

/-- The Poisson kernel at the circle point `e^{iθ}` and radius `r` is the real part of the
Herglotz kernel at the disk point `w = r e^{−iθ}`. -/
theorem poissonKernel_eq_herglotz_re (r θ : ℝ) :
    poissonKernel 0 (r : ℂ) (Complex.exp (Complex.I * (θ : ℂ)))
      = ((1 + (r : ℂ) * Complex.exp (-(Complex.I * (θ : ℂ))))
          / (1 - (r : ℂ) * Complex.exp (-(Complex.I * (θ : ℂ))))).re := by
  rw [herglotzKernel_re, poissonKernel_def]
  simp only [sub_zero]
  have hu := norm_exp_I_mul_ofReal' θ
  have hw : ‖(r : ℂ) * Complex.exp (-(Complex.I * (θ : ℂ)))‖ = ‖(r : ℂ)‖ := by
    rw [norm_mul, norm_exp_neg_I_mul_ofReal, mul_one]
  have hd : ‖(1 : ℂ) - (r : ℂ) * Complex.exp (-(Complex.I * (θ : ℂ)))‖
      = ‖Complex.exp (Complex.I * (θ : ℂ)) - (r : ℂ)‖ := by
    have hprod : Complex.exp (Complex.I * (θ : ℂ)) * Complex.exp (-(Complex.I * (θ : ℂ))) = 1 := by
      rw [← Complex.exp_add]
      simp
    have hfac : Complex.exp (Complex.I * (θ : ℂ)) - (r : ℂ)
        = Complex.exp (Complex.I * (θ : ℂ))
          * (1 - (r : ℂ) * Complex.exp (-(Complex.I * (θ : ℂ)))) := by
      linear_combination (r : ℂ) * hprod
    rw [hfac, norm_mul, hu, one_mul]
  rw [hu, hw, hd]
  ring

/-- `spectralCoord (½ + iz) = z`: on the line the spectral coordinate is the height itself. -/
theorem spectralCoord_line (z : ℝ) :
    HilbertPolya.spectralCoord ((1 / 2 : ℂ) + Complex.I * z) = (z : ℂ) := by
  unfold HilbertPolya.spectralCoord
  linear_combination (-(z : ℂ)) * Complex.I_sq

/-- **The density is the real part of the compiled clock face, read on the line**:
`clockDensity p z = (1/π)·Re logDeriv_s(clock_p)(½ + iz)`, `clock_p = symClock (p^{−½}) (log p) ∘ spectralCoord`. -/
theorem clockDensity_eq_re_logDeriv {p : ℕ} (hp : 1 < p) (z : ℝ) :
    clockDensity p z
      = (1 / Real.pi) * (logDeriv (fun w => symClock (eulerRadius p : ℂ) (Real.log p)
          (HilbertPolya.spectralCoord w)) ((1 / 2 : ℂ) + Complex.I * z)).re := by
  set w : ℂ := lineDiskPoint p z with hw
  have hne : 1 - w ≠ 0 := one_sub_lineDiskPoint_ne_zero hp z
  have hwform : (eulerRadius p : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (Real.log p : ℂ))) = w := by
    rw [hw]
    unfold lineDiskPoint clockAngle
    congr 1
    congr 1
    push_cast
    ring
  have hcomp0 : logDeriv (fun w => symClock (eulerRadius p : ℂ) (Real.log p)
      (HilbertPolya.spectralCoord w)) ((1 / 2 : ℂ) + Complex.I * z)
      = logDeriv (symClock (eulerRadius p : ℂ) (Real.log p))
          (HilbertPolya.spectralCoord ((1 / 2 : ℂ) + Complex.I * z))
        * deriv HilbertPolya.spectralCoord ((1 / 2 : ℂ) + Complex.I * z) :=
    logDeriv_comp (symClock_differentiableAt _ _ _) (spectralCoord_hasDerivAt _).differentiableAt
  have hcomp : logDeriv (fun w => symClock (eulerRadius p : ℂ) (Real.log p)
      (HilbertPolya.spectralCoord w)) ((1 / 2 : ℂ) + Complex.I * z)
      = logDeriv (symClock (eulerRadius p : ℂ) (Real.log p)) (z : ℂ) * (-Complex.I) := by
    rw [hcomp0, (spectralCoord_hasDerivAt _).deriv, spectralCoord_line]
  have hne' : 1 - (eulerRadius p : ℂ) * Complex.exp (-(Complex.I * (z : ℂ) * (Real.log p : ℂ))) ≠ 0 := by
    rw [hwform]
    exact hne
  rw [hcomp, symClock_logDeriv_face_form _ _ _ hne', hwform]
  have hK : (Complex.I * (Real.log p : ℂ) / 2) * ((1 + w) / (1 - w)) * (-Complex.I)
      = ((Real.log p / 2 : ℝ) : ℂ) * ((1 + w) / (1 - w)) := by
    rw [Complex.ofReal_div, Complex.ofReal_ofNat]
    linear_combination (-((Real.log p : ℝ) : ℂ) / 2 * ((1 + w) / (1 - w))) * Complex.I_sq
  rw [hK, Complex.re_ofReal_mul]
  unfold clockDensity
  rw [poissonKernel_eq_herglotz_re]
  have hwθ : (eulerRadius p : ℂ) * Complex.exp (-(Complex.I * (clockAngle p z : ℂ))) = w := by
    rw [hw]
    rfl
  rw [hwθ]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

/-- `Re(w^{j+1}) = r^{j+1} cos((j+1)θ)` for the disk point `w = r e^{−iθ}`. -/
theorem lineDiskPoint_pow_re (p : ℕ) (z : ℝ) (j : ℕ) :
    (lineDiskPoint p z ^ (j + 1)).re
      = eulerRadius p ^ (j + 1) * Real.cos ((j + 1) * clockAngle p z) := by
  unfold lineDiskPoint
  rw [mul_pow, ← Complex.ofReal_pow, ← Complex.exp_nat_mul, Complex.re_ofReal_mul]
  congr 1
  have harg : ((j + 1 : ℕ) : ℂ) * -(Complex.I * (clockAngle p z : ℂ))
      = ((-((j + 1 : ℕ) * clockAngle p z) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [harg, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  push_cast
  ring_nf

/-- **The DC split of the clock density**:
`clockDensity p z − log p/2π = (1/π) Σ_{j≥0} log p · p^{−(j+1)/2} cos((j+1) z log p)`. -/
theorem clockDensity_hasSum {p : ℕ} (hp : 1 < p) (z : ℝ) :
    HasSum (fun j : ℕ => (Real.log p / Real.pi)
        * (eulerRadius p ^ (j + 1) * Real.cos ((j + 1) * clockAngle p z)))
      (clockDensity p z - Real.log p / (2 * Real.pi)) := by
  set w : ℂ := lineDiskPoint p z with hw
  have hw1 : ‖w‖ < 1 := lineDiskPoint_norm_lt_one hp z
  have hne : 1 - w ≠ 0 := one_sub_lineDiskPoint_ne_zero hp z
  -- the geometric series Σ_{j≥0} w^{j+1} = w (1−w)⁻¹
  have hgeom : HasSum (fun j : ℕ => w ^ (j + 1)) (w * (1 - w)⁻¹) := by
    have h := (hasSum_geometric_of_norm_lt_one hw1).mul_left w
    have hf : (fun j : ℕ => w ^ (j + 1)) = fun j : ℕ => w * w ^ j := by
      funext j
      ring
    rw [hf]
    exact h
  have hre : HasSum (fun j : ℕ => (w ^ (j + 1)).re) (w * (1 - w)⁻¹).re :=
    ((Complex.hasSum_iff _ _).mp hgeom).1
  have hf2 : (fun j : ℕ => (w ^ (j + 1)).re)
      = fun j : ℕ => eulerRadius p ^ (j + 1) * Real.cos ((j + 1) * clockAngle p z) := by
    funext j
    rw [hw]
    exact lineDiskPoint_pow_re p z j
  rw [hf2] at hre
  have hval : (w * (1 - w)⁻¹).re = (((1 + w) / (1 - w)).re - 1) / 2 := by
    have hsplit : (1 + w) / (1 - w) = 1 + 2 * (w * (1 - w)⁻¹) := by
      field_simp
      ring
    rw [hsplit]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
      zero_mul, sub_zero]
    ring
  have hmain := hre.mul_left (Real.log p / Real.pi)
  have hvalue : (Real.log p / Real.pi) * (w * (1 - w)⁻¹).re
      = clockDensity p z - Real.log p / (2 * Real.pi) := by
    rw [hval]
    unfold clockDensity
    rw [poissonKernel_eq_herglotz_re]
    have hwθ : (eulerRadius p : ℂ) * Complex.exp (-(Complex.I * (clockAngle p z : ℂ))) = w := by
      rw [hw]
      rfl
    rw [hwθ]
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [hvalue] at hmain
  exact hmain

/-- The finite-bank density over a conduction set `Q`. -/
def bankDensity (Q : Finset ℕ) (z : ℝ) : ℝ := ∑ p ∈ Q, clockDensity p z

/-- The bank's clock DC: `Σ_{p∈Q} log p / 2π`. -/
def bankDC (Q : Finset ℕ) : ℝ := ∑ p ∈ Q, Real.log p / (2 * Real.pi)

/-- **The clock DC cancels exactly**: the DC-subtracted bank density is the `Q`-smooth
von Mangoldt oscillation `(1/π) Σ_{p∈Q} Σ_{k≥1} log p · p^{−k/2} cos(k z log p)`. -/
theorem bankDensity_sub_dc (Q : Finset ℕ) (hQ : ∀ p ∈ Q, 1 < p) (z : ℝ) :
    bankDensity Q z - bankDC Q
      = ∑ p ∈ Q, ∑' j : ℕ, (Real.log p / Real.pi)
          * (eulerRadius p ^ (j + 1) * Real.cos ((j + 1) * clockAngle p z)) := by
  unfold bankDensity bankDC
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  exact ((clockDensity_hasSum (hQ p hp) z).tsum_eq).symm

end CriticalLinePhasor.BankLimit

#print axioms CriticalLinePhasor.BankLimit.clockDensity_eq_re_logDeriv
#print axioms CriticalLinePhasor.BankLimit.clockDensity_hasSum
#print axioms CriticalLinePhasor.BankLimit.bankDensity_sub_dc
