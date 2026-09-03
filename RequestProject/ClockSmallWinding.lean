import RequestProject.ClockPoissonBarycenter

/-!
# The small-winding clock is the Hadamard atom

`BankDoorClassLaw` shows the clock door admits only banks whose windings tend to zero apart
from boundedly many clocks.  This file computes what such a clock IS: with the face pinned so
that the clock's zero sits at a real `t₀`, the log-derivative of `symClock (e^{iℓt₀}) ℓ`
converges, as the winding `ℓ → 0⁺`, to the single resolvent atom `1/(z − t₀)`
(`symClock_logDeriv_small_winding`).  The door's admissible clocks are therefore the atoms of
the symmetrized line tower (`HelixSymmetrizedLineTower`): the two compiled doors are one
object, seen at winding `0` and at winding `log p`.

Reading in the geometry: a clock of winding `ℓ` is a helix strand of pitch `2π/ℓ`; as the
pitch grows without bound the strand straightens into the single ray through `t₀`, and its
Herglotz kernel collapses to the atom.  The arithmetic clocks (`ℓ = log p ≥ log 2`) are the
far-from-limit members whose DC `ℓ/2` cannot be absorbed (ledger 517).

No `sorry`, no `axiom`.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.BankLimit

open CriticalLinePhasor.ChiralityHB

/-- The pinned clock's disk point: `α·e^{−izℓ} = e^{iℓ(t₀ − z)}`. -/
theorem pinned_disk_point (ℓ : ℝ) (t₀ : ℝ) (z : ℂ) :
    Complex.exp (Complex.I * ℓ * t₀) * Complex.exp (-(Complex.I * z * ℓ))
      = Complex.exp (Complex.I * ℓ * (t₀ - z)) := by
  rw [← Complex.exp_add]
  congr 1
  ring

/-- Off the real axis the pinned disk point never equals `1` (for `ℓ ≠ 0`). -/
theorem pinned_disk_point_ne_one {ℓ : ℝ} (hℓ : ℓ ≠ 0) {t₀ : ℝ} {z : ℂ} (hz : z.im ≠ 0) :
    Complex.exp (Complex.I * ℓ * (t₀ - z)) ≠ 1 := by
  intro h
  have hn : ‖Complex.exp (Complex.I * ℓ * (t₀ - z))‖ = 1 := by rw [h, norm_one]
  rw [Complex.norm_exp] at hn
  have hre : (Complex.I * (ℓ : ℂ) * ((t₀ : ℂ) - z)).re = ℓ * z.im := by
    simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
  rw [hre, Real.exp_eq_one_iff] at hn
  exact hz (by
    rcases mul_eq_zero.mp hn with h1 | h1
    · exact absurd h1 hℓ
    · exact h1)

/-- The derivative in the winding of `1 − e^{iℓ(t₀ − z)}` at `ℓ = 0` is `i(z − t₀)`. -/
theorem hasDerivAt_one_sub_pinned (t₀ : ℝ) (z : ℂ) :
    HasDerivAt (fun ℓ : ℝ => (1 : ℂ) - Complex.exp (Complex.I * (ℓ : ℂ) * ((t₀ : ℂ) - z)))
      (Complex.I * (z - t₀)) 0 := by
  have h1 : HasDerivAt (fun ℓ : ℝ => ((ℓ : ℝ) : ℂ)) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).ofReal_comp
  have h2 : HasDerivAt (fun ℓ : ℝ => Complex.I * (ℓ : ℂ) * ((t₀ : ℂ) - z))
      (Complex.I * 1 * ((t₀ : ℂ) - z)) 0 :=
    (h1.const_mul Complex.I).mul_const ((t₀ : ℂ) - z)
  have h3 := h2.cexp
  have h4 := h3.const_sub (1 : ℂ)
  refine h4.congr_deriv ?_
  simp
  ring

/-- **The small-winding limit is the Hadamard atom.**  With the face pinned at `t₀`, the clock's
log-derivative tends to `1/(z − t₀)` as the winding tends to `0⁺`, at every `z` off the real
axis. -/
theorem symClock_logDeriv_small_winding (t₀ : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    Tendsto (fun ℓ : ℝ => logDeriv (symClock (Complex.exp (Complex.I * ℓ * t₀)) ℓ) z)
      (𝓝[>] 0) (𝓝 (1 / (z - t₀))) := by
  set u : ℂ := z - t₀ with hu
  have hu0 : u ≠ 0 := by
    intro h
    have : z.im = 0 := by
      have := congrArg Complex.im h
      simpa [hu, Complex.sub_im] using this
    exact hz this
  -- the difference quotient of `1 − e^{iℓ(t₀−z)}` tends to `i·u`
  have hslope := (hasDerivAt_one_sub_pinned t₀ z).tendsto_slope_zero
  have hslope' : Tendsto (fun ℓ : ℝ =>
      ((ℓ : ℂ))⁻¹ * ((1 : ℂ) - Complex.exp (Complex.I * (ℓ : ℂ) * ((t₀ : ℂ) - z))))
      (𝓝[>] 0) (𝓝 (Complex.I * u)) := by
    have hmono : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
      nhdsWithin_mono 0 (fun x hx => ne_of_gt hx)
    refine (hslope.mono_left hmono).congr' ?_
    filter_upwards with ℓ
    simp [Complex.real_smul]
  -- hence `ℓ/(1 − e^{iℓ(t₀−z)}) → (i·u)⁻¹`
  have hinv : Tendsto (fun ℓ : ℝ =>
      (((ℓ : ℂ))⁻¹ * ((1 : ℂ) - Complex.exp (Complex.I * (ℓ : ℂ) * ((t₀ : ℂ) - z))))⁻¹)
      (𝓝[>] 0) (𝓝 ((Complex.I * u)⁻¹)) :=
    hslope'.inv₀ (mul_ne_zero Complex.I_ne_zero hu0)
  -- the numerator `1 + e^{iℓ(t₀−z)} → 2`
  have hnum : Tendsto (fun ℓ : ℝ => (1 : ℂ) + Complex.exp (Complex.I * (ℓ : ℂ) * ((t₀ : ℂ) - z)))
      (𝓝[>] 0) (𝓝 (2 : ℂ)) := by
    have hc : Continuous (fun ℓ : ℝ => (1 : ℂ) + Complex.exp (Complex.I * (ℓ : ℂ) * ((t₀ : ℂ) - z))) := by
      fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    simpa [one_add_one_eq_two] using this
  -- assemble
  have hprod := ((hnum.const_mul (Complex.I / 2)).mul hinv)
  have hlim : (Complex.I / 2) * 2 * (Complex.I * u)⁻¹ = 1 / u := by
    field_simp
  rw [hlim] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ℓ hℓ
  have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
  have hne1 : Complex.exp (Complex.I * ℓ * (t₀ - z)) ≠ 1 := pinned_disk_point_ne_one hℓ0 hz
  have hne : 1 - Complex.exp (Complex.I * ℓ * t₀) * Complex.exp (-(Complex.I * z * ℓ)) ≠ 0 := by
    rw [pinned_disk_point]
    exact sub_ne_zero.mpr (Ne.symm hne1)
  rw [symClock_logDeriv_face_form _ ℓ z hne, pinned_disk_point]
  have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ0
  have hden : (1 : ℂ) - Complex.exp (Complex.I * ℓ * (t₀ - z)) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne1)
  field_simp

end CriticalLinePhasor.BankLimit

#print axioms CriticalLinePhasor.BankLimit.hasDerivAt_one_sub_pinned
#print axioms CriticalLinePhasor.BankLimit.symClock_logDeriv_small_winding
