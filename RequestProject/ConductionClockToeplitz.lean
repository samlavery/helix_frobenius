import RequestProject.UnitaryClockToeplitz
import Mathlib.Analysis.Complex.Poisson
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Toeplitz positivity of the conduction clock at every degree (ledger 624, stage 3)

The conduction clock `cond_ℓ(s) = 1 − e^{(1−s)ℓ}` (`ℓ = log q`) has its zeros on `Re s = 1`, not on
the line, so its transported measure is not atomic-positive. Its positivity comes from its
**constitution**: on the channel `Re s < ½`, with `v = e^{ℓ(s−½)}` (`|v| < 1`) and the Herglotz
kernel `h(x) = (1+x)/(1−x)`,

  `logDeriv(clock_θ)(s) = −G_{e^{−iθ}}(s)`,  `logDeriv(cond_ℓ)(s) = −G_r(s) − ℓ/2`,  `G_β(s) = (ℓ/2) h(β v)`,

with `r = e^{−ℓ/2} ∈ (0,1)`. Every `s`-jet of `G_β` is `(ℓ/2) ℓ^k D_k(βv)` with `D_k = (x∂_x)^k h`,
holomorphic in `β` on a neighbourhood of the closed unit disc, so **Mathlib's Poisson integral
formula** (`DiffContOnCl.circleAverage_poissonKernel_smul`) evaluates the conduction clock's
Toeplitz form as the Poisson circle average of the unitary clocks' Toeplitz forms (which are `≥ 0`
by stage 2) plus the DC term `(ℓ/|d|)·‖c‖²` contributed by the constant `−ℓ/2`:

* `toeplitzForm_jets_rad_eq`: `T(G_r) = ∮ P_r(β) T(G_β) dβ/2π`;
* `condClock_toeplitz_lower_bound`: `Im T(cond) = 0` and `(ℓ/(1−2σ)) Σ|c_j|² ≤ Re T(cond)`;
* `conductionClock_toeplitz_lower_bound`: the same for the house clock `1 − q^{1−s}`, `ℓ = log q`.

No series is differentiated: the jets are closed forms and the averaging is the Poisson formula.
-/

open Complex Finset Filter Topology Real Metric
open CriticalLinePhasor.ChiralityHB

namespace CriticalLinePhasor.SeatingLedger

/-! ## The Dirichlet variable, the Herglotz kernel and its `x∂_x` iterates -/

/-- `v(s) = e^{ℓ s − ℓ/2} = e^{ℓ(s − ½)}`. -/
noncomputable def dvar (ℓ : ℝ) (s : ℂ) : ℂ := Complex.exp ((ℓ : ℂ) * s - ((ℓ / 2 : ℝ) : ℂ))

theorem norm_dvar_lt_one {ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ} (hs : s.re < 1 / 2) : ‖dvar ℓ s‖ < 1 := by
  unfold dvar
  rw [Complex.norm_exp, Real.exp_lt_one_iff]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero]
  nlinarith

theorem dvar_hasDerivAt (ℓ : ℝ) (s : ℂ) : HasDerivAt (dvar ℓ) ((ℓ : ℂ) * dvar ℓ s) s := by
  unfold dvar
  have h := (((hasDerivAt_id s).const_mul (ℓ : ℂ)).sub_const ((ℓ / 2 : ℝ) : ℂ)).cexp
  exact h.congr_deriv (by simp only [id_eq]; ring)

theorem norm_mul_dvar_lt_one {ℓ : ℝ} (hℓ : 0 < ℓ) {β : ℂ} (hβ : ‖β‖ ≤ 1) {s : ℂ}
    (hs : s.re < 1 / 2) : ‖β * dvar ℓ s‖ < 1 := by
  rw [norm_mul]
  calc ‖β‖ * ‖dvar ℓ s‖ ≤ 1 * ‖dvar ℓ s‖ := mul_le_mul_of_nonneg_right hβ (norm_nonneg _)
    _ < 1 := by rw [one_mul]; exact norm_dvar_lt_one hℓ hs

theorem mul_dvar_mem_ball {ℓ : ℝ} (hℓ : 0 < ℓ) {β : ℂ} (hβ : ‖β‖ ≤ 1) {s : ℂ}
    (hs : s.re < 1 / 2) : β * dvar ℓ s ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball, dist_zero_right]; exact norm_mul_dvar_lt_one hℓ hβ hs

/-- The Herglotz kernel `h(x) = (1+x)/(1−x)`. -/
noncomputable def hker (x : ℂ) : ℂ := (1 + x) / (1 - x)

/-- `D_k = (x ∂_x)^k h`. -/
noncomputable def Dk : ℕ → ℂ → ℂ
  | 0 => hker
  | k + 1 => fun x => x * deriv (Dk k) x

theorem one_sub_ne_zero_of_mem_ball {x : ℂ} (hx : x ∈ ball (0 : ℂ) 1) : 1 - x ≠ 0 := by
  rw [mem_ball, dist_zero_right] at hx
  intro h
  have : x = 1 := by linear_combination -h
  rw [this, norm_one] at hx
  exact lt_irrefl _ hx

theorem hker_analyticOnNhd : AnalyticOnNhd ℂ hker (ball 0 1) := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_ball
  intro x hx
  apply DifferentiableAt.differentiableWithinAt
  unfold hker
  fun_prop (disch := exact one_sub_ne_zero_of_mem_ball hx)

theorem Dk_analyticOnNhd (k : ℕ) : AnalyticOnNhd ℂ (Dk k) (ball 0 1) := by
  induction k with
  | zero => exact hker_analyticOnNhd
  | succ k ih => exact analyticOnNhd_id.mul ih.deriv

/-! ## The Poisson-side clock `G_β` and its jets -/

/-- `G_β(s) = (ℓ/2) h(β v(s))`. -/
noncomputable def Gclock (ℓ : ℝ) (β : ℂ) (s : ℂ) : ℂ := ((ℓ : ℂ) / 2) * hker (β * dvar ℓ s)

/-- **The `s`-jets of `G_β` in closed form**: `∂^k G_β(s) = (ℓ/2) ℓ^k D_k(β v(s))`. -/
theorem Gclock_iteratedDeriv {ℓ : ℝ} (hℓ : 0 < ℓ) {β : ℂ} (hβ : ‖β‖ ≤ 1) (k : ℕ) {s : ℂ}
    (hs : s.re < 1 / 2) :
    iteratedDeriv k (Gclock ℓ β) s = ((ℓ : ℂ) / 2) * (ℓ : ℂ) ^ k * Dk k (β * dvar ℓ s) := by
  induction k generalizing s with
  | zero => simp [Gclock, Dk]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv k (Gclock ℓ β)
        =ᶠ[𝓝 s] fun s => ((ℓ : ℂ) / 2) * (ℓ : ℂ) ^ k * Dk k (β * dvar ℓ s) := by
      filter_upwards [isOpen_channel.mem_nhds hs] with s' hs'
      exact ih hs'
    rw [hev.deriv_eq]
    have hD : HasDerivAt (Dk k) (deriv (Dk k) (β * dvar ℓ s)) (β * dvar ℓ s) :=
      ((Dk_analyticOnNhd k) _ (mul_dvar_mem_ball hℓ hβ hs)).differentiableAt.hasDerivAt
    have hin : HasDerivAt (fun s => β * dvar ℓ s) (β * ((ℓ : ℂ) * dvar ℓ s)) s :=
      (dvar_hasDerivAt ℓ s).const_mul β
    have hfin : HasDerivAt (fun s => ((ℓ : ℂ) / 2) * (ℓ : ℂ) ^ k * Dk k (β * dvar ℓ s))
        (((ℓ : ℂ) / 2) * (ℓ : ℂ) ^ k
          * (deriv (Dk k) (β * dvar ℓ s) * (β * ((ℓ : ℂ) * dvar ℓ s)))) s :=
      (hD.comp s hin).const_mul _
    rw [hfin.deriv]
    simp only [Dk]
    ring

/-! ## The unitary clock and the conduction clock are `−G_β` (up to the DC of the latter) -/

theorem clockS_eq_exp (θ ℓ : ℝ) (s : ℂ) :
    clockS θ ℓ s = Complex.exp ((s - 1 / 2) * ℓ / 2)
      - Complex.exp (I * θ) * Complex.exp (-((s - 1 / 2) * ℓ / 2)) := by
  unfold clockS symClock
  have h : ∀ w : ℂ, I * (-I * w) = w := fun w => by linear_combination (-w) * Complex.I_sq
  rw [h]

theorem clock_alg (E A ℓ : ℂ) (hE : E ≠ 0) (hA : A ≠ 0) (hden : E - A * E⁻¹ ≠ 0)
    (h1v : 1 - A⁻¹ * E ^ 2 ≠ 0) :
    (E * (ℓ / 2) - A * (E⁻¹ * (-(ℓ / 2)))) / (E - A * E⁻¹)
      = -(ℓ / 2 * ((1 + A⁻¹ * E ^ 2) / (1 - A⁻¹ * E ^ 2))) := by
  have key : (E * (ℓ / 2) - A * (E⁻¹ * (-(ℓ / 2)))) * (1 - A⁻¹ * E ^ 2)
      = (-(ℓ / 2 * (1 + A⁻¹ * E ^ 2))) * (E - A * E⁻¹) := by
    field_simp
    ring
  rw [show -(ℓ / 2 * ((1 + A⁻¹ * E ^ 2) / (1 - A⁻¹ * E ^ 2)))
      = (-(ℓ / 2 * (1 + A⁻¹ * E ^ 2))) / (1 - A⁻¹ * E ^ 2) by ring]
  rw [div_eq_div_iff hden h1v]
  exact key

/-- **The unitary clock is `−G_β`** with `β = e^{−iθ}`, on the channel. -/
theorem clockS_logDeriv_eq_Gclock {θ ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ} (hs : s.re < 1 / 2) :
    logDeriv (clockS θ ℓ) s = -Gclock ℓ (Complex.exp (-(I * θ))) s := by
  have hfun : clockS θ ℓ = fun s => Complex.exp ((s - 1 / 2) * ℓ / 2)
      - Complex.exp (I * θ) * Complex.exp (-((s - 1 / 2) * ℓ / 2)) := funext (clockS_eq_exp θ ℓ)
  have h1 : HasDerivAt (fun s : ℂ => (s - 1 / 2) * ℓ / 2) ((ℓ : ℂ) / 2) s := by
    have := (((hasDerivAt_id s).sub_const (1 / 2 : ℂ)).mul_const (ℓ : ℂ)).div_const 2
    exact this.congr_deriv (by ring)
  have hd : HasDerivAt (fun s => Complex.exp ((s - 1 / 2) * ℓ / 2)
      - Complex.exp (I * θ) * Complex.exp (-((s - 1 / 2) * ℓ / 2)))
      (Complex.exp ((s - 1 / 2) * ℓ / 2) * ((ℓ : ℂ) / 2)
        - Complex.exp (I * θ) * (Complex.exp (-((s - 1 / 2) * ℓ / 2)) * -((ℓ : ℂ) / 2))) s :=
    h1.cexp.sub ((h1.neg.cexp).const_mul (Complex.exp (I * θ)))
  have hne : clockS θ ℓ s ≠ 0 := clockS_ne_zero hℓ hs
  have hβ : ‖Complex.exp (-(I * θ))‖ ≤ 1 := by
    rw [show -(I * (θ : ℂ)) = ((-θ : ℝ) : ℂ) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  have h1v : (1 : ℂ) - Complex.exp (-(I * θ)) * dvar ℓ s ≠ 0 :=
    one_sub_ne_zero_of_mem_ball (mul_dvar_mem_ball hℓ hβ hs)
  rw [logDeriv_apply, hfun, hd.deriv]
  rw [hfun] at hne
  beta_reduce at hne ⊢
  unfold Gclock hker
  have hEneg : Complex.exp (-((s - 1 / 2) * ℓ / 2)) = (Complex.exp ((s - 1 / 2) * ℓ / 2))⁻¹ :=
    Complex.exp_neg _
  have hAneg : Complex.exp (-(I * θ)) = (Complex.exp (I * θ))⁻¹ := Complex.exp_neg _
  have hv : dvar ℓ s = (Complex.exp ((s - 1 / 2) * ℓ / 2)) ^ 2 := by
    rw [← Complex.exp_nat_mul]; unfold dvar; congr 1; push_cast; ring
  rw [hEneg] at hne ⊢
  rw [hAneg, hv] at h1v ⊢
  exact clock_alg _ _ _ (Complex.exp_ne_zero _) (Complex.exp_ne_zero _) hne h1v

/-- The conduction clock `1 − e^{(1−s)ℓ}` (`= 1 − q^{1−s}` for `ℓ = log q`). -/
noncomputable def condClock (ℓ : ℝ) (s : ℂ) : ℂ := 1 - Complex.exp ((1 - s) * ℓ)

theorem conductionClock_eq_condClock {q : ℕ} (hq : 1 < q) (s : ℂ) :
    conductionClock q s = condClock (Real.log q) s := by
  unfold conductionClock condClock
  congr 1
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (by omega : q ≠ 0)), Complex.natCast_log]
  congr 1
  ring

/-- The Poisson radius `r = e^{−ℓ/2}`. -/
noncomputable def rad (ℓ : ℝ) : ℂ := ((Real.exp (-ℓ / 2) : ℝ) : ℂ)

theorem norm_rad_le_one {ℓ : ℝ} (hℓ : 0 < ℓ) : ‖rad ℓ‖ ≤ 1 := by
  unfold rad
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by linarith)

theorem norm_rad_lt_one {ℓ : ℝ} (hℓ : 0 < ℓ) : ‖rad ℓ‖ < 1 := by
  unfold rad
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_lt_one_iff.mpr (by linarith)

theorem rad_mem_ball {ℓ : ℝ} (hℓ : 0 < ℓ) : rad ℓ ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball, dist_zero_right]; exact norm_rad_lt_one hℓ

theorem cond_alg (U ℓ : ℂ) (h1 : 1 - U ≠ 0) (h2 : 1 - U⁻¹ ≠ 0) (h3 : U - 1 ≠ 0) (hU : U ≠ 0) :
    U * ℓ / (1 - U) = -(ℓ / 2 * ((1 + U⁻¹) / (1 - U⁻¹))) - ℓ / 2 := by
  have : (1 + U⁻¹) / (1 - U⁻¹) = (U + 1) / (U - 1) := by
    rw [div_eq_div_iff h2 h3]
    field_simp
  rw [this]
  field_simp
  ring

/-- **The conduction clock is `−G_r − ℓ/2`** on the channel: the Poisson barycenter minus its DC. -/
theorem condClock_logDeriv_eq {ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ} (hs : s.re < 1 / 2) :
    logDeriv (condClock ℓ) s = -Gclock ℓ (rad ℓ) s - (ℓ : ℂ) / 2 := by
  have hU0 : Complex.exp ((1 - s) * ℓ) ≠ 0 := Complex.exp_ne_zero _
  have hd : HasDerivAt (condClock ℓ) (Complex.exp ((1 - s) * ℓ) * ℓ) s := by
    have h1 : HasDerivAt (fun s : ℂ => (1 - s) * ℓ) (-ℓ) s := by
      have := ((hasDerivAt_id s).const_sub 1).mul_const (ℓ : ℂ)
      exact this.congr_deriv (by ring)
    have := (hasDerivAt_const s (1 : ℂ)).sub h1.cexp
    unfold condClock
    exact this.congr_deriv (by ring)
  rw [logDeriv_apply, hd.deriv]
  have hr : rad ℓ * dvar ℓ s = (Complex.exp ((1 - s) * ℓ))⁻¹ := by
    unfold rad dvar
    rw [Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  have h2 : (1 : ℂ) - (Complex.exp ((1 - s) * ℓ))⁻¹ ≠ 0 := by
    rw [← hr]; exact one_sub_ne_zero_of_mem_ball (mul_dvar_mem_ball hℓ (norm_rad_le_one hℓ) hs)
  have h1 : (1 : ℂ) - Complex.exp ((1 - s) * ℓ) ≠ 0 := by
    intro h
    have hU1 : Complex.exp ((1 - s) * ℓ) = 1 := by linear_combination -h
    have := congrArg norm hU1
    rw [Complex.norm_exp, norm_one] at this
    have hre : ((1 - s) * (ℓ : ℂ)).re = (1 - s.re) * ℓ := by simp
    rw [hre, Real.exp_eq_one_iff] at this
    nlinarith
  have h3 : Complex.exp ((1 - s) * ℓ) - 1 ≠ 0 := by
    intro h; apply h1; linear_combination -h
  unfold condClock Gclock hker
  rw [hr]
  exact cond_alg _ _ h1 h2 h3 hU0

/-! ## Jets -/

/-- The jets of `F` at `s`: `J_F(m) = (−1)^{m−1}/(m−1)! ∂^{m−1}F(s)` for `m ≥ 1`, `J_F(0) = 0`. -/
noncomputable def jets (F : ℂ → ℂ) (s : ℂ) : ℕ → ℂ
  | 0 => 0
  | m + 1 => (-1) ^ m / (m.factorial : ℂ) * iteratedDeriv m F s

theorem iteratedDeriv_congr_nhds {f g : ℂ → ℂ} {x : ℂ} (h : f =ᶠ[𝓝 x] g) (k : ℕ) :
    iteratedDeriv k f x = iteratedDeriv k g x := by
  rw [← iteratedDerivWithin_univ, ← iteratedDerivWithin_univ]
  exact Filter.EventuallyEq.iteratedDerivWithin_eq (by rwa [nhdsWithin_univ]) h.eq_of_nhds

/-- The unitary clock's jets of stage 2 are the jets of its log-derivative. -/
theorem clockJet_eq_jets {θ ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ} (hs : s.re < 1 / 2) :
    clockJet θ ℓ s = jets (logDeriv (clockS θ ℓ)) s := by
  funext m
  match m with
  | 0 => rfl
  | 1 => simp [clockJet, jets]
  | m + 2 =>
    simp only [jets]
    have h := clockJet_eq_iteratedDeriv (θ := θ) hℓ hs (m := m + 2) (by omega)
    rw [show m + 2 - 1 = m + 1 by omega] at h
    rw [h]
    have hf : ((m + 1).factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have hsq : ((-1 : ℂ) ^ (m + 1)) * (-1) ^ (m + 1) = 1 := by
      rw [← mul_pow]; simp
    rw [show (-1 : ℂ) ^ (m + 1) / ((m + 1).factorial : ℂ)
        * ((-1) ^ (m + 1) * ((m + 1).factorial : ℂ) * clockJet θ ℓ s (m + 2))
        = ((-1 : ℂ) ^ (m + 1) * (-1) ^ (m + 1)) * (((m + 1).factorial : ℂ) / ((m + 1).factorial : ℂ))
          * clockJet θ ℓ s (m + 2) by ring, hsq, div_self hf, one_mul, one_mul]

/-- The jets of the unitary clock are `−` the jets of `G_{e^{−iθ}}`. -/
theorem jets_clockS_eq {θ ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ} (hs : s.re < 1 / 2) :
    jets (logDeriv (clockS θ ℓ)) s = -(jets (Gclock ℓ (Complex.exp (-(I * θ)))) s) := by
  funext m
  cases m with
  | zero => simp [jets]
  | succ m =>
    simp only [jets, Pi.neg_apply]
    have hev : logDeriv (clockS θ ℓ) =ᶠ[𝓝 s] -(Gclock ℓ (Complex.exp (-(I * θ)))) := by
      filter_upwards [isOpen_channel.mem_nhds hs] with s' hs'
      rw [Pi.neg_apply]; exact clockS_logDeriv_eq_Gclock hℓ hs'
    rw [iteratedDeriv_congr_nhds hev, iteratedDeriv_neg]
    ring

/-- The jets of the conduction clock are `−` the jets of `G_r`, plus the DC `−ℓ/2` at `m = 1`. -/
theorem jets_condClock_eq {ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ} (hs : s.re < 1 / 2) :
    jets (logDeriv (condClock ℓ)) s
      = -(jets (Gclock ℓ (rad ℓ)) s) + (fun m => if m = 1 then -(ℓ : ℂ) / 2 else 0) := by
  have hev : logDeriv (condClock ℓ) =ᶠ[𝓝 s] (fun s => -Gclock ℓ (rad ℓ) s - (ℓ : ℂ) / 2) := by
    filter_upwards [isOpen_channel.mem_nhds hs] with s' hs'
    exact condClock_logDeriv_eq hℓ hs'
  funext m
  match m with
  | 0 => simp [jets]
  | 1 =>
    simp only [jets, Pi.add_apply, Pi.neg_apply, iteratedDeriv_zero, pow_zero, Nat.factorial_zero,
      Nat.cast_one, div_one, one_mul, if_true]
    rw [hev.eq_of_nhds]
    ring
  | m + 2 =>
    simp only [jets, Pi.add_apply, Pi.neg_apply]
    rw [if_neg (by omega), add_zero, iteratedDeriv_congr_nhds hev]
    conv_lhs => rw [iteratedDeriv_succ']
    have hderiv : deriv (fun s => -Gclock ℓ (rad ℓ) s - (ℓ : ℂ) / 2) = deriv (-(Gclock ℓ (rad ℓ))) := by
      funext x; exact deriv_sub_const _
    rw [hderiv, ← iteratedDeriv_succ', iteratedDeriv_neg]
    ring

/-! ## Linearity of the form in the jets, and the DC term -/

theorem toeplitzCoeff_neg (d : ℂ) (S : ℕ → ℂ) (k : ℕ) :
    toeplitzCoeff d (-S) k = -toeplitzCoeff d S k := by
  cases k with
  | zero =>
    simp only [toeplitzCoeff, Pi.neg_apply, Complex.neg_re]
    push_cast
    ring
  | succ n => simp only [toeplitzCoeff, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem hermExt_neg (μ : ℕ → ℂ) : hermExt (-μ) = -hermExt μ := by
  funext k
  unfold hermExt
  by_cases hk : 0 ≤ k <;> simp [hk]

theorem toeplitzForm_neg (μ : ℤ → ℂ) {N : ℕ} (c : Fin N → ℂ) :
    toeplitzForm (-μ) c = -toeplitzForm μ c := by
  unfold toeplitzForm
  simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem toeplitzForm_hermExt_add (d : ℂ) (S S' : ℕ → ℂ) {N : ℕ} (c : Fin N → ℂ) :
    toeplitzForm (hermExt (toeplitzCoeff d (S + S'))) c
      = toeplitzForm (hermExt (toeplitzCoeff d S)) c + toeplitzForm (hermExt (toeplitzCoeff d S')) c := by
  rw [show toeplitzCoeff d (S + S') = toeplitzCoeff d S + toeplitzCoeff d S' from
    funext (toeplitzCoeff_add d S S'), hermExt_add, toeplitzForm_add]

theorem toeplitzForm_hermExt_neg (d : ℂ) (S : ℕ → ℂ) {N : ℕ} (c : Fin N → ℂ) :
    toeplitzForm (hermExt (toeplitzCoeff d (-S))) c = -toeplitzForm (hermExt (toeplitzCoeff d S)) c := by
  rw [show toeplitzCoeff d (-S) = -toeplitzCoeff d S from funext (toeplitzCoeff_neg d S),
    hermExt_neg, toeplitzForm_neg]

theorem toeplitzCoeff_dcSeq (d a : ℂ) (k : ℕ) :
    toeplitzCoeff d (fun m => if m = 1 then a else 0) k
      = if k = 0 then 2 * (a.re : ℂ) / d else 0 := by
  cases k with
  | zero => simp [toeplitzCoeff]
  | succ n =>
    simp only [toeplitzCoeff, Nat.succ_ne_zero, if_false]
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    rw [if_neg (by omega)]
    ring

theorem hermExt_delta (a : ℝ) :
    hermExt (fun k : ℕ => if k = 0 then (a : ℂ) else 0)
      = fun m : ℤ => if m = 0 then (a : ℂ) else 0 := by
  funext m
  unfold hermExt
  by_cases hm : 0 ≤ m
  · simp only [if_pos hm]
    by_cases h0 : m = 0
    · subst h0; simp
    · rw [if_neg (by omega : m.toNat ≠ 0), if_neg h0]
  · simp only [if_neg hm]
    rw [if_neg (by omega : (-m).toNat ≠ 0), if_neg (by omega), map_zero]

theorem toeplitzForm_delta (a : ℝ) {N : ℕ} (c : Fin N → ℂ) :
    toeplitzForm (fun m : ℤ => if m = 0 then (a : ℂ) else 0) c
      = ((a * ∑ j : Fin N, Complex.normSq (c j) : ℝ) : ℂ) := by
  unfold toeplitzForm
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_eq_single j]
  · rw [sub_self, if_pos rfl, Complex.normSq_eq_conj_mul_self]; ring
  · intro l _ hlj
    rw [if_neg, mul_zero]
    intro h
    apply hlj
    exact Fin.ext (by exact_mod_cast (sub_eq_zero.mp h).symm)
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **The DC term**: the constant `−ℓ/2` in `S_1` contributes exactly `(ℓ/(1−2σ)) ‖c‖²`. -/
theorem toeplitzForm_hermExt_dc {ℓ : ℝ} {s : ℂ} (hs : s.re < 1 / 2) {N : ℕ} (c : Fin N → ℂ) :
    toeplitzForm (hermExt (toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ)
      (fun m => if m = 1 then -(ℓ : ℂ) / 2 else 0))) c
      = ((ℓ / (1 - 2 * s.re) * ∑ j : Fin N, Complex.normSq (c j) : ℝ) : ℂ) := by
  have h1 : toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (fun m => if m = 1 then -(ℓ : ℂ) / 2 else 0)
      = fun k => if k = 0 then ((ℓ / (1 - 2 * s.re) : ℝ) : ℂ) else 0 := by
    funext k
    rw [toeplitzCoeff_dcSeq]
    by_cases hk : k = 0
    · rw [if_pos hk, if_pos hk]
      have hd : (2 * (s.re : ℂ) - 1) ≠ 0 := by
        have : (2 * s.re - 1 : ℝ) ≠ 0 := by intro h; linarith
        exact_mod_cast this
      have hd' : (1 - 2 * (s.re : ℂ)) ≠ 0 := by
        have : (1 - 2 * s.re : ℝ) ≠ 0 := by intro h; linarith
        exact_mod_cast this
      simp only [Complex.neg_re, Complex.div_ofNat_re, Complex.ofReal_re]
      push_cast
      field_simp
      ring
    · rw [if_neg hk, if_neg hk]
  rw [h1, hermExt_delta, toeplitzForm_delta]

/-! ## The Poisson average -/

/-- The holomorphic half of the Hermitian-extended coefficients of `G_β`. -/
noncomputable def muHol (ℓ : ℝ) (s : ℂ) (β : ℂ) (m : ℤ) : ℂ :=
  if 0 < m then toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (jets (Gclock ℓ β) s) m.toNat
  else if m = 0 then Gclock ℓ β s / ((2 * s.re - 1 : ℝ) : ℂ) else 0

theorem hermExt_jets_eq (ℓ : ℝ) (s β : ℂ) (m : ℤ) :
    hermExt (toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (jets (Gclock ℓ β) s)) m
      = muHol ℓ s β m + (starRingEnd ℂ) (muHol ℓ s β (-m)) := by
  unfold hermExt muHol
  rcases lt_trichotomy m 0 with hm | hm | hm
  · rw [if_neg (not_le.mpr hm), if_neg (not_lt.mpr hm.le), if_neg hm.ne, if_pos (neg_pos.mpr hm)]
    simp
  · subst hm
    simp only [le_refl, if_true, lt_irrefl, if_false, neg_zero, Int.toNat_zero, toeplitzCoeff]
    rw [map_div₀, Complex.conj_ofReal, ← add_div, Complex.add_conj]
    simp [jets]
  · rw [if_pos hm.le, if_pos hm, if_neg (not_lt.mpr (neg_nonpos.mpr hm.le)), if_neg (by omega)]
    simp

/-- The holomorphic and anti-holomorphic halves of the Toeplitz form of `G_β`. -/
noncomputable def Hfun (ℓ : ℝ) (s : ℂ) {N : ℕ} (c : Fin N → ℂ) (β : ℂ) : ℂ :=
  ∑ j : Fin N, ∑ l : Fin N, (starRingEnd ℂ) (c j) * c l * muHol ℓ s β ((j : ℤ) - (l : ℤ))

noncomputable def Kfun (ℓ : ℝ) (s : ℂ) {N : ℕ} (c : Fin N → ℂ) (β : ℂ) : ℂ :=
  ∑ j : Fin N, ∑ l : Fin N, c j * (starRingEnd ℂ) (c l) * muHol ℓ s β ((l : ℤ) - (j : ℤ))

theorem toeplitzForm_jets_eq (ℓ : ℝ) (s : ℂ) {N : ℕ} (c : Fin N → ℂ) (β : ℂ) :
    toeplitzForm (hermExt (toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (jets (Gclock ℓ β) s))) c
      = Hfun ℓ s c β + (starRingEnd ℂ) (Kfun ℓ s c β) := by
  unfold toeplitzForm Hfun Kfun
  simp only [map_sum, map_mul, Complex.conj_conj]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [hermExt_jets_eq, show -((j : ℤ) - (l : ℤ)) = (l : ℤ) - (j : ℤ) by ring]
  ring

section Holomorphy
variable {ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ} (hs : s.re < 1 / 2)
include hℓ hs

theorem Gclock_differentiableOn :
    DifferentiableOn ℂ (fun β => Gclock ℓ β s) (closedBall 0 1) := by
  intro β hβ
  rw [mem_closedBall_zero_iff] at hβ
  have hx := mul_dvar_mem_ball hℓ hβ hs
  have h1 : DifferentiableAt ℂ hker (β * dvar ℓ s) := (hker_analyticOnNhd _ hx).differentiableAt
  have h2 : DifferentiableAt ℂ (fun β : ℂ => β * dvar ℓ s) β := differentiableAt_id.mul_const _
  exact ((h1.comp β h2).const_mul _).differentiableWithinAt

theorem iteratedDeriv_Gclock_differentiableOn (k : ℕ) :
    DifferentiableOn ℂ (fun β => iteratedDeriv k (Gclock ℓ β) s) (closedBall 0 1) := by
  have hD : DifferentiableOn ℂ (fun β => ((ℓ : ℂ) / 2) * (ℓ : ℂ) ^ k * Dk k (β * dvar ℓ s))
      (closedBall 0 1) := by
    intro β hβ
    rw [mem_closedBall_zero_iff] at hβ
    have hx := mul_dvar_mem_ball hℓ hβ hs
    have h1 : DifferentiableAt ℂ (Dk k) (β * dvar ℓ s) := (Dk_analyticOnNhd k _ hx).differentiableAt
    have h2 : DifferentiableAt ℂ (fun β : ℂ => β * dvar ℓ s) β := differentiableAt_id.mul_const _
    exact ((h1.comp β h2).const_mul _).differentiableWithinAt
  refine hD.congr (fun β hβ => ?_)
  rw [mem_closedBall_zero_iff] at hβ
  exact Gclock_iteratedDeriv hℓ hβ k hs

theorem jets_Gclock_differentiableOn (m : ℕ) :
    DifferentiableOn ℂ (fun β => jets (Gclock ℓ β) s m) (closedBall 0 1) := by
  cases m with
  | zero => simp only [jets]; exact differentiableOn_const _
  | succ m =>
    simp only [jets]
    exact (iteratedDeriv_Gclock_differentiableOn hℓ hs m).const_mul _

theorem toeplitzCoeff_jets_differentiableOn {k : ℕ} (hk : 1 ≤ k) :
    DifferentiableOn ℂ
      (fun β => toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (jets (Gclock ℓ β) s) k) (closedBall 0 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  simp only [toeplitzCoeff]
  apply DifferentiableOn.fun_sum
  intro i _
  exact (jets_Gclock_differentiableOn hℓ hs _).const_mul _

theorem muHol_differentiableOn (m : ℤ) :
    DifferentiableOn ℂ (fun β => muHol ℓ s β m) (closedBall 0 1) := by
  unfold muHol
  by_cases h1 : 0 < m
  · simp only [if_pos h1]
    exact toeplitzCoeff_jets_differentiableOn hℓ hs (by omega)
  · simp only [if_neg h1]
    by_cases h2 : m = 0
    · simp only [if_pos h2]
      exact (Gclock_differentiableOn hℓ hs).div_const _
    · simp only [if_neg h2]
      exact differentiableOn_const _

theorem Hfun_differentiableOn {N : ℕ} (c : Fin N → ℂ) :
    DifferentiableOn ℂ (Hfun ℓ s c) (closedBall 0 1) := by
  unfold Hfun
  apply DifferentiableOn.fun_sum
  intro j _
  apply DifferentiableOn.fun_sum
  intro l _
  exact (muHol_differentiableOn hℓ hs _).const_mul _

theorem Kfun_differentiableOn {N : ℕ} (c : Fin N → ℂ) :
    DifferentiableOn ℂ (Kfun ℓ s c) (closedBall 0 1) := by
  unfold Kfun
  apply DifferentiableOn.fun_sum
  intro j _
  apply DifferentiableOn.fun_sum
  intro l _
  exact (muHol_differentiableOn hℓ hs _).const_mul _

end Holomorphy

theorem continuousOn_poissonKernel_sphere {r : ℂ} (hr : ‖r‖ < 1) :
    ContinuousOn (poissonKernel 0 r) (sphere (0 : ℂ) 1) := by
  have : poissonKernel 0 r
      = fun z => (‖z - 0‖ ^ 2 - ‖r - 0‖ ^ 2) / ‖(z - 0) - (r - 0)‖ ^ 2 := funext (poissonKernel_def 0 r)
  rw [this]
  apply ContinuousOn.div (by fun_prop) (by fun_prop)
  intro z hz
  rw [mem_sphere_zero_iff_norm] at hz
  have hne : z - 0 - (r - 0) ≠ 0 := by
    rw [sub_zero, sub_zero, sub_ne_zero]
    intro h
    rw [← h, hz] at hr
    exact lt_irrefl _ hr
  exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)

theorem poissonKernel_nonneg_sphere {r : ℂ} (hr : ‖r‖ < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ poissonKernel 0 r z := by
  rw [poissonKernel_def, sub_zero, sub_zero, hz]
  apply div_nonneg _ (sq_nonneg _)
  nlinarith [norm_nonneg r]

theorem circleIntegrable_poisson_smul {r : ℂ} (hr : ‖r‖ < 1) {f : ℂ → ℂ}
    (hf : ContinuousOn f (sphere (0 : ℂ) 1)) :
    CircleIntegrable (fun β => poissonKernel 0 r β • f β) 0 1 :=
  ContinuousOn.circleIntegrable zero_le_one ((continuousOn_poissonKernel_sphere hr).smul hf)

section Average
variable {ℓ : ℝ} (hℓ : 0 < ℓ) {s : ℂ} (hs : s.re < 1 / 2) {N : ℕ} (c : Fin N → ℂ)
include hℓ hs

theorem Hfun_continuousOn : ContinuousOn (Hfun ℓ s c) (sphere (0 : ℂ) 1) :=
  (Hfun_differentiableOn hℓ hs c).continuousOn.mono sphere_subset_closedBall

theorem Kfun_continuousOn : ContinuousOn (Kfun ℓ s c) (sphere (0 : ℂ) 1) :=
  (Kfun_differentiableOn hℓ hs c).continuousOn.mono sphere_subset_closedBall

theorem poisson_Hfun :
    Real.circleAverage (fun β => poissonKernel 0 (rad ℓ) β • Hfun ℓ s c β) 0 1
      = Hfun ℓ s c (rad ℓ) := by
  have hH : DiffContOnCl ℂ (Hfun ℓ s c) (ball 0 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact Hfun_differentiableOn hℓ hs c
  exact hH.circleAverage_poissonKernel_smul (rad_mem_ball hℓ)

theorem poisson_Kfun :
    Real.circleAverage (fun β => poissonKernel 0 (rad ℓ) β • Kfun ℓ s c β) 0 1
      = Kfun ℓ s c (rad ℓ) := by
  have hK : DiffContOnCl ℂ (Kfun ℓ s c) (ball 0 1) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball (0 : ℂ) one_ne_zero]
    exact Kfun_differentiableOn hℓ hs c
  exact hK.circleAverage_poissonKernel_smul (rad_mem_ball hℓ)

theorem poisson_conj_Kfun :
    Real.circleAverage (fun β => poissonKernel 0 (rad ℓ) β • (starRingEnd ℂ) (Kfun ℓ s c β)) 0 1
      = (starRingEnd ℂ) (Kfun ℓ s c (rad ℓ)) := by
  have hint : CircleIntegrable (fun β => poissonKernel 0 (rad ℓ) β • Kfun ℓ s c β) 0 1 :=
    circleIntegrable_poisson_smul (norm_rad_lt_one hℓ) (Kfun_continuousOn hℓ hs c)
  have e : (fun β => poissonKernel 0 (rad ℓ) β • (starRingEnd ℂ) (Kfun ℓ s c β))
      = (Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ (fun β => poissonKernel 0 (rad ℓ) β • Kfun ℓ s c β) := by
    funext β
    simp [Complex.real_smul, map_mul, Complex.conj_ofReal]
  rw [e, (Complex.conjCLE : ℂ →L[ℝ] ℂ).circleAverage_comp_comm hint, poisson_Kfun hℓ hs c]
  simp

/-- **The Toeplitz form of `G_r` is the Poisson average of the Toeplitz forms of `G_β`, `|β| = 1`.** -/
theorem toeplitzForm_jets_rad_eq :
    toeplitzForm (hermExt (toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (jets (Gclock ℓ (rad ℓ)) s))) c
      = Real.circleAverage (fun β => poissonKernel 0 (rad ℓ) β
          • toeplitzForm (hermExt (toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (jets (Gclock ℓ β) s))) c)
          0 1 := by
  have e : (fun β => poissonKernel 0 (rad ℓ) β
      • toeplitzForm (hermExt (toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (jets (Gclock ℓ β) s))) c)
      = fun β => poissonKernel 0 (rad ℓ) β • Hfun ℓ s c β
          + poissonKernel 0 (rad ℓ) β • (starRingEnd ℂ) (Kfun ℓ s c β) := by
    funext β
    rw [toeplitzForm_jets_eq, smul_add]
  have hint1 : CircleIntegrable (fun β => poissonKernel 0 (rad ℓ) β • Hfun ℓ s c β) 0 1 :=
    circleIntegrable_poisson_smul (norm_rad_lt_one hℓ) (Hfun_continuousOn hℓ hs c)
  have hint2 : CircleIntegrable
      (fun β => poissonKernel 0 (rad ℓ) β • (starRingEnd ℂ) (Kfun ℓ s c β)) 0 1 :=
    circleIntegrable_poisson_smul (norm_rad_lt_one hℓ)
      (Complex.continuous_conj.comp_continuousOn (Kfun_continuousOn hℓ hs c))
  rw [toeplitzForm_jets_eq, e, Real.circleAverage_fun_add hint1 hint2,
    poisson_Hfun hℓ hs c, poisson_conj_Kfun hℓ hs c]

/-- On the unit circle, `T(G_β)` is minus the Toeplitz form of a unitary clock: real and `≤ 0`. -/
theorem toeplitzForm_jets_circle {β : ℂ} (hβ : ‖β‖ = 1) :
    (toeplitzForm (hermExt (toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (jets (Gclock ℓ β) s))) c).im = 0 ∧
    (toeplitzForm (hermExt (toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (jets (Gclock ℓ β) s))) c).re ≤ 0 := by
  have hβ' : β = Complex.exp (-(I * ((-Complex.arg β : ℝ) : ℂ))) := by
    conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I β]
    rw [hβ, Complex.ofReal_one, one_mul]
    congr 1
    push_cast
    ring
  have hjets := jets_clockS_eq hℓ hs (θ := -Complex.arg β)
  rw [← hβ'] at hjets
  have hcj := clockJet_eq_jets hℓ hs (θ := -Complex.arg β)
  have key : toeplitzForm (hermExt (toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (jets (Gclock ℓ β) s))) c
      = -toeplitzForm (hermExt (toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ)
          (clockJet (-Complex.arg β) ℓ s))) c := by
    rw [hcj, hjets, toeplitzForm_hermExt_neg, neg_neg]
  obtain ⟨him, hre⟩ := unitaryClock_toeplitz_psd hℓ hs (θ := -Complex.arg β) c
  rw [key, Complex.neg_im, Complex.neg_re, him]
  exact ⟨neg_zero, by linarith⟩

theorem toeplitzForm_jets_continuousOn :
    ContinuousOn (fun β =>
      toeplitzForm (hermExt (toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (jets (Gclock ℓ β) s))) c)
      (sphere (0 : ℂ) 1) := by
  have e : (fun β =>
      toeplitzForm (hermExt (toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (jets (Gclock ℓ β) s))) c)
      = fun β => Hfun ℓ s c β + (starRingEnd ℂ) (Kfun ℓ s c β) := funext (toeplitzForm_jets_eq ℓ s c)
  rw [e]
  exact (Hfun_continuousOn hℓ hs c).add
    (Complex.continuous_conj.comp_continuousOn (Kfun_continuousOn hℓ hs c))

/-- **Toeplitz positivity of the conduction clock at every degree, with the DC lower bound.**
For every anchor on the channel, every degree `N` and every `c : Fin N → ℂ`, the Toeplitz form of the
conduction clock's coefficients is real and `≥ (ℓ/(1−2σ)) Σ_j |c_j|²`. -/
theorem condClock_toeplitz_lower_bound :
    (toeplitzForm (hermExt (toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ)
      (jets (logDeriv (condClock ℓ)) s))) c).im = 0 ∧
    ℓ / (1 - 2 * s.re) * ∑ j : Fin N, Complex.normSq (c j)
      ≤ (toeplitzForm (hermExt (toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ)
          (jets (logDeriv (condClock ℓ)) s))) c).re := by
  rw [jets_condClock_eq hℓ hs, toeplitzForm_hermExt_add, toeplitzForm_hermExt_neg,
    toeplitzForm_hermExt_dc hs, toeplitzForm_jets_rad_eq hℓ hs c]
  set T : ℂ → ℂ := fun β =>
    toeplitzForm (hermExt (toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ) (jets (Gclock ℓ β) s))) c with hT
  have hint : CircleIntegrable (fun β => poissonKernel 0 (rad ℓ) β • T β) 0 1 :=
    circleIntegrable_poisson_smul (norm_rad_lt_one hℓ) (toeplitzForm_jets_continuousOn hℓ hs c)
  have hre : (Real.circleAverage (fun β => poissonKernel 0 (rad ℓ) β • T β) 0 1).re
      = Real.circleAverage (fun β => poissonKernel 0 (rad ℓ) β * (T β).re) 0 1 := by
    rw [← Complex.reCLM_apply, ← Complex.reCLM.circleAverage_comp_comm hint]
    congr 1
    funext β
    simp [Complex.real_smul]
  have him : (Real.circleAverage (fun β => poissonKernel 0 (rad ℓ) β • T β) 0 1).im = 0 := by
    rw [← Complex.imCLM_apply, ← Complex.imCLM.circleAverage_comp_comm hint]
    rw [Real.circleAverage_congr_sphere (f₂ := fun _ => (0 : ℝ)), Real.circleAverage_const]
    intro β hβ
    rw [abs_one, mem_sphere_zero_iff_norm] at hβ
    simp only [Function.comp_apply, Complex.imCLM_apply, Complex.real_smul, Complex.im_ofReal_mul]
    rw [(toeplitzForm_jets_circle hℓ hs c hβ).1, mul_zero]
  have hnonneg : 0 ≤ -(Real.circleAverage (fun β => poissonKernel 0 (rad ℓ) β • T β) 0 1).re := by
    rw [hre]
    have e : (fun β => poissonKernel 0 (rad ℓ) β * (T β).re)
        = (-1 : ℝ) • fun β => poissonKernel 0 (rad ℓ) β * (-(T β).re) := by
      funext β; simp
    rw [e, Real.circleAverage_smul, smul_eq_mul, neg_mul, one_mul, neg_neg]
    apply Real.circleAverage_nonneg_of_nonneg
    intro β hβ
    rw [abs_one, mem_sphere_zero_iff_norm] at hβ
    exact mul_nonneg (poissonKernel_nonneg_sphere (norm_rad_lt_one hℓ) hβ)
      (neg_nonneg.mpr (toeplitzForm_jets_circle hℓ hs c hβ).2)
  refine ⟨?_, ?_⟩
  · rw [Complex.add_im, Complex.neg_im, him, Complex.ofReal_im]; ring
  · rw [Complex.add_re, Complex.neg_re, Complex.ofReal_re]; linarith

end Average

/-- **The house conduction clock `1 − q^{1−s}`**: Toeplitz positivity at every degree with the DC
lower bound `(log q/(1−2σ)) Σ|c_j|²`. -/
theorem conductionClock_toeplitz_lower_bound {q : ℕ} (hq : 1 < q) {s : ℂ} (hs : s.re < 1 / 2)
    {N : ℕ} (c : Fin N → ℂ) :
    (toeplitzForm (hermExt (toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ)
      (jets (logDeriv (conductionClock q)) s))) c).im = 0 ∧
    Real.log q / (1 - 2 * s.re) * ∑ j : Fin N, Complex.normSq (c j)
      ≤ (toeplitzForm (hermExt (toeplitzCoeff ((2 * s.re - 1 : ℝ) : ℂ)
          (jets (logDeriv (conductionClock q)) s))) c).re := by
  have hℓ : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have e : conductionClock q = condClock (Real.log q) := funext (conductionClock_eq_condClock hq)
  rw [e]
  exact condClock_toeplitz_lower_bound hℓ hs c

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.Gclock_iteratedDeriv
#print axioms CriticalLinePhasor.SeatingLedger.clockS_logDeriv_eq_Gclock
#print axioms CriticalLinePhasor.SeatingLedger.condClock_logDeriv_eq
#print axioms CriticalLinePhasor.SeatingLedger.toeplitzForm_jets_rad_eq
#print axioms CriticalLinePhasor.SeatingLedger.condClock_toeplitz_lower_bound
#print axioms CriticalLinePhasor.SeatingLedger.conductionClock_toeplitz_lower_bound
