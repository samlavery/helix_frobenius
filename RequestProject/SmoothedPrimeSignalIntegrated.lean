import RequestProject.SmoothedPrimeSignalTheta

/-!
# The integrated form: the positive-kernel one-sided bound (ledger 920)

`V(y) = e^{−y/2} ∫_{s ≤ y} e^{s/2} W(s) ds`.  In the multiplicative chart `x = e^y`,
`e^{y/2} V(y) = ∫_{s ≤ log x} ψ_K(e^s) ds = ∫_0^x ψ_K(t) dt/t`, the Riesz-type integral of the smoothed Chebyshev sum;
against `ψ(t) − t` its kernel is positive (ledger 919).

* `integral_V_mul_cexp`: the transform of `V` is `K̃(z) L(Λ, ½ + z)/(z + ½)` — one Fubini swap from `W`'s;
* `no_zero_of_lowerBoundInt`, `abs_re_sub_half_le_of_lowerBoundInt`, `riemannHypothesis_of_forall_lowerBoundInt`:
  the θ-dial for the integrated signal, with kernel `J̃(z) = K̃(z)/(z + ½)` (zero-free on `Re z > −½`);
* `LowerBoundTheta.toInt`: the integrated input is implied by the `ψ_K` input.

No `sorry`, no `axiom`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ArithmeticFunction.vonMangoldt LSeries.notation

noncomputable section

namespace SmoothedPrimeSignal

/-! ## 1. The integrated signal -/

/-- The integrand `e^{s/2} W(s)`; in `x = e^s` it is `ψ_K(x)`. -/
def P (s : ℝ) : ℝ := Real.exp (s / 2) * W s

theorem P_nonneg (s : ℝ) : 0 ≤ P s := mul_nonneg (Real.exp_pos _).le (W_nonneg s)

theorem continuous_P : Continuous P :=
  (Real.continuous_exp.comp (continuous_id.div_const 2)).mul continuous_W

theorem P_eq_psiK (s : ℝ) : P s = psiK (Real.exp s) := by
  rw [psiK_eq (Real.exp_pos s), Real.log_exp, P, ← exp_half_log (Real.exp_pos s), Real.log_exp]

theorem integrableOn_P_Iic (y : ℝ) : IntegrableOn P (Iic y) := by
  have hdom : IntegrableOn (fun s => Real.exp (3 / 2 * y) * (W s * Real.exp (-1 * s))) (Iic y) :=
    ((integrable_W_mul_exp (by norm_num : (1 : ℝ) / 2 < 1)).const_mul _).integrableOn
  refine hdom.mono' continuous_P.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Iic).2 (Eventually.of_forall fun s hs => ?_)
  have hs' : s ≤ y := hs
  rw [Real.norm_eq_abs, abs_of_nonneg (P_nonneg s)]
  have h1 : Real.exp (s / 2) ≤ Real.exp (3 / 2 * y) * Real.exp (-1 * s) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  calc P s = Real.exp (s / 2) * W s := rfl
    _ ≤ (Real.exp (3 / 2 * y) * Real.exp (-1 * s)) * W s := mul_le_mul_of_nonneg_right h1 (W_nonneg s)
    _ = Real.exp (3 / 2 * y) * (W s * Real.exp (-1 * s)) := by ring

/-- **The integrated signal** `V(y) = e^{−y/2} ∫_{s ≤ y} e^{s/2} W(s) ds`. -/
def V (y : ℝ) : ℝ := Real.exp (-(y / 2)) * ∫ s in Iic y, P s

theorem V_nonneg (y : ℝ) : 0 ≤ V y :=
  mul_nonneg (Real.exp_pos _).le (setIntegral_nonneg measurableSet_Iic fun s _ => P_nonneg s)

theorem exp_mul_V (y : ℝ) : Real.exp (y / 2) * V y = ∫ s in Iic y, P s := by
  rw [V, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]

/-- **The x-chart reading**: `e^{y/2} V(y) = ∫_{s ≤ y} ψ_K(e^s) ds`. -/
theorem exp_mul_V_eq_integral_psiK (y : ℝ) :
    Real.exp (y / 2) * V y = ∫ s in Iic y, psiK (Real.exp s) := by
  rw [exp_mul_V]
  exact setIntegral_congr_fun measurableSet_Iic (fun s _ => P_eq_psiK s)

theorem integral_Iic_P_eq (y : ℝ) :
    ∫ s in Iic y, P s = (∫ s in Iic 0, P s) + ∫ s in (0 : ℝ)..y, P s := by
  rw [← intervalIntegral.integral_Iic_sub_Iic (integrableOn_P_Iic 0) (integrableOn_P_Iic y)]
  ring

theorem continuous_V : Continuous V := by
  have h : Continuous fun y => ∫ s in Iic y, P s := by
    have h' : (fun y => ∫ s in Iic y, P s) = fun y => (∫ s in Iic 0, P s) + ∫ s in (0 : ℝ)..y, P s :=
      funext integral_Iic_P_eq
    rw [h']
    exact continuous_const.add (intervalIntegral.continuous_primitive
      (fun a b => continuous_P.intervalIntegrable a b) 0)
  exact (Real.continuous_exp.comp (continuous_id.div_const 2).neg).mul h

/-! ### The left tail is Gaussian -/

/-- `∫ e^{t/2} e^{−t²} dt = D`. -/
theorem integral_exp_half_mul_K : ∫ t : ℝ, Real.exp (t / 2) * K t = D := by
  have h := integral_K_mul_cexp (-(1 / 2) : ℂ)
  have hKt : Kt (-(1 / 2)) = (D : ℂ) := by
    rw [← Kt_half]
    unfold Kt
    congr 2
    ring
  rw [hKt] at h
  have h2 : (fun x : ℝ => ((K x : ℝ) : ℂ) * cexp (-(-(1 / 2) : ℂ) * x))
      = fun x : ℝ => ((Real.exp (x / 2) * K x : ℝ) : ℂ) := by
    funext x
    rw [Complex.ofReal_mul, Complex.ofReal_exp, mul_comm (cexp _) _]
    congr 2
    push_cast
    ring
  rw [h2, integral_complex_ofReal] at h
  exact_mod_cast h

theorem integrable_exp_half_mul_K : Integrable (fun t : ℝ => Real.exp (t / 2) * K t) := by
  refine (integrable_K_mul_exp (-(1 / 2))).congr (Eventually.of_forall fun t => ?_)
  simp only
  rw [mul_comm, show -(-(1 / 2) : ℝ) * t = t / 2 by ring]

/-- The tail constant of `W_le_of_nonpos`. -/
def Mtail : ℝ := ∑' n : ℕ, Real.exp (9 / 4 + 3 * 0) * (n : ℝ) ^ (-(5 / 2) : ℝ)

theorem Mtail_nonneg : 0 ≤ Mtail := tsum_nonneg fun n => by positivity

theorem K_le_mul {s y : ℝ} (hsy : s ≤ y) (hy : y ≤ 0) : K s ≤ K y * K (s - y) := by
  unfold K
  rw [← Real.exp_add]
  exact Real.exp_le_exp.2 (by nlinarith)

/-- **On `(−∞, 0]` the integrated signal is Gaussian-small**: `V(y) ≤ M D e^{−y²}`. -/
theorem V_le_of_nonpos {y : ℝ} (hy : y ≤ 0) : V y ≤ Mtail * D * K y := by
  have hint : Integrable (fun s => Real.exp ((s - y) / 2) * K (s - y)) :=
    integrable_exp_half_mul_K.comp_sub_right y
  have hA : 0 ≤ Mtail * (Real.exp (y / 2) * K y) := by
    have := Mtail_nonneg
    unfold K
    positivity
  have h1 : ∫ s in Iic y, P s
      ≤ ∫ s in Iic y, Mtail * (Real.exp (y / 2) * K y) * (Real.exp ((s - y) / 2) * K (s - y)) := by
    refine setIntegral_mono_on (integrableOn_P_Iic y) (hint.const_mul _).integrableOn measurableSet_Iic
      (fun s hs => ?_)
    have hs' : s ≤ y := hs
    have hW : W s ≤ Mtail * K s := W_le_of_nonpos (hs'.trans hy)
    have hK := K_le_mul hs' hy
    have hsplit : Real.exp (s / 2) = Real.exp (y / 2) * Real.exp ((s - y) / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc P s = Real.exp (s / 2) * W s := rfl
      _ ≤ Real.exp (s / 2) * (Mtail * K s) := mul_le_mul_of_nonneg_left hW (Real.exp_pos _).le
      _ ≤ Real.exp (s / 2) * (Mtail * (K y * K (s - y))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hK Mtail_nonneg) (Real.exp_pos _).le
      _ = Mtail * (Real.exp (y / 2) * K y) * (Real.exp ((s - y) / 2) * K (s - y)) := by
          rw [hsplit]
          ring
  have h2 : ∫ s in Iic y, Mtail * (Real.exp (y / 2) * K y) * (Real.exp ((s - y) / 2) * K (s - y))
      ≤ Mtail * (Real.exp (y / 2) * K y) * D := by
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ hA
    calc ∫ s in Iic y, Real.exp ((s - y) / 2) * K (s - y)
        ≤ ∫ s, Real.exp ((s - y) / 2) * K (s - y) :=
          setIntegral_le_integral hint (Eventually.of_forall fun s => by unfold K; positivity)
      _ = D := by
          rw [integral_sub_right_eq_self (fun t => Real.exp (t / 2) * K t) y]
          exact integral_exp_half_mul_K
  have hprod : Real.exp (-(y / 2)) * Real.exp (y / 2) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc V y = Real.exp (-(y / 2)) * ∫ s in Iic y, P s := rfl
    _ ≤ Real.exp (-(y / 2)) * (Mtail * (Real.exp (y / 2) * K y) * D) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos _).le
    _ = (Real.exp (-(y / 2)) * Real.exp (y / 2)) * (Mtail * D * K y) := by ring
    _ = Mtail * D * K y := by rw [hprod, one_mul]

/-- The left tail `E_V(z) = ∫_{y < 0} V(y) e^{−zy} dy`. -/
def EV (z : ℂ) : ℂ := LandauLaplace.laplace (Iio 0) V z

theorem integrableOn_V_Iio (σ : ℝ) : IntegrableOn (fun y => V y * Real.exp (-σ * y)) (Iio 0) := by
  have hdom : IntegrableOn (fun y => Mtail * D * (K y * Real.exp (-σ * y))) (Iio 0) :=
    ((integrable_K_mul_exp σ).const_mul _).integrableOn
  refine hdom.mono' ((continuous_V.mul
    (Real.continuous_exp.comp (continuous_const.mul continuous_id))).aestronglyMeasurable) ?_
  refine (ae_restrict_iff' measurableSet_Iio).2 (Eventually.of_forall fun y hy => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (V_nonneg y) (Real.exp_pos _).le)]
  have h := V_le_of_nonpos (le_of_lt hy)
  calc V y * Real.exp (-σ * y) ≤ (Mtail * D * K y) * Real.exp (-σ * y) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = Mtail * D * (K y * Real.exp (-σ * y)) := by ring

/-- **The left tail is entire.** -/
theorem differentiable_EV : Differentiable ℂ EV := by
  intro z
  have h := LandauLaplace.differentiableOn_laplace (Iio 0) V (z.re - 1)
    (fun σ _ => integrableOn_V_Iio σ)
  exact h.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (by simp only [mem_ofPred_eq]; linarith))

/-! ## 2. The transform of the integrated signal (one Fubini swap) -/

theorem integral_Ioi_exp_neg_mul (b c : ℝ) (hb : 0 < b) :
    ∫ y in Ioi c, Real.exp (-b * y) = Real.exp (-b * c) / b := by
  have h := integral_exp_mul_complex_Ioi (a := ((-b : ℝ) : ℂ)) (by simpa using hb) c
  have h2 : (fun y : ℝ => cexp (((-b : ℝ) : ℂ) * y)) = fun y : ℝ => ((Real.exp (-b * y) : ℝ) : ℂ) := by
    funext y
    push_cast
    ring_nf
  rw [h2, integral_complex_ofReal] at h
  have h3 : -cexp (((-b : ℝ) : ℂ) * c) / ((-b : ℝ) : ℂ) = ((Real.exp (-b * c) / b : ℝ) : ℂ) := by
    push_cast
    rw [neg_div, div_neg, neg_neg]
  rw [h3] at h
  exact_mod_cast h

/-- The region `s ≤ y`. -/
def Sle : Set (ℝ × ℝ) := {q | q.1 ≤ q.2}

theorem measurableSet_Sle : MeasurableSet Sle := measurableSet_le measurable_fst measurable_snd

/-- The real Fubini integrand `1_{s ≤ y} P(s) e^{−(σ+½) y}`. -/
def Freal (σ : ℝ) : ℝ × ℝ → ℝ := Sle.indicator (fun q => P q.1 * Real.exp (-(σ + 1 / 2) * q.2))

theorem Freal_apply (σ s y : ℝ) :
    Freal σ (s, y) = (Ici s).indicator (fun y => P s * Real.exp (-(σ + 1 / 2) * y)) y := by
  simp only [Freal, Sle, Set.indicator_apply, mem_setOf_eq, mem_Ici]

theorem Freal_apply' (σ s y : ℝ) :
    Freal σ (s, y) = (Iic y).indicator (fun s => P s * Real.exp (-(σ + 1 / 2) * y)) s := by
  simp only [Freal, Sle, Set.indicator_apply, mem_setOf_eq, mem_Iic]

theorem Freal_nonneg (σ : ℝ) (q : ℝ × ℝ) : 0 ≤ Freal σ q :=
  Set.indicator_nonneg (fun q _ => mul_nonneg (P_nonneg _) (Real.exp_pos _).le) q

theorem integral_Freal_right (σ : ℝ) (hσ : -(1 / 2) < σ) (s : ℝ) :
    ∫ y, Freal σ (s, y) = W s * Real.exp (-σ * s) / (σ + 1 / 2) := by
  simp_rw [Freal_apply]
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul,
    integral_Ioi_exp_neg_mul (σ + 1 / 2) s (by linarith), P]
  rw [show -(σ + 1 / 2) * s = s / 2 * (-1) + -σ * s by ring, Real.exp_add,
    show s / 2 * (-1) = -(s / 2) by ring, Real.exp_neg]
  field_simp

theorem integrable_Freal (σ : ℝ) (hσ : 1 / 2 < σ) : Integrable (Freal σ) (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable (Freal σ) (volume.prod volume) :=
    ((continuous_P.comp continuous_fst).mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_snd))).aestronglyMeasurable.indicator measurableSet_Sle
  refine (integrable_prod_iff hmeas).2 ⟨Eventually.of_forall fun s => ?_, ?_⟩
  · simp_rw [Freal_apply]
    refine (integrable_indicator_iff measurableSet_Ici).2 ?_
    exact (((exp_neg_integrableOn_Ioi s (by linarith : (0 : ℝ) < σ + 1 / 2)).congr_set_ae
      Ioi_ae_eq_Ici.symm).const_mul (P s))
  · have heq : (fun s => ∫ y, ‖Freal σ (s, y)‖) = fun s => W s * Real.exp (-σ * s) / (σ + 1 / 2) := by
      funext s
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (Freal_nonneg σ _)]
      exact integral_Freal_right σ (by linarith) s
    rw [heq]
    exact (integrable_W_mul_exp hσ).div_const _

theorem integral_Freal_left (σ y : ℝ) :
    ∫ s, Freal σ (s, y) = V y * Real.exp (-σ * y) := by
  simp_rw [Freal_apply']
  rw [integral_indicator measurableSet_Iic, integral_mul_const, ← exp_mul_V, mul_comm (Real.exp _),
    mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Convergence**: `V(y) e^{−σy}` is integrable on `ℝ` for every `σ > ½`. -/
theorem integrable_V_mul_exp {σ : ℝ} (hσ : 1 / 2 < σ) :
    Integrable (fun y => V y * Real.exp (-σ * y)) := by
  have h := (integrable_Freal σ hσ).integral_prod_right
  refine h.congr (Eventually.of_forall fun y => ?_)
  exact integral_Freal_left σ y

theorem integrable_V_mul_cexp {z : ℂ} (hz : 1 / 2 < z.re) :
    Integrable (fun y : ℝ => (V y : ℂ) * cexp (-z * y)) := by
  refine (integrable_V_mul_exp hz).mono
    ((Complex.continuous_ofReal.comp continuous_V).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  rw [norm_mul, Complex.norm_real, LandauLaplace.norm_cexp_neg_mul_ofReal, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]

/-- The complex Fubini integrand `1_{s ≤ y} P(s) e^{−(z+½) y}`. -/
def Fc (z : ℂ) : ℝ × ℝ → ℂ := Sle.indicator (fun q => (P q.1 : ℂ) * cexp (-(z + 1 / 2) * q.2))

theorem norm_Fc (z : ℂ) (q : ℝ × ℝ) : ‖Fc z q‖ = Freal z.re q := by
  unfold Fc Freal
  by_cases hq : q ∈ Sle
  · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (P_nonneg _), Complex.norm_exp]
    congr 2
    simp
  · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq, norm_zero]

theorem integrable_Fc {z : ℂ} (hz : 1 / 2 < z.re) : Integrable (Fc z) (volume.prod volume) := by
  have hmeas : AEStronglyMeasurable (Fc z) (volume.prod volume) :=
    (((Complex.continuous_ofReal.comp (continuous_P.comp continuous_fst)).mul (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd))))).aestronglyMeasurable.indicator
      measurableSet_Sle
  exact (integrable_Freal z.re hz).mono' hmeas (Eventually.of_forall fun q => (norm_Fc z q).le)

/-- **The transform of the integrated signal**: `∫ V(y) e^{−zy} dy = K̃(z) L(Λ, ½ + z)/(z + ½)` for `Re z > ½`. -/
theorem integral_V_mul_cexp {z : ℂ} (hz : 1 / 2 < z.re) :
    ∫ y : ℝ, (V y : ℂ) * cexp (-z * y) = Kt z * LSeries (fun m => (Λ m : ℂ)) (1 / 2 + z) / (z + 1 / 2) := by
  have hz0 : z + 1 / 2 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hre : (-(z + 1 / 2)).re < 0 := by simp; linarith
  -- inner integral in `s`, at fixed `y`
  have hy : ∀ y : ℝ, ∫ s, Fc z (s, y) = (V y : ℂ) * cexp (-z * y) := by
    intro y
    have hpt : (fun s => Fc z (s, y)) = (Iic y).indicator (fun s => (P s : ℂ) * cexp (-(z + 1 / 2) * y)) := by
      funext s
      simp only [Fc, Sle, Set.indicator_apply, mem_setOf_eq, mem_Iic]
    rw [hpt, integral_indicator measurableSet_Iic, integral_mul_const, integral_complex_ofReal, ← exp_mul_V]
    push_cast
    rw [show -(z + 1 / 2) * (y : ℂ) = -((y : ℂ) / 2) + -z * y by ring, Complex.exp_add]
    have h1 : cexp ((y : ℂ) / 2) * cexp (-((y : ℂ) / 2)) = 1 := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    linear_combination ((V y : ℂ) * cexp (-z * y)) * h1
  -- inner integral in `y`, at fixed `s`
  have hs : ∀ s : ℝ, ∫ y, Fc z (s, y) = (1 / (z + 1 / 2)) * ((W s : ℂ) * cexp (-z * s)) := by
    intro s
    have hpt : (fun y => Fc z (s, y)) = (Ici s).indicator (fun y => (P s : ℂ) * cexp (-(z + 1 / 2) * y)) := by
      funext y
      simp only [Fc, Sle, Set.indicator_apply, mem_setOf_eq, mem_Ici]
    rw [hpt, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul,
      integral_exp_mul_complex_Ioi hre s, P]
    push_cast
    rw [show -(z + 1 / 2) * (s : ℂ) = (s : ℂ) / 2 * (-1) + -z * s by ring, Complex.exp_add,
      show (s : ℂ) / 2 * (-1) = -((s : ℂ) / 2) by ring, Complex.exp_neg]
    field_simp
  have hswap := integral_integral_swap (f := fun s y => Fc z (s, y)) (integrable_Fc hz)
  calc ∫ y : ℝ, (V y : ℂ) * cexp (-z * y) = ∫ y, ∫ s, Fc z (s, y) := by
        exact integral_congr_ae (Eventually.of_forall fun y => (hy y).symm)
    _ = ∫ s, ∫ y, Fc z (s, y) := hswap.symm
    _ = ∫ s, (1 / (z + 1 / 2)) * ((W s : ℂ) * cexp (-z * s)) :=
        integral_congr_ae (Eventually.of_forall hs)
    _ = Kt z * LSeries (fun m => (Λ m : ℂ)) (1 / 2 + z) / (z + 1 / 2) := by
        rw [integral_const_mul, integral_W_mul_cexp hz]
        ring

/-! ## 3. The kernel `J̃(z) = K̃(z)/(z + ½)` -/

/-- The integrated kernel's transform. -/
def Jt (z : ℂ) : ℂ := Kt z / (z + 1 / 2)

theorem add_half_ne_zero {z : ℂ} (hz : -(1 / 2) < z.re) : z + 1 / 2 ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  simp at this
  linarith

theorem Jt_half : Jt (1 / 2) = (D : ℂ) := by
  rw [Jt, Kt_half]
  norm_num

theorem Jt_ne_zero {z : ℂ} (hz : -(1 / 2) < z.re) : Jt z ≠ 0 :=
  div_ne_zero (Kt_ne_zero z) (add_half_ne_zero hz)

theorem differentiableAt_Jt {z : ℂ} (hz : -(1 / 2) < z.re) : DifferentiableAt ℂ Jt z :=
  (differentiable_Kt z).div (differentiableAt_id.add_const _) (add_half_ne_zero hz)

/-- The half-plane `Re w > −½`, where `J̃` is analytic and zero-free. -/
def Hhalf : Set ℂ := {w | -(1 / 2 : ℝ) < w.re}

theorem isOpen_Hhalf : IsOpen Hhalf := isOpen_lt continuous_const Complex.continuous_re

theorem differentiableOn_Jt : DifferentiableOn ℂ Jt Hhalf := fun w hw =>
  (differentiableAt_Jt (show -(1 / 2 : ℝ) < w.re from hw)).differentiableWithinAt

theorem differentiableOn_dslope_Jt :
    DifferentiableOn ℂ (dslope (fun w => Jt w - (D : ℂ)) (1 / 2)) Hhalf := by
  have hs : Hhalf ∈ 𝓝 (1 / 2 : ℂ) := isOpen_Hhalf.mem_nhds (by
    show -(1 / 2 : ℝ) < (1 / 2 : ℂ).re
    norm_num)
  refine (differentiableOn_dslope hs).2 fun w hw => ?_
  exact ((differentiableAt_Jt (show -(1 / 2 : ℝ) < w.re from hw)).sub_const _).differentiableWithinAt

theorem differentiableAt_dslope_Jt {z : ℂ} (hz : -(1 / 2) < z.re) :
    DifferentiableAt ℂ (dslope (fun w => Jt w - (D : ℂ)) (1 / 2)) z :=
  differentiableOn_dslope_Jt.differentiableAt (isOpen_Hhalf.mem_nhds hz)

/-! ## 4. The θ-dial for the integrated signal -/

/-- **The integrated θ-dial input.** -/
def LowerBoundInt (θ : ℝ) : Prop :=
  ∃ C : ℝ, ∀ y : ℝ, 0 ≤ y → D * Real.exp (y / 2) - C * Real.exp (θ * y) ≤ V y

/-- The integrated weight `V(y) − D e^{y/2} + C e^{θy}`. -/
def gInt (θ C : ℝ) (y : ℝ) : ℝ := V y - D * Real.exp (y / 2) + C * Real.exp (θ * y)

theorem laplace_gInt_eq (θ C : ℝ) {z : ℂ} (hz : 1 / 2 < z.re) (hθz : θ < z.re) :
    LandauLaplace.laplace (Ici 0) (gInt θ C) z
      = Jt z * LSeries (fun m => (Λ m : ℂ)) (1 / 2 + z) - EV z - (D : ℂ) / (z - 1 / 2)
        + (C : ℂ) / (z - θ) := by
  have hV := integrable_V_mul_cexp hz
  have h1 : IntegrableOn (fun y : ℝ => (V y : ℂ) * cexp (-z * y)) (Ici 0) := hV.integrableOn
  have h2 : IntegrableOn (fun y : ℝ => cexp ((1 / 2 - z) * y)) (Ici 0) :=
    integrableOn_Ici_cexp (by simp; linarith)
  have h3 : IntegrableOn (fun y : ℝ => cexp (((θ : ℂ) - z) * y)) (Ici 0) :=
    integrableOn_Ici_cexp (by simp; linarith)
  have hpt : ∀ y : ℝ, ((gInt θ C y : ℝ) : ℂ) * cexp (-z * y)
      = (V y : ℂ) * cexp (-z * y) - (D : ℂ) * cexp ((1 / 2 - z) * y)
        + (C : ℂ) * cexp (((θ : ℂ) - z) * y) := by
    intro y
    rw [gInt]
    push_cast
    rw [show (1 / 2 - z) * (y : ℂ) = (y : ℂ) / 2 + -z * y by ring,
      show ((θ : ℂ) - z) * (y : ℂ) = (θ : ℂ) * y + -z * y by ring, Complex.exp_add, Complex.exp_add]
    ring
  have hA : IntegrableOn (fun y : ℝ => (V y : ℂ) * cexp (-z * y) - (D : ℂ) * cexp ((1 / 2 - z) * y))
      (Ici 0) := h1.sub (h2.const_mul _)
  have hB : IntegrableOn (fun y : ℝ => (D : ℂ) * cexp ((1 / 2 - z) * y)) (Ici 0) := h2.const_mul _
  have hC : IntegrableOn (fun y : ℝ => (C : ℂ) * cexp (((θ : ℂ) - z) * y)) (Ici 0) := h3.const_mul _
  rw [LandauLaplace.laplace, integral_congr_ae (Eventually.of_forall hpt), integral_add hA hC,
    integral_sub h1 hB, integral_const_mul, integral_const_mul, integral_Ici_cexp (by simp; linarith),
    integral_Ici_cexp (by simp; linarith)]
  have hsplit := integral_add_compl (measurableSet_Ici (a := (0 : ℝ))) hV
  rw [compl_Ici, integral_V_mul_cexp hz] at hsplit
  have hE : ∫ y in Iio (0 : ℝ), (V y : ℂ) * cexp (-z * y) = EV z := rfl
  rw [hE] at hsplit
  rw [show (∫ y in Ici (0 : ℝ), (V y : ℂ) * cexp (-z * y)) =
      Jt z * LSeries (fun m => (Λ m : ℂ)) (1 / 2 + z) - EV z by rw [Jt]; linear_combination hsplit]
  rw [show -1 / (1 / 2 - z) = 1 / (z - 1 / 2) by
      rw [show (1 / 2 : ℂ) - z = -(z - 1 / 2) by ring, div_neg, neg_div, neg_neg],
    show -1 / ((θ : ℂ) - z) = 1 / (z - θ) by
      rw [show (θ : ℂ) - z = -(z - θ) by ring, div_neg, neg_div, neg_neg]]
  ring

/-- The continuation for the integrated θ-dial. -/
def FInt (θ C : ℝ) (z : ℂ) : ℂ :=
  Jt z * (-deriv Zfun (1 / 2 + z) / Zfun (1 / 2 + z)) + dslope (fun w => Jt w - (D : ℂ)) (1 / 2) z
    - EV z + (C : ℂ) / (z - θ)

theorem FInt_eq_laplace (θ C : ℝ) (hθ : θ < 1) {z : ℂ} (hz : 1 < z.re) :
    FInt θ C z = LandauLaplace.laplace (Ici 0) (gInt θ C) z := by
  rw [laplace_gInt_eq θ C (by linarith) (by linarith)]
  have hs : 1 < ((1 / 2 : ℂ) + z).re := by rw [re_half_add]; linarith
  have hs1 : (1 / 2 : ℂ) + z ≠ 1 := half_add_ne_one (by linarith)
  have hzeta : riemannZeta ((1 / 2 : ℂ) + z) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, neg_logDeriv_zeta_eq hs1 hzeta]
  have hz12 : z ≠ 1 / 2 := by
    intro h
    rw [h] at hz
    norm_num at hz
  rw [FInt, dslope_of_ne _ hz12, slope_def_field, Jt_half,
    show (1 / 2 : ℂ) + z - 1 = z - 1 / 2 by ring]
  ring

theorem differentiableOn_FInt (θ C : ℝ) {σ₀ r : ℝ} (h0 : 0 < σ₀) (hθ : θ ≤ σ₀) (h01 : σ₀ < 1)
    (hr : ∀ z : ℂ, σ₀ < z.re → |z.im| < r → Zfun (1 / 2 + z) ≠ 0) :
    DifferentiableOn ℂ (FInt θ C) (LandauLaplace.domain σ₀ 1 r) := by
  intro z hz
  have hre : σ₀ < z.re := by
    rcases hz with ⟨h, _⟩ | h
    · exact h
    · have h' : (1 : ℝ) < z.re := h
      linarith
  have hZ : Zfun (1 / 2 + z) ≠ 0 := by
    rcases hz with ⟨h1, h2⟩ | h
    · exact hr z h1 h2
    · have h' : (1 : ℝ) < z.re := h
      rw [Ne, Zfun_eq_zero_iff (half_add_ne_one (by linarith))]
      exact riemannZeta_ne_zero_of_one_le_re (by rw [re_half_add]; linarith)
  have hzθ : z - θ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hzh : -(1 / 2) < z.re := by linarith
  apply DifferentiableAt.differentiableWithinAt
  have hshift : DifferentiableAt ℂ (fun w : ℂ => (1 / 2 : ℂ) + w) z :=
    (differentiableAt_const _).add differentiableAt_id
  have hZd : DifferentiableAt ℂ (fun w => Zfun (1 / 2 + w)) z :=
    (differentiable_Zfun _).comp z hshift
  have hdZd : DifferentiableAt ℂ (fun w => deriv Zfun (1 / 2 + w)) z :=
    ((differentiable_Zfun.analyticAt _).deriv.differentiableAt).comp z hshift
  unfold FInt
  exact ((((differentiableAt_Jt hzh).mul (hdZd.neg.div hZd hZ)).add (differentiableAt_dslope_Jt hzh)).sub
    (differentiable_EV z)).add ((differentiableAt_const _).div (differentiableAt_id.sub_const _) hzθ)

theorem integrableOn_gInt_Ici (θ C : ℝ) {σ : ℝ} (hσ : 1 / 2 < σ) (hθσ : θ < σ) :
    IntegrableOn (fun y => gInt θ C y * Real.exp (-σ * y)) (Ici 0) := by
  have hV : IntegrableOn (fun y => V y * Real.exp (-σ * y)) (Ici 0) :=
    (integrable_V_mul_exp hσ).integrableOn
  have hD : IntegrableOn (fun y : ℝ => D * Real.exp (-(σ - 1 / 2) * y)) (Ici 0) :=
    ((exp_neg_integrableOn_Ioi 0 (by linarith)).congr_set_ae Ioi_ae_eq_Ici.symm).const_mul D
  have hC : IntegrableOn (fun y : ℝ => C * Real.exp (-(σ - θ) * y)) (Ici 0) :=
    ((exp_neg_integrableOn_Ioi 0 (by linarith)).congr_set_ae Ioi_ae_eq_Ici.symm).const_mul C
  refine ((hV.sub hD).add hC).congr_fun (fun y _ => ?_) measurableSet_Ici
  simp only [gInt, Pi.add_apply, Pi.sub_apply]
  rw [show -(σ - 1 / 2) * y = y / 2 + -σ * y by ring, show -(σ - θ) * y = θ * y + -σ * y by ring,
    Real.exp_add, Real.exp_add]
  ring

/-- **Landau applied to the integrated weight.** -/
theorem integrableOn_gInt_of_lowerBound (θ C : ℝ)
    (hC : ∀ y, 0 ≤ y → D * Real.exp (y / 2) - C * Real.exp (θ * y) ≤ V y)
    {σ₀ : ℝ} (h0 : 0 < σ₀) (hθ : θ ≤ σ₀) (h01 : σ₀ < 1) :
    ∀ σ, σ₀ < σ → IntegrableOn (fun y => gInt θ C y * Real.exp (-σ * y)) (Ici 0) := by
  obtain ⟨r, hr, hrZ⟩ := exists_zeroFree_strip h0
  refine LandauLaplace.landau (gInt θ C) 0 le_rfl (fun y hy => ?_) h01 hr
    (fun σ hσ => integrableOn_gInt_Ici θ C (by linarith) (by linarith)) (FInt θ C)
    (differentiableOn_FInt θ C h0 hθ h01 hrZ) (fun z hz => FInt_eq_laplace θ C (by linarith) hz)
  have := hC y hy
  unfold gInt
  linarith

/-- **The integrated θ-dial excludes zeros with `Re ρ > ½ + θ`.** -/
theorem no_zero_of_lowerBoundInt (θ C : ℝ) (hθ : 0 ≤ θ)
    (hC : ∀ y, 0 ≤ y → D * Real.exp (y / 2) - C * Real.exp (θ * y) ≤ V y)
    (ρ : ℂ) (hρ : riemannZeta ρ = 0) (h1 : 1 / 2 + θ < ρ.re) (h2 : ρ.re < 1) : False := by
  set p : ℂ := ρ - 1 / 2 with hp
  have hpre : p.re = ρ.re - 1 / 2 := by simp [hp]
  set σ₀ : ℝ := (p.re + θ) / 2 with hσ₀
  have h0 : 0 < σ₀ := by rw [hσ₀, hpre]; linarith
  have hθσ : θ ≤ σ₀ := by rw [hσ₀, hpre]; linarith
  have h01 : σ₀ < 1 := by rw [hσ₀, hpre]; linarith
  have hLd := LandauLaplace.differentiableOn_laplace (Ici 0) (gInt θ C) σ₀
    (integrableOn_gInt_of_lowerBound θ C hC h0 hθσ h01)
  set U : Set ℂ := {z | σ₀ < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  set Q : ℂ → ℂ := fun z => LandauLaplace.laplace (Ici 0) (gInt θ C) z + EV z - (C : ℂ) / (z - θ)
    - dslope (fun w => Jt w - (D : ℂ)) (1 / 2) z with hQ
  set ψ : ℂ → ℂ := fun z => Zfun (1 / 2 + z) with hψ
  have hψd : Differentiable ℂ ψ := fun z =>
    (differentiable_Zfun _).comp z ((differentiableAt_const _).add differentiableAt_id)
  have hQd : DifferentiableOn ℂ Q U := by
    intro z hz
    have hz' : σ₀ < z.re := hz
    have hzθ : z - θ ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    apply DifferentiableAt.differentiableWithinAt
    exact (((hLd.differentiableAt (hUo.mem_nhds hz)).add (differentiable_EV z)).sub
      ((differentiableAt_const _).div (differentiableAt_id.sub_const _) hzθ)).sub
      (differentiableAt_dslope_Jt (by linarith))
  have hderiv : ∀ z, deriv ψ z = deriv Zfun (1 / 2 + z) := fun z => deriv_comp_const_add Zfun (1 / 2) z
  have hG1 : AnalyticOnNhd ℂ (fun z => ψ z * Q z) U :=
    (hψd.differentiableOn.mul hQd).analyticOnNhd hUo
  have hG2 : AnalyticOnNhd ℂ (fun z => -(Jt z * deriv ψ z)) U := by
    have hd : DifferentiableOn ℂ (fun z => -(Jt z * deriv ψ z)) U := by
      intro z hz
      have hz' : σ₀ < z.re := hz
      apply DifferentiableAt.differentiableWithinAt
      have hdd : DifferentiableAt ℂ (fun z => deriv ψ z) z := by
        simp_rw [hderiv]
        exact ((differentiable_Zfun.analyticAt _).deriv.differentiableAt).comp z
          ((differentiableAt_const _).add differentiableAt_id)
      exact ((differentiableAt_Jt (by linarith)).mul hdd).neg
    exact hd.analyticOnNhd hUo
  have hUc : IsPreconnected U := (convex_halfSpace_gt Complex.reLm.isLinear σ₀).isPreconnected
  have h2U : (2 : ℂ) ∈ U := by
    show σ₀ < (2 : ℂ).re
    rw [show (2 : ℂ).re = 2 by norm_num]
    linarith
  have hEq : EqOn (fun z => ψ z * Q z) (fun z => -(Jt z * deriv ψ z)) U := by
    refine hG1.eqOn_of_preconnected_of_eventuallyEq hG2 hUc h2U ?_
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
    have hz' : (1 : ℝ) < z.re := hz
    have hF := FInt_eq_laplace θ C (by linarith) hz'
    have hZ : Zfun (1 / 2 + z) ≠ 0 := by
      rw [Ne, Zfun_eq_zero_iff (half_add_ne_one (by linarith))]
      exact riemannZeta_ne_zero_of_one_le_re (by rw [re_half_add]; linarith)
    have hQz : Q z = Jt z * (-deriv Zfun (1 / 2 + z) / Zfun (1 / 2 + z)) := by
      show LandauLaplace.laplace (Ici 0) (gInt θ C) z + EV z - (C : ℂ) / (z - θ)
        - dslope (fun w => Jt w - (D : ℂ)) (1 / 2) z = _
      rw [← hF]
      unfold FInt
      ring
    show ψ z * Q z = -(Jt z * deriv ψ z)
    rw [hQz, hderiv z]
    show Zfun (1 / 2 + z) * (Jt z * (-deriv Zfun (1 / 2 + z) / Zfun (1 / 2 + z)))
      = -(Jt z * deriv Zfun (1 / 2 + z))
    rw [mul_div_assoc', mul_div_assoc', div_eq_iff hZ]
    ring
  have hpU : p ∈ U := by
    show σ₀ < p.re
    rw [hσ₀, hpre]
    linarith
  have hph : -(1 / 2 : ℝ) < p.re := by rw [hpre]; linarith
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at h2
    exact lt_irrefl _ h2
  have hψp : ψ p = 0 := by
    simp only [hψ, hp]
    rw [show (1 / 2 : ℂ) + (ρ - 1 / 2) = ρ by ring, Zfun_eq_zero_iff hρ1]
    exact hρ
  have hψne : ∃ w, ψ w ≠ 0 := ⟨1 / 2, by
    simp only [hψ]
    rw [show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, Zfun_one]
    exact one_ne_zero⟩
  exact no_zero_of_multiplied_identity hψd hψne hψp
    (hQd.analyticAt (hUo.mem_nhds hpU)) (differentiableOn_Jt.analyticAt (isOpen_Hhalf.mem_nhds hph))
    (Jt_ne_zero hph) (by filter_upwards [hUo.mem_nhds hpU] with z hz using hEq hz)

/-- **The integrated dial confines the strip zeros**: every zero with `0 < Re ρ < 1` has `|Re ρ − ½| ≤ θ`. -/
theorem abs_re_sub_half_le_of_lowerBoundInt {θ : ℝ} (hθ : 0 ≤ θ) (h : LowerBoundInt θ)
    (ρ : ℂ) (hρ : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : |ρ.re - 1 / 2| ≤ θ := by
  obtain ⟨C, hC⟩ := h
  rw [abs_le]
  constructor
  · by_contra hlt
    have hlt' := not_le.mp hlt
    have hn : ∀ n : ℕ, ρ ≠ -n := by
      intro n hn
      have hre := congrArg Complex.re hn
      rw [Complex.neg_re, Complex.natCast_re] at hre
      have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith
    have hne1 : ρ ≠ 1 := by
      intro h'
      rw [h', Complex.one_re] at h1
      exact lt_irrefl _ h1
    have hz : riemannZeta (1 - ρ) = 0 := by
      rw [riemannZeta_one_sub hn hne1, hρ, mul_zero]
    exact no_zero_of_lowerBoundInt θ C hθ hC (1 - ρ) hz
      (by rw [Complex.sub_re, Complex.one_re]; linarith) (by rw [Complex.sub_re, Complex.one_re]; linarith)
  · by_contra hlt
    have hlt' := not_le.mp hlt
    exact no_zero_of_lowerBoundInt θ C hθ hC ρ hρ (by linarith) h1

theorem re_eq_half_of_forall_lowerBoundInt (h : ∀ θ : ℝ, 0 < θ → LowerBoundInt θ)
    (ρ : ℂ) (hρ : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : ρ.re = 1 / 2 := by
  have key : ∀ θ : ℝ, 0 < θ → |ρ.re - 1 / 2| ≤ θ := fun θ hθ =>
    abs_re_sub_half_le_of_lowerBoundInt hθ.le (h θ hθ) ρ hρ h0 h1
  have habs : |ρ.re - 1 / 2| = 0 := by
    by_contra hne
    have hpos : 0 < |ρ.re - 1 / 2| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne)
    have := key (|ρ.re - 1 / 2| / 2) (by linarith)
    linarith
  have := abs_eq_zero.mp habs
  linarith

/-- **Every `θ > 0` of the integrated dial together suffices.** -/
theorem riemannHypothesis_of_forall_lowerBoundInt (h : ∀ θ : ℝ, 0 < θ → LowerBoundInt θ) :
    RiemannHypothesis :=
  VMEFStandalone.NontrivialZeros_implies_RiemannHypothesis fun ρ hρ =>
    re_eq_half_of_forall_lowerBoundInt h ρ hρ.2.2 hρ.1 hρ.2.1

/-! ## 5. The integrated input is the weaker one -/

theorem integral_exp_mul_interval (c y : ℝ) (hc : c ≠ 0) :
    ∫ s in (0 : ℝ)..y, Real.exp (c * s) = (Real.exp (c * y) - 1) / c := by
  rw [intervalIntegral.integral_comp_mul_left (fun s => Real.exp s) hc, integral_exp, mul_zero,
    Real.exp_zero, smul_eq_mul]
  field_simp

/-- **`ψ_K`'s dial implies the integrated dial**: `LowerBoundTheta θ → LowerBoundInt θ` (`θ ≥ 0`). -/
theorem LowerBoundTheta.toInt {θ : ℝ} (hθ : 0 ≤ θ) (h : LowerBoundTheta θ) : LowerBoundInt θ := by
  obtain ⟨C, hC⟩ := h
  set Cp := max C 0 with hCp
  have hCp0 : 0 ≤ Cp := le_max_right _ _
  have hc : (0 : ℝ) < 1 / 2 + θ := by linarith
  refine ⟨D + Cp / (1 / 2 + θ), fun y hy => ?_⟩
  have hpt : ∀ s ∈ Icc (0 : ℝ) y, D * Real.exp s - Cp * Real.exp ((1 / 2 + θ) * s) ≤ P s := by
    intro s hs
    have h1 := hC s hs.1
    have e1 : Real.exp (s / 2) * Real.exp (s / 2) = Real.exp s := by
      rw [← Real.exp_add]
      ring_nf
    have e2 : Real.exp (s / 2) * Real.exp (θ * s) = Real.exp ((1 / 2 + θ) * s) := by
      rw [← Real.exp_add]
      ring_nf
    have hm := mul_le_mul_of_nonneg_left h1 (Real.exp_pos (s / 2)).le
    have hCC := mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos ((1 / 2 + θ) * s)).le
    calc D * Real.exp s - Cp * Real.exp ((1 / 2 + θ) * s)
        ≤ D * Real.exp s - C * Real.exp ((1 / 2 + θ) * s) := by linarith
      _ = Real.exp (s / 2) * (D * Real.exp (s / 2) - C * Real.exp (θ * s)) := by
          rw [← e1, ← e2]
          ring
      _ ≤ Real.exp (s / 2) * W s := hm
      _ = P s := rfl
  have hcont : Continuous fun s : ℝ => D * Real.exp s - Cp * Real.exp ((1 / 2 + θ) * s) := by
    fun_prop
  have hmono := intervalIntegral.integral_mono_on (μ := volume) hy (hcont.intervalIntegrable 0 y)
    (continuous_P.intervalIntegrable 0 y) hpt
  have hval : ∫ s in (0 : ℝ)..y, (D * Real.exp s - Cp * Real.exp ((1 / 2 + θ) * s))
      = D * (Real.exp y - 1) - Cp * ((Real.exp ((1 / 2 + θ) * y) - 1) / (1 / 2 + θ)) := by
    have i1 : IntervalIntegrable (fun s : ℝ => D * Real.exp s) volume 0 y :=
      (by fun_prop : Continuous fun s : ℝ => D * Real.exp s).intervalIntegrable 0 y
    have i2 : IntervalIntegrable (fun s : ℝ => Cp * Real.exp ((1 / 2 + θ) * s)) volume 0 y :=
      (by fun_prop : Continuous fun s : ℝ => Cp * Real.exp ((1 / 2 + θ) * s)).intervalIntegrable 0 y
    rw [intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_exp, Real.exp_zero, integral_exp_mul_interval _ y hc.ne']
  rw [hval] at hmono
  have hIic0 : 0 ≤ ∫ s in Iic 0, P s := setIntegral_nonneg measurableSet_Iic fun s _ => P_nonneg s
  have hEV : Real.exp (y / 2) * V y ≥ D * (Real.exp y - 1) - Cp * ((Real.exp ((1 / 2 + θ) * y) - 1) / (1 / 2 + θ)) := by
    rw [exp_mul_V, integral_Iic_P_eq]
    linarith
  set E := Real.exp (y / 2) with hE
  set T := Real.exp (θ * y) with hT
  have hEpos : 0 < E := Real.exp_pos _
  have hE1 : 1 ≤ E := Real.one_le_exp (by linarith)
  have hT1 : 1 ≤ T := Real.one_le_exp (by positivity)
  have hy1 : Real.exp y = E * E := by
    rw [hE, ← Real.exp_add]
    ring_nf
  have hy2 : Real.exp ((1 / 2 + θ) * y) = E * T := by
    rw [hE, hT, ← Real.exp_add]
    ring_nf
  rw [hy1, hy2] at hEV
  have hET : 1 ≤ E * T := by nlinarith
  have hD0 : 0 ≤ D := D_pos.le
  have hq : 0 ≤ Cp / (1 / 2 + θ) := div_nonneg hCp0 hc.le
  have hdiv : Cp * ((E * T - 1) / (1 / 2 + θ)) = Cp / (1 / 2 + θ) * (E * T) - Cp / (1 / 2 + θ) := by
    field_simp
  rw [hdiv] at hEV
  have key : E * (D * E - (D + Cp / (1 / 2 + θ)) * T) ≤ E * V y := by
    nlinarith [mul_le_mul_of_nonneg_left hET hD0]
  exact le_of_mul_le_mul_left key hEpos

end SmoothedPrimeSignal
