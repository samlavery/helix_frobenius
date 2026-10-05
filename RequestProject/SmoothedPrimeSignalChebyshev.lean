import RequestProject.SmoothedPrimeSignalIntegrated

/-!
# The classical one-sided Chebyshev bound feeds the integrated form by positivity (ledger 920)

With `ψ = Chebyshev.psi` (Mathlib) and the positive kernel `q(t) = e^{t/2} e^{−t²}`,

  `e^{y/2} V(y) = ∫ q(y − u) ψ(e^u) du`          (`exp_mul_V_eq_integral_psi`),

and `∫ q(y − u) e^{cu} du = e^{cy} √π e^{(c − ½)²/4}`.  Since `q ≥ 0`, a one-sided bound `ψ(t) ≥ t − C t^{½+θ}`
passes to `V` with no loss of exponent:

* `lowerBoundInt_of_psi`: `ψ(t) ≥ t − C t^{½+θ}` for `t ≥ 1` implies `LowerBoundInt θ` (`0 ≤ θ ≤ ½`);
* `riemannHypothesis_of_psi_lowerBound`: the one-sided bound for every `θ ∈ (0, ½]` gives `RiemannHypothesis`.

No `sorry`, no `axiom`.
-/

open MeasureTheory Set Filter Topology
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace SmoothedPrimeSignal

/-! ## 1. The positive kernel -/

/-- The positive kernel `q(t) = e^{t/2} e^{−t²}`. -/
def q (t : ℝ) : ℝ := Real.exp (t / 2) * K t

theorem q_nonneg (t : ℝ) : 0 ≤ q t := by
  unfold q K
  positivity

theorem continuous_q : Continuous q := by
  unfold q K
  fun_prop

/-- `∫ e^{−t²} e^{−σt} dt = √π e^{σ²/4}`. -/
theorem integral_K_mul_exp' (σ : ℝ) :
    ∫ t : ℝ, K t * Real.exp (-σ * t) = Real.sqrt Real.pi * Real.exp (σ ^ 2 / 4) := by
  have h := integral_K_mul_cexp (σ : ℂ)
  have h2 : (fun x : ℝ => ((K x : ℝ) : ℂ) * Complex.exp (-(σ : ℂ) * x))
      = fun x : ℝ => ((K x * Real.exp (-σ * x) : ℝ) : ℂ) := by
    funext x
    push_cast
    ring_nf
  rw [h2, integral_complex_ofReal] at h
  have hKt : Kt (σ : ℂ) = ((Real.sqrt Real.pi * Real.exp (σ ^ 2 / 4) : ℝ) : ℂ) := by
    rw [Kt, Complex.ofReal_mul, Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le, Complex.ofReal_exp]
    congr 2
    all_goals (push_cast; try ring)
  rw [hKt] at h
  exact_mod_cast h

theorem q_shift_mul_exp_eq (y c u : ℝ) :
    q (y - u) * Real.exp (c * u) = Real.exp (c * y) * (K (y - u) * Real.exp (-(c - 1 / 2) * (y - u))) := by
  unfold q
  have h : Real.exp (c * y) * Real.exp (-(c - 1 / 2) * (y - u)) = Real.exp ((y - u) / 2) * Real.exp (c * u) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc Real.exp ((y - u) / 2) * K (y - u) * Real.exp (c * u)
      = K (y - u) * (Real.exp ((y - u) / 2) * Real.exp (c * u)) := by ring
    _ = K (y - u) * (Real.exp (c * y) * Real.exp (-(c - 1 / 2) * (y - u))) := by rw [h]
    _ = Real.exp (c * y) * (K (y - u) * Real.exp (-(c - 1 / 2) * (y - u))) := by ring

theorem integrable_q_shift_mul_exp (y c : ℝ) : Integrable (fun u => q (y - u) * Real.exp (c * u)) := by
  have h := ((integrable_K_mul_exp (c - 1 / 2)).comp_sub_left y).const_mul (Real.exp (c * y))
  refine h.congr (Eventually.of_forall fun u => ?_)
  simp only
  rw [q_shift_mul_exp_eq]

/-- **The kernel's moments**: `∫ q(y − u) e^{cu} du = e^{cy} √π e^{(c − ½)²/4}`. -/
theorem integral_q_shift_mul_exp (y c : ℝ) :
    ∫ u : ℝ, q (y - u) * Real.exp (c * u)
      = Real.exp (c * y) * (Real.sqrt Real.pi * Real.exp ((c - 1 / 2) ^ 2 / 4)) := by
  simp_rw [q_shift_mul_exp_eq]
  rw [integral_const_mul, integral_sub_left_eq_self (fun t => K t * Real.exp (-(c - 1 / 2) * t)) volume y,
    integral_K_mul_exp']

/-! ## 2. The positive-kernel representation of the integrated signal -/

theorem term_eq_Λq (s : ℝ) (n : ℕ) :
    Real.exp (s / 2) * (a n * K (s - Real.log n)) = Λ n * q (s - Real.log n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [a_zero]
  · have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    rw [a, q, Real.rpow_def_of_pos hn']
    have h : Real.exp (s / 2) * Real.exp (Real.log n * -(1 / 2)) = Real.exp ((s - Real.log n) / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc Real.exp (s / 2) * (Λ n * Real.exp (Real.log n * -(1 / 2)) * K (s - Real.log n))
        = Λ n * ((Real.exp (s / 2) * Real.exp (Real.log n * -(1 / 2))) * K (s - Real.log n)) := by ring
      _ = Λ n * (Real.exp ((s - Real.log n) / 2) * K (s - Real.log n)) := by rw [h]

theorem summable_Λq (s : ℝ) : Summable fun n : ℕ => Λ n * q (s - Real.log n) :=
  ((summable_terms s).mul_left (Real.exp (s / 2))).congr (term_eq_Λq s)

theorem P_eq_tsum (s : ℝ) : P s = ∑' n : ℕ, Λ n * q (s - Real.log n) := by
  rw [P, W, ← tsum_mul_left]
  exact tsum_congr (term_eq_Λq s)

/-- A non-negative series may be integrated termwise when its sum is integrable. -/
theorem integral_tsum_of_nonneg' {f : ℕ → ℝ → ℝ} (hf : ∀ n x, 0 ≤ f n x)
    (hmeas : ∀ n, AEStronglyMeasurable (f n) volume) (hsum : ∀ x, Summable fun n => f n x)
    (hint : Integrable (fun x => ∑' n, f n x)) :
    ∫ x, ∑' n, f n x = ∑' n, ∫ x, f n x := by
  refine integral_tsum hmeas ?_
  rw [← lintegral_tsum (fun n => (hmeas n).enorm)]
  have hpt : ∀ x, ∑' n, ‖f n x‖ₑ = ‖∑' n, f n x‖ₑ := by
    intro x
    rw [Real.enorm_eq_ofReal (tsum_nonneg (hf · x)), ENNReal.ofReal_tsum_of_nonneg (hf · x) (hsum x)]
    exact tsum_congr fun n => Real.enorm_eq_ofReal (hf n x)
  simp_rw [hpt]
  exact hint.2.ne

/-- The pieces of `P` on `(−∞, y]`. -/
def Gp (y : ℝ) (n : ℕ) (s : ℝ) : ℝ := (Iic y).indicator (fun s => Λ n * q (s - Real.log n)) s

/-- The same pieces after `s ↦ y + log n − s`. -/
def Fp (y : ℝ) (n : ℕ) (u : ℝ) : ℝ := (Ici (Real.log n)).indicator (fun u => Λ n * q (y - u)) u

theorem Gp_nonneg (y : ℝ) (n : ℕ) (s : ℝ) : 0 ≤ Gp y n s :=
  Set.indicator_nonneg (fun _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (q_nonneg _)) s

theorem Fp_nonneg (y : ℝ) (n : ℕ) (u : ℝ) : 0 ≤ Fp y n u :=
  Set.indicator_nonneg (fun _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (q_nonneg _)) u

theorem Gp_eq_Fp (y : ℝ) (n : ℕ) (s : ℝ) : Gp y n s = Fp y n (y + Real.log n - s) := by
  unfold Gp Fp
  by_cases hs : s ≤ y
  · rw [Set.indicator_of_mem (show s ∈ Iic y from hs),
      Set.indicator_of_mem (show y + Real.log n - s ∈ Ici (Real.log n) by simp only [mem_Ici]; linarith)]
    congr 2
    ring
  · rw [Set.indicator_of_notMem (show s ∉ Iic y from hs),
      Set.indicator_of_notMem (show y + Real.log n - s ∉ Ici (Real.log n) by
        simp only [mem_Ici, not_le]; linarith [not_le.mp hs])]

theorem integral_Gp_eq (y : ℝ) (n : ℕ) : ∫ s, Gp y n s = ∫ u, Fp y n u := by
  simp_rw [Gp_eq_Fp y n]
  exact integral_sub_left_eq_self (Fp y n) volume (y + Real.log n)

theorem tsum_Gp (y s : ℝ) : ∑' n, Gp y n s = (Iic y).indicator P s := by
  by_cases hs : s ≤ y
  · simp only [Gp, Set.indicator_of_mem (show s ∈ Iic y from hs)]
    exact (P_eq_tsum s).symm
  · simp only [Gp, Set.indicator_of_notMem (show s ∉ Iic y from hs), tsum_zero]

theorem summable_Gp (y s : ℝ) : Summable fun n => Gp y n s := by
  by_cases hs : s ≤ y
  · simp only [Gp, Set.indicator_of_mem (show s ∈ Iic y from hs)]
    exact summable_Λq s
  · simp only [Gp, Set.indicator_of_notMem (show s ∉ Iic y from hs)]
    exact summable_zero

/-- **`ψ(e^u)` as a sum over prime powers below `e^u`.** -/
theorem hasSum_ite_Λ (u : ℝ) :
    HasSum (fun n : ℕ => if Real.log n ≤ u then Λ n else 0) (Chebyshev.psi (Real.exp u)) := by
  have hzero : ∀ n ∉ Finset.Ioc 0 ⌊Real.exp u⌋₊, (if Real.log n ≤ u then Λ n else 0) = 0 := by
    intro n hn
    rw [Finset.mem_Ioc, not_and_or] at hn
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · rcases hn with h | h
      · exact absurd hpos h
      · have hn1 : (0 : ℝ) < n := by exact_mod_cast hpos
        have hlt : Real.exp u < n := (Nat.floor_lt (Real.exp_pos u).le).1 (not_le.mp h)
        rw [ite_eq_right (not_le.mpr ((Real.lt_log_iff_exp_lt hn1).2 hlt))]
  have h : HasSum (fun n : ℕ => if Real.log n ≤ u then Λ n else 0)
      (∑ n ∈ Finset.Ioc 0 ⌊Real.exp u⌋₊, (if Real.log n ≤ u then Λ n else 0)) :=
    hasSum_sum_of_ne_finset_zero hzero
  convert h using 1
  show (∑ n ∈ Finset.Ioc 0 ⌊Real.exp u⌋₊, Λ n) = _
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Finset.mem_Ioc] at hn
  have hn1 : (0 : ℝ) < n := by exact_mod_cast hn.1
  have hnx : (n : ℝ) ≤ Real.exp u := (Nat.le_floor_iff (Real.exp_pos u).le).1 hn.2
  have hc : Real.log n ≤ u := by
    calc Real.log n ≤ Real.log (Real.exp u) := Real.log_le_log hn1 hnx
      _ = u := Real.log_exp u
  rw [ite_eq_left hc]

theorem Fp_eq_ite (y : ℝ) (n : ℕ) (u : ℝ) :
    Fp y n u = (if Real.log n ≤ u then Λ n else 0) * q (y - u) := by
  unfold Fp
  by_cases hu : Real.log n ≤ u
  · rw [Set.indicator_of_mem (show u ∈ Ici (Real.log n) from hu), ite_eq_left hu]
  · rw [Set.indicator_of_notMem (show u ∉ Ici (Real.log n) from hu), ite_eq_right hu, zero_mul]

theorem tsum_Fp (y u : ℝ) : ∑' n, Fp y n u = q (y - u) * Chebyshev.psi (Real.exp u) := by
  simp_rw [Fp_eq_ite]
  rw [tsum_mul_right, (hasSum_ite_Λ u).tsum_eq, mul_comm]

theorem summable_Fp (y u : ℝ) : Summable fun n => Fp y n u := by
  simp_rw [Fp_eq_ite]
  exact (hasSum_ite_Λ u).summable.mul_right _

/-- A crude growth bound, enough against the Gaussian kernel. -/
theorem psi_exp_le (u : ℝ) : Chebyshev.psi (Real.exp u) ≤ (Real.log 4 + 2) * Real.exp (2 * u) := by
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rcases lt_or_ge u 0 with hu | hu
  · have h1 : Real.exp u < 1 := by
      have := Real.exp_lt_exp.2 hu
      rwa [Real.exp_zero] at this
    have h0 : ⌊Real.exp u⌋₊ = 0 := Nat.floor_eq_zero.2 h1
    have hψ : Chebyshev.psi (Real.exp u) = 0 := by
      show (∑ n ∈ Finset.Ioc 0 ⌊Real.exp u⌋₊, Λ n) = 0
      rw [h0]
      simp
    rw [hψ]
    positivity
  · set x := Real.exp u with hx
    have hx1 : 1 ≤ x := Real.one_le_exp hu
    have h := Chebyshev.psi_le hx1
    have hs1 : 1 ≤ Real.sqrt x := Real.one_le_sqrt.2 hx1
    have hss : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
    have hsx : Real.sqrt x ≤ x := by nlinarith
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hlogx : Real.log x ≤ x := Real.log_le_self (by linarith)
    have hx2 : Real.exp (2 * u) = x * x := by
      rw [hx, ← Real.exp_add]
      ring_nf
    rw [hx2]
    have h3 : 2 * Real.sqrt x * Real.log x ≤ 2 * x * x := by
      have := mul_le_mul hsx hlogx hlog0 (by linarith)
      linarith
    have h4 : Real.log 4 * x ≤ Real.log 4 * (x * x) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hl4
    nlinarith

theorem integrable_q_psi (y : ℝ) : Integrable (fun u => q (y - u) * Chebyshev.psi (Real.exp u)) := by
  have hmeas : AEStronglyMeasurable (fun u => q (y - u) * Chebyshev.psi (Real.exp u)) volume :=
    ((continuous_q.comp (continuous_const.sub continuous_id)).measurable.mul
      (Chebyshev.psi_mono.comp Real.exp_monotone).measurable).aestronglyMeasurable
  refine ((integrable_q_shift_mul_exp y 2).const_mul (Real.log 4 + 2)).mono' hmeas
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (q_nonneg _) (Chebyshev.psi_nonneg _))]
  calc q (y - u) * Chebyshev.psi (Real.exp u) ≤ q (y - u) * ((Real.log 4 + 2) * Real.exp (2 * u)) :=
        mul_le_mul_of_nonneg_left (psi_exp_le u) (q_nonneg _)
    _ = (Real.log 4 + 2) * (q (y - u) * Real.exp (2 * u)) := by ring

/-- **The positive-kernel representation**: `e^{y/2} V(y) = ∫ q(y − u) ψ(e^u) du`. -/
theorem exp_mul_V_eq_integral_psi (y : ℝ) :
    Real.exp (y / 2) * V y = ∫ u : ℝ, q (y - u) * Chebyshev.psi (Real.exp u) := by
  rw [exp_mul_V]
  have hB : ∫ s in Iic y, P s = ∑' n, ∫ s, Gp y n s := by
    rw [← integral_indicator measurableSet_Iic]
    have heq : (Iic y).indicator P = fun s => ∑' n, Gp y n s := funext fun s => (tsum_Gp y s).symm
    rw [heq]
    refine integral_tsum_of_nonneg' (fun n s => Gp_nonneg y n s) (fun n => ?_) (summable_Gp y) ?_
    · exact ((continuous_const.mul (continuous_q.comp (continuous_id.sub continuous_const))).aestronglyMeasurable).indicator
        measurableSet_Iic
    · rw [← heq]
      exact (integrable_indicator_iff measurableSet_Iic).2 (integrableOn_P_Iic y)
  have hA : ∫ u, q (y - u) * Chebyshev.psi (Real.exp u) = ∑' n, ∫ u, Fp y n u := by
    have heq : (fun u => q (y - u) * Chebyshev.psi (Real.exp u)) = fun u => ∑' n, Fp y n u :=
      funext fun u => (tsum_Fp y u).symm
    rw [heq]
    refine integral_tsum_of_nonneg' (fun n u => Fp_nonneg y n u) (fun n => ?_) (summable_Fp y) ?_
    · exact ((continuous_const.mul (continuous_q.comp (continuous_const.sub continuous_id))).aestronglyMeasurable).indicator
        measurableSet_Ici
    · rw [← heq]
      exact integrable_q_psi y
  rw [hB, hA]
  exact tsum_congr fun n => integral_Gp_eq y n

/-! ## 3. The one-sided Chebyshev bound passes to the integrated form -/

theorem LowerBoundInt.mono {θ θ' : ℝ} (hθ : θ ≤ θ') (h : LowerBoundInt θ) : LowerBoundInt θ' := by
  obtain ⟨C, hC⟩ := h
  refine ⟨max C 0, fun y hy => ?_⟩
  have h1 := hC y hy
  have h2 : C * Real.exp (θ * y) ≤ max C 0 * Real.exp (θ' * y) := by
    calc C * Real.exp (θ * y) ≤ max C 0 * Real.exp (θ * y) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ ≤ max C 0 * Real.exp (θ' * y) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hθ hy))
            (le_max_right _ _)
  linarith

/-- The integrated dial's end `θ = ½` holds unconditionally (`V ≥ 0`). -/
theorem lowerBoundInt_half : LowerBoundInt (1 / 2) :=
  ⟨D, fun y _ => by
    rw [show (1 / 2 : ℝ) * y = y / 2 by ring, sub_self]
    exact V_nonneg y⟩

/-- **The classical one-sided Chebyshev bound implies the integrated input**, with the same exponent:
`ψ(t) ≥ t − C t^{½+θ}` for all `t ≥ 1` gives `LowerBoundInt θ` (`θ ≤ ½`). -/
theorem lowerBoundInt_of_psi {θ : ℝ} (hθ1 : θ ≤ 1 / 2) {C : ℝ}
    (hC : ∀ t : ℝ, 1 ≤ t → t - C * t ^ (1 / 2 + θ) ≤ Chebyshev.psi t) : LowerBoundInt θ := by
  set C₁ := max C 1 with hC₁
  set Kθ := Real.sqrt Real.pi * Real.exp (θ ^ 2 / 4) with hKθ
  refine ⟨C₁ * Kθ, fun y _ => ?_⟩
  have hpt : ∀ u : ℝ, q (y - u) * (Real.exp (1 * u) - C₁ * Real.exp ((1 / 2 + θ) * u))
      ≤ q (y - u) * Chebyshev.psi (Real.exp u) := by
    intro u
    refine mul_le_mul_of_nonneg_left ?_ (q_nonneg _)
    rw [one_mul]
    rcases le_or_gt 0 u with hu | hu
    · have h1 := hC (Real.exp u) (Real.one_le_exp hu)
      rw [← Real.exp_mul] at h1
      have h2 : C * Real.exp (u * (1 / 2 + θ)) ≤ C₁ * Real.exp ((1 / 2 + θ) * u) := by
        rw [mul_comm u]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      linarith
    · have hψ := Chebyshev.psi_nonneg (Real.exp u)
      have hprod : 0 ≤ (1 / 2 - θ) * (-u) := mul_nonneg (by linarith) (by linarith)
      have h2 : Real.exp u ≤ Real.exp ((1 / 2 + θ) * u) := Real.exp_le_exp.2 (by nlinarith)
      have h3 : Real.exp ((1 / 2 + θ) * u) ≤ C₁ * Real.exp ((1 / 2 + θ) * u) :=
        le_mul_of_one_le_left (Real.exp_pos _).le (le_max_right _ _)
      linarith
  have hi1 := integrable_q_shift_mul_exp y 1
  have hi2 := integrable_q_shift_mul_exp y (1 / 2 + θ)
  have hlow : ∫ u, q (y - u) * (Real.exp (1 * u) - C₁ * Real.exp ((1 / 2 + θ) * u))
      = D * Real.exp y - C₁ * Kθ * Real.exp ((1 / 2 + θ) * y) := by
    have hsplit : (fun u => q (y - u) * (Real.exp (1 * u) - C₁ * Real.exp ((1 / 2 + θ) * u)))
        = fun u => q (y - u) * Real.exp (1 * u) - C₁ * (q (y - u) * Real.exp ((1 / 2 + θ) * u)) := by
      funext u
      ring
    rw [hsplit, integral_sub hi1 (hi2.const_mul C₁), integral_const_mul, integral_q_shift_mul_exp,
      integral_q_shift_mul_exp, one_mul, D]
    rw [show ((1 : ℝ) - 1 / 2) ^ 2 / 4 = 1 / 16 by norm_num,
      show (1 / 2 + θ - 1 / 2) ^ 2 / 4 = θ ^ 2 / 4 by ring]
    ring
  have hmono := integral_mono ((hi1.sub (hi2.const_mul C₁)).congr (Eventually.of_forall fun u => by
    simp only [Pi.sub_apply]
    ring)) (integrable_q_psi y) hpt
  rw [← exp_mul_V_eq_integral_psi, hlow] at hmono
  set E := Real.exp (y / 2) with hE
  set T := Real.exp (θ * y) with hT
  have hEpos : 0 < E := Real.exp_pos _
  have hy1 : Real.exp y = E * E := by
    rw [hE, ← Real.exp_add]
    ring_nf
  have hy2 : Real.exp ((1 / 2 + θ) * y) = E * T := by
    rw [hE, hT, ← Real.exp_add]
    ring_nf
  rw [hy1, hy2] at hmono
  have key : E * (D * E - C₁ * Kθ * T) ≤ E * V y := by nlinarith
  exact le_of_mul_le_mul_left key hEpos

/-- **The one-sided Chebyshev bound at every exponent `½ + θ`, `θ ∈ (0, ½]`, gives `RiemannHypothesis`**, through
the integrated form (positive kernel, Landau, reflection). -/
theorem riemannHypothesis_of_psi_lowerBound
    (h : ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 →
      ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t → t - C * t ^ (1 / 2 + θ) ≤ Chebyshev.psi t) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_forall_lowerBoundInt fun θ hθ => ?_
  rcases le_or_gt θ (1 / 2) with hθ1 | hθ1
  · obtain ⟨C, hC⟩ := h θ hθ hθ1
    exact lowerBoundInt_of_psi hθ1 hC
  · exact lowerBoundInt_half.mono hθ1.le

end SmoothedPrimeSignal
