import RequestProject.ThetaWronskianSuzukiGram

/-!
# The Rouché numerator: uniform strip bounds for the extent tail

The first two links of the explicit tail bound `B(U,Y)` for
`E_U(z) = Ξ_∞(z) − Ξ_U(z) = 2∫_U^∞ Φ(u)cos(zu)du`, both unconditional and
elementary:

* `cos_strip_bound` — `‖cos(zu)‖ ≤ e^{Yu}` for `u ≥ 0`, `|Im z| ≤ Y`: the
  only place the complex frequency enters, and it enters as a single
  exponential in the extent.
* `kernel_term_abs_bound` — `|Φ_n(u)| ≤ 2π²(n+1)⁴e^{9u/2}e^{−π(n+1)²e^{2u}}`
  for `u ≥ 0`: mode-wise domination — the negative part never exceeds the
  positive part's scale.

Their product is the integrand bound whose `∫_U^∞` is the incomplete-Γ
expression, i.e. the numerator side of the Rouché front `X ≈ 4e^{2U}`
(the kernel's cutoff at `πe^{2U}` against the ξ-envelope's rate `π/4`).

No `sorry`, no `axiom`.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.ThetaWronskianSuzukiGram

/-- **The strip bound on the oscillatory factor**: complex frequency costs
exactly one exponential in the extent. -/
theorem cos_strip_bound {z : ℂ} {u Y : ℝ} (hu : 0 ≤ u) (hz : |z.im| ≤ Y) :
    ‖Complex.cos (z * u)‖ ≤ Real.exp (Y * u) := by
  have hb := abs_le.mp hz
  have hA : ‖Complex.exp (-(z * ↑u * Complex.I))‖ ≤ Real.exp (Y * u) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (-(z * ↑u * Complex.I)).re = z.im * u := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    nlinarith [hb.1, hb.2]
  have hB : ‖Complex.exp (z * ↑u * Complex.I)‖ ≤ Real.exp (Y * u) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (z * ↑u * Complex.I).re = -(z.im * u) := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre]
    nlinarith [hb.1, hb.2]
  rw [Complex.cos]
  simp only [neg_mul]
  rw [norm_div]
  have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2n]
  have hsum := norm_add_le (Complex.exp (z * ↑u * Complex.I))
    (Complex.exp (-(z * ↑u * Complex.I)))
  linarith

/-- The mode-domination inequality, as a statement about real parameters. -/
theorem kernel_bound_aux {r u : ℝ} (hr1 : 1 ≤ r) (hu : 0 ≤ u) :
    |(2 * Real.pi ^ 2 * r ^ 4 * Real.exp (9 * u / 2)
        - 3 * Real.pi * r ^ 2 * Real.exp (5 * u / 2))
      * Real.exp (-Real.pi * r ^ 2 * Real.exp (2 * u))|
      ≤ 2 * Real.pi ^ 2 * r ^ 4 * Real.exp (9 * u / 2)
        * Real.exp (-Real.pi * r ^ 2 * Real.exp (2 * u)) := by
  have hE : (0:ℝ) < Real.exp (-Real.pi * r ^ 2 * Real.exp (2 * u)) :=
    Real.exp_pos _
  have h59 : Real.exp (5 * u / 2) ≤ Real.exp (9 * u / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have h5pos : (0:ℝ) < Real.exp (5 * u / 2) := Real.exp_pos _
  have h9pos : (0:ℝ) < Real.exp (9 * u / 2) := Real.exp_pos _
  have hr0 : (0:ℝ) < r := by linarith
  have hrsq : (1:ℝ) ≤ r ^ 2 := by nlinarith
  have hr24 : r ^ 2 ≤ r ^ 4 := by nlinarith
  have hpi3 : (3:ℝ) < Real.pi := Real.pi_gt_three
  have hpipos : (0:ℝ) < Real.pi := Real.pi_pos
  have hpi : (3:ℝ) * Real.pi ≤ 4 * Real.pi ^ 2 := by nlinarith
  rw [abs_mul, abs_of_pos hE]
  apply mul_le_mul_of_nonneg_right _ hE.le
  rw [abs_le]
  have hprod : r ^ 2 * Real.exp (5 * u / 2) ≤ r ^ 4 * Real.exp (9 * u / 2) :=
    mul_le_mul hr24 h59 h5pos.le (by positivity)
  have hstep : 3 * Real.pi * r ^ 2 * Real.exp (5 * u / 2)
      ≤ 4 * Real.pi ^ 2 * r ^ 4 * Real.exp (9 * u / 2) := by
    calc 3 * Real.pi * r ^ 2 * Real.exp (5 * u / 2)
        = (3 * Real.pi) * (r ^ 2 * Real.exp (5 * u / 2)) := by ring
      _ ≤ (3 * Real.pi) * (r ^ 4 * Real.exp (9 * u / 2)) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ ≤ (4 * Real.pi ^ 2) * (r ^ 4 * Real.exp (9 * u / 2)) :=
          mul_le_mul_of_nonneg_right hpi (by positivity)
      _ = 4 * Real.pi ^ 2 * r ^ 4 * Real.exp (9 * u / 2) := by ring
  constructor
  · linarith
  · have hpos : (0:ℝ) ≤ 3 * Real.pi * r ^ 2 * Real.exp (5 * u / 2) := by
      positivity
    linarith

/-- **Mode-wise domination of the kernel**: each Riemann mode is dominated
by its Gaussian head, uniformly on `u ≥ 0`. -/
theorem kernel_term_abs_bound (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |riemannXiKernelTerm n u|
      ≤ 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u / 2)
        * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u)) := by
  have hr1 : (1:ℝ) ≤ (n : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  simpa only [riemannXiKernelTerm] using kernel_bound_aux hr1 hu


/-- **The tail integrand bound**: the product of the two links — this is
the function whose `∫_U^∞` is the incomplete-Γ expression `B(U,Y)`, i.e.
the Rouché numerator.  Doubly-exponential in `u`, so integrable on
`[U,∞)` for every `Y`. -/
theorem mode_integrand_bound (n : ℕ) {u Y : ℝ} (hu : 0 ≤ u)
    {z : ℂ} (hz : |z.im| ≤ Y) :
    ‖(riemannXiKernelTerm n u : ℂ) * Complex.cos (z * u)‖
      ≤ (2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u / 2)
          * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u)))
        * Real.exp (Y * u) := by
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul (kernel_term_abs_bound n hu) (cos_strip_bound hu hz)
    (norm_nonneg _) (by positivity)

/-- **Exponential domination of the tail integrand** for `u ≥ U`: convexity
of the inner clock (`e^{2u} ≥ e^{2U}(1 + 2(u−U))`) converts the
doubly-exponential decay into a pure exponential with rate
`c = 2πe^{2U} − 9/2 − Y`. -/
theorem mode_tail_exp_domination (n : ℕ) {u U Y : ℝ} (hU : 0 ≤ U)
    (hu : U ≤ u) (hY : 0 ≤ Y) {z : ℂ} (hz : |z.im| ≤ Y) :
    ‖(riemannXiKernelTerm n u : ℂ) * Complex.cos (z * u)‖
      ≤ (2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp ((9/2 + Y) * U)
          * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * U)))
        * Real.exp (-(2 * Real.pi * Real.exp (2 * U) - 9/2 - Y) * (u - U)) := by
  have hu0 : 0 ≤ u := le_trans hU hu
  refine le_trans (mode_integrand_bound n hu0 hz) ?_
  have hL : (2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp (9 * u / 2)
        * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u)))
        * Real.exp (Y * u)
      = 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4
        * Real.exp (9 * u / 2 + -Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * u)
            + Y * u) := by
    rw [Real.exp_add, Real.exp_add]
    ring
  have hR : (2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp ((9/2 + Y) * U)
        * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * U)))
        * Real.exp (-(2 * Real.pi * Real.exp (2 * U) - 9/2 - Y) * (u - U))
      = 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4
        * Real.exp ((9/2 + Y) * U + -Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * U)
            + -(2 * Real.pi * Real.exp (2 * U) - 9/2 - Y) * (u - U)) := by
    rw [Real.exp_add, Real.exp_add]
    ring
  rw [hL, hR]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  -- exponent inequality ⟺ 2πe^{2U}(u−U) ≤ π(n+1)²(e^{2u} − e^{2U})
  have hconv : 2 * Real.exp (2 * U) * (u - U)
      ≤ Real.exp (2 * u) - Real.exp (2 * U) := by
    have h1 : 2 * (u - U) + 1 ≤ Real.exp (2 * (u - U)) := by
      have := Real.add_one_le_exp (2 * (u - U))
      linarith
    have h2 : Real.exp (2 * u) = Real.exp (2 * U) * Real.exp (2 * (u - U)) := by
      rw [← Real.exp_add]
      ring_nf
    nlinarith [Real.exp_pos (2 * U)]
  have hr2 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by
    have := Nat.cast_nonneg (α := ℝ) n
    nlinarith
  have hnonneg : 0 ≤ Real.exp (2 * u) - Real.exp (2 * U) := by
    have h0 : (0:ℝ) ≤ 2 * Real.exp (2 * U) * (u - U) := by
      have := Real.exp_pos (2 * U)
      nlinarith
    linarith [hconv]
  have hs1 : Real.pi * (Real.exp (2 * u) - Real.exp (2 * U))
      ≤ Real.pi * (((n : ℝ) + 1) ^ 2 * (Real.exp (2 * u) - Real.exp (2 * U))) :=
    mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hnonneg hr2) Real.pi_pos.le
  have hs2 : Real.pi * (2 * Real.exp (2 * U) * (u - U))
      ≤ Real.pi * (Real.exp (2 * u) - Real.exp (2 * U)) := by
    nlinarith [hconv, Real.pi_pos]
  nlinarith [hs1, hs2]

/-- **The mode tail integral bound — the L2 link, closed form**: beyond
extent `U`, each Riemann mode's tail integral is at most an explicit
incomplete-Γ-type expression, uniformly on the strip `|Im z| ≤ Y`.  The
bound is doubly-exponentially small in `U`: the quantitative content of
`Ξ_U → Ξ` on every strip, per mode. -/
theorem mode_tail_integral_bound (n : ℕ) {U Y : ℝ} (hU : 0 ≤ U) (hY : 0 ≤ Y)
    (hc : 9/2 + Y < 2 * Real.pi * Real.exp (2 * U)) {z : ℂ} (hz : |z.im| ≤ Y) :
    ∫ u in Set.Ioi U, ‖(riemannXiKernelTerm n u : ℂ) * Complex.cos (z * u)‖
      ≤ (2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp ((9/2 + Y) * U)
          * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * U)))
        / (2 * Real.pi * Real.exp (2 * U) - 9/2 - Y) := by
  set c' : ℝ := 2 * Real.pi * Real.exp (2 * U) - 9/2 - Y with hc'
  have hc0 : 0 < c' := by
    rw [hc']
    linarith
  set A : ℝ := 2 * Real.pi ^ 2 * ((n : ℝ) + 1) ^ 4 * Real.exp ((9/2 + Y) * U)
      * Real.exp (-Real.pi * ((n : ℝ) + 1) ^ 2 * Real.exp (2 * U)) with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    positivity
  clear_value c' A
  have hfun : (fun u : ℝ => A * Real.exp (-c' * (u - U)))
      = fun u : ℝ => (A * Real.exp (c' * U)) * Real.exp (-c' * u) := by
    funext u
    rw [mul_assoc, ← Real.exp_add,
      show c' * U + -c' * u = -c' * (u - U) by ring]
  have hmaj : MeasureTheory.IntegrableOn
      (fun u : ℝ => A * Real.exp (-c' * (u - U))) (Set.Ioi U) := by
    rw [hfun]
    exact (exp_neg_integrableOn_Ioi U hc0).const_mul _
  have hle : ∫ u in Set.Ioi U,
        ‖(riemannXiKernelTerm n u : ℂ) * Complex.cos (z * u)‖
      ≤ ∫ u in Set.Ioi U, A * Real.exp (-c' * (u - U)) := by
    apply MeasureTheory.integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun u => norm_nonneg _)
    · exact hmaj
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      rw [hA, hc']
      exact mode_tail_exp_domination n hU (le_of_lt hu) hY hz
  have hval : ∫ u in Set.Ioi U, A * Real.exp (-c' * (u - U)) = A / c' := by
    rw [hfun, MeasureTheory.integral_const_mul,
      integral_exp_mul_Ioi (by linarith : -c' < 0) U]
    rw [show -c' * U = -(c' * U) by ring, Real.exp_neg]
    field_simp
  calc ∫ u in Set.Ioi U,
        ‖(riemannXiKernelTerm n u : ℂ) * Complex.cos (z * u)‖
      ≤ ∫ u in Set.Ioi U, A * Real.exp (-c' * (u - U)) := hle
    _ = A / c' := hval

/-- Mode-decay core: `m⁴e^{−πm²} ≤ e^{−m}` for `m ≥ 1` — the whole mode
ladder is dominated by one geometric series. -/
theorem pow_four_mul_exp_le {m : ℕ} (hm : 1 ≤ m) :
    ((m : ℝ)) ^ 4 * Real.exp (-Real.pi * (m : ℝ) ^ 2) ≤ Real.exp (-(m : ℝ)) := by
  have hm1 : (1:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  have hm0 : (0:ℝ) < (m:ℝ) := by linarith
  have hlog : Real.log (m:ℝ) ≤ (m:ℝ) - 1 := Real.log_le_sub_one_of_pos hm0
  have hpow : ((m:ℝ))^4 = Real.exp (4 * Real.log (m:ℝ)) := by
    rw [show (4:ℝ) * Real.log (m:ℝ)
        = Real.log (m:ℝ) + Real.log (m:ℝ) + Real.log (m:ℝ) + Real.log (m:ℝ)
      by ring, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log hm0]
    ring
  rw [hpow, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hπ : (3:ℝ) < Real.pi := Real.pi_gt_three
  nlinarith [hlog, sq_nonneg (2*(m:ℝ) - 3), hm1,
    mul_le_mul_of_nonneg_right hπ.le (sq_nonneg (m:ℝ))]

/-- Each mode's bound is dominated by a `u`-independent geometric factor
times the leading mode's profile. -/
theorem kernel_term_abs_le_geometric (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |riemannXiKernelTerm n u|
      ≤ (2 * Real.pi^2 * Real.exp Real.pi * Real.exp (9*u/2)
          * Real.exp (-Real.pi * Real.exp (2*u))) * Real.exp (-((n:ℝ)+1)) := by
  refine le_trans (kernel_term_abs_bound n hu) ?_
  have h2u : (1:ℝ) ≤ Real.exp (2*u) := by
    have := Real.add_one_le_exp (2*u)
    linarith
  have hnn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have h1 : (1:ℝ) ≤ ((n:ℝ)+1)^2 := by nlinarith
  have hA : Real.exp (-Real.pi * ((n:ℝ)+1)^2 * Real.exp (2*u))
      ≤ Real.exp (-Real.pi * Real.exp (2*u)) * Real.exp Real.pi
        * Real.exp (-(Real.pi * ((n:ℝ)+1)^2)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hprod : 0 ≤ Real.pi * (((n:ℝ)+1)^2 - 1) * (Real.exp (2*u) - 1) :=
      mul_nonneg (mul_nonneg Real.pi_pos.le (by linarith)) (by linarith)
    nlinarith [hprod]
  calc 2 * Real.pi ^ 2 * ((n:ℝ) + 1) ^ 4 * Real.exp (9 * u / 2)
        * Real.exp (-Real.pi * ((n:ℝ) + 1) ^ 2 * Real.exp (2 * u))
      ≤ 2 * Real.pi ^ 2 * ((n:ℝ) + 1) ^ 4 * Real.exp (9 * u / 2)
        * (Real.exp (-Real.pi * Real.exp (2*u)) * Real.exp Real.pi
            * Real.exp (-(Real.pi * ((n:ℝ)+1)^2))) := by
        apply mul_le_mul_of_nonneg_left hA (by positivity)
    _ = (2 * Real.pi^2 * Real.exp Real.pi * Real.exp (9*u/2)
          * Real.exp (-Real.pi * Real.exp (2*u)))
        * (((n:ℝ)+1)^4 * Real.exp (-(Real.pi * ((n:ℝ)+1)^2))) := by
        ring
    _ ≤ (2 * Real.pi^2 * Real.exp Real.pi * Real.exp (9*u/2)
          * Real.exp (-Real.pi * Real.exp (2*u))) * Real.exp (-((n:ℝ)+1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h := pow_four_mul_exp_le (m := n+1) (by omega)
        have hc : ((n+1 : ℕ) : ℝ) = (n:ℝ) + 1 := by push_cast; ring
        rw [hc] at h
        calc ((n:ℝ)+1)^4 * Real.exp (-(Real.pi * ((n:ℝ)+1)^2))
            = ((n:ℝ)+1)^4 * Real.exp (-Real.pi * ((n:ℝ)+1)^2) := by ring_nf
          _ ≤ Real.exp (-((n:ℝ)+1)) := h

/-- **The full-kernel pointwise bound**: the whole mode ladder is at most a
constant times the leading profile — `|Φ(u)| ≤ 8π²e^π·e^{9u/2}e^{−πe^{2u}}`
on `u ≥ 0`. -/
theorem kernel_abs_bound {u : ℝ} (hu : 0 ≤ u) :
    |riemannXiKernel u|
      ≤ 8 * Real.pi^2 * Real.exp Real.pi * Real.exp (9*u/2)
        * Real.exp (-Real.pi * Real.exp (2*u)) := by
  have hr0 : (0:ℝ) ≤ Real.exp (-1:ℝ) := (Real.exp_pos _).le
  have hr1 : Real.exp (-1:ℝ) < 1 := by
    rw [show (1:ℝ) = Real.exp 0 by rw [Real.exp_zero]]
    exact Real.exp_lt_exp.mpr (by norm_num)
  have hexpshift : ∀ n : ℕ, Real.exp (-((n:ℝ)+1)) = Real.exp (-1:ℝ)^(n+1) := by
    intro n
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hgeo : Summable (fun n : ℕ => Real.exp (-1:ℝ) ^ (n+1)) := by
    have hfun : (fun n : ℕ => Real.exp (-1:ℝ)^(n+1))
        = fun n : ℕ => Real.exp (-1:ℝ)^n * Real.exp (-1:ℝ) := by
      funext n
      rw [pow_succ]
    rw [hfun]
    exact (summable_geometric_of_lt_one hr0 hr1).mul_right _
  set C : ℝ := 2*Real.pi^2*Real.exp Real.pi*Real.exp (9*u/2)
      * Real.exp (-Real.pi*Real.exp (2*u)) with hC
  have hC0 : (0:ℝ) ≤ C := by rw [hC]; positivity
  have hmajor : Summable (fun n : ℕ => C * Real.exp (-((n:ℝ)+1))) := by
    simp_rw [hexpshift]
    exact hgeo.mul_left C
  have hsumabs : Summable (fun n : ℕ => |riemannXiKernelTerm n u|) :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _)
      (fun n => kernel_term_abs_le_geometric n hu) hmajor
  have htsum : |∑' n, riemannXiKernelTerm n u|
      ≤ ∑' n, |riemannXiKernelTerm n u| := by
    have h := norm_tsum_le_tsum_norm
      (f := fun n : ℕ => riemannXiKernelTerm n u)
      (by simpa [Real.norm_eq_abs] using hsumabs)
    simpa [Real.norm_eq_abs] using h
  have hbound : (∑' n : ℕ, |riemannXiKernelTerm n u|)
      ≤ ∑' n : ℕ, C * Real.exp (-((n:ℝ)+1)) :=
    hsumabs.tsum_le_tsum (fun n => kernel_term_abs_le_geometric n hu) hmajor
  have hgeoval : ∑' n : ℕ, C * Real.exp (-((n:ℝ)+1)) ≤ C := by
    have h1 : ∑' n : ℕ, C * Real.exp (-((n:ℝ)+1))
        = C * ∑' n : ℕ, Real.exp (-1:ℝ)^(n+1) := by
      rw [← tsum_mul_left]
      congr 1
      funext n
      rw [hexpshift]
    rw [h1]
    have h2 : ∑' n : ℕ, Real.exp (-1:ℝ)^(n+1) ≤ 1 := by
      have hval : ∑' n : ℕ, Real.exp (-1:ℝ)^(n+1)
          = (∑' n : ℕ, Real.exp (-1:ℝ)^n) * Real.exp (-1:ℝ) := by
        simp_rw [pow_succ]
        rw [tsum_mul_right]
      rw [hval, tsum_geometric_of_lt_one hr0 hr1]
      have he2 : (2:ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1:ℝ)
        linarith
      have hhalf : Real.exp (-1:ℝ) ≤ 1/2 := by
        have hprod1 : Real.exp (-1:ℝ) * Real.exp 1 = 1 := by
          rw [← Real.exp_add]
          norm_num
        nlinarith [hprod1, he2, mul_nonneg (Real.exp_pos (-1:ℝ)).le
          (by linarith : (0:ℝ) ≤ Real.exp 1 - 2)]
      have h1x : (0:ℝ) < 1 - Real.exp (-1:ℝ) := by linarith
      rw [show (1 - Real.exp (-1:ℝ))⁻¹ * Real.exp (-1:ℝ)
          = Real.exp (-1:ℝ) / (1 - Real.exp (-1:ℝ)) by
        rw [div_eq_mul_inv]; ring]
      rw [div_le_one h1x]
      linarith
    calc C * ∑' n : ℕ, Real.exp (-1:ℝ)^(n+1) ≤ C * 1 :=
        mul_le_mul_of_nonneg_left h2 hC0
      _ = C := mul_one C
  have hker : riemannXiKernel u = 4 * ∑' n, riemannXiKernelTerm n u := rfl
  rw [hker, abs_mul, show |(4:ℝ)| = 4 by norm_num]
  calc 4 * |∑' n, riemannXiKernelTerm n u|
      ≤ 4 * (∑' n, |riemannXiKernelTerm n u|) := by linarith [htsum]
    _ ≤ 4 * C := by linarith [hbound, hgeoval]
    _ = 8 * Real.pi^2 * Real.exp Real.pi * Real.exp (9*u/2)
        * Real.exp (-Real.pi * Real.exp (2*u)) := by
        rw [hC]; ring

/-- Exponential domination of the FULL-kernel tail integrand for `u ≥ U`. -/
theorem kernel_tail_exp_domination {u U Y : ℝ} (hU : 0 ≤ U) (hu : U ≤ u)
    (hY : 0 ≤ Y) {z : ℂ} (hz : |z.im| ≤ Y) :
    ‖(riemannXiKernel u : ℂ) * Complex.cos (z * u)‖
      ≤ (8 * Real.pi^2 * Real.exp Real.pi * Real.exp ((9/2 + Y) * U)
          * Real.exp (-Real.pi * Real.exp (2 * U)))
        * Real.exp (-(2 * Real.pi * Real.exp (2 * U) - 9/2 - Y) * (u - U)) := by
  have hu0 : 0 ≤ u := le_trans hU hu
  have hpt : ‖(riemannXiKernel u : ℂ) * Complex.cos (z * u)‖
      ≤ (8 * Real.pi^2 * Real.exp Real.pi * Real.exp (9*u/2)
          * Real.exp (-Real.pi * Real.exp (2*u))) * Real.exp (Y * u) := by
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul (kernel_abs_bound hu0) (cos_strip_bound hu0 hz)
      (norm_nonneg _) (by positivity)
  refine le_trans hpt ?_
  have hL : (8 * Real.pi^2 * Real.exp Real.pi * Real.exp (9*u/2)
        * Real.exp (-Real.pi * Real.exp (2*u))) * Real.exp (Y * u)
      = 8 * Real.pi^2 * Real.exp Real.pi
        * Real.exp (9*u/2 + -Real.pi * Real.exp (2*u) + Y*u) := by
    rw [Real.exp_add, Real.exp_add]
    ring
  have hR : (8 * Real.pi^2 * Real.exp Real.pi * Real.exp ((9/2 + Y) * U)
        * Real.exp (-Real.pi * Real.exp (2 * U)))
        * Real.exp (-(2 * Real.pi * Real.exp (2 * U) - 9/2 - Y) * (u - U))
      = 8 * Real.pi^2 * Real.exp Real.pi
        * Real.exp ((9/2 + Y) * U + -Real.pi * Real.exp (2 * U)
            + -(2 * Real.pi * Real.exp (2 * U) - 9/2 - Y) * (u - U)) := by
    rw [Real.exp_add, Real.exp_add]
    ring
  rw [hL, hR]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  have hconv : 2 * Real.exp (2 * U) * (u - U)
      ≤ Real.exp (2 * u) - Real.exp (2 * U) := by
    have h1 : 2 * (u - U) + 1 ≤ Real.exp (2 * (u - U)) := by
      have := Real.add_one_le_exp (2 * (u - U))
      linarith
    have h2 : Real.exp (2 * u) = Real.exp (2 * U) * Real.exp (2 * (u - U)) := by
      rw [← Real.exp_add]
      ring_nf
    nlinarith [Real.exp_pos (2 * U)]
  have hs2 : Real.pi * (2 * Real.exp (2 * U) * (u - U))
      ≤ Real.pi * (Real.exp (2 * u) - Real.exp (2 * U)) := by
    nlinarith [hconv, Real.pi_pos]
  nlinarith [hs2]

/-- **The full-kernel tail integral bound — L2 complete**: beyond extent `U`
the whole tail `2∫_U^∞ Φ(u)cos(zu)du` is dominated, in norm and in closed
form, by a doubly-exponentially small quantity, uniformly on the strip
`|Im z| ≤ Y`.  Together with the (uncompiled classical) representation
`Ξ = 2∫₀^∞ Φcos`, this is the quantitative content of `Ξ_U → Ξ`. -/
theorem kernel_tail_integral_bound {U Y : ℝ} (hU : 0 ≤ U) (hY : 0 ≤ Y)
    (hc : 9/2 + Y < 2 * Real.pi * Real.exp (2 * U)) {z : ℂ} (hz : |z.im| ≤ Y) :
    ∫ u in Set.Ioi U, ‖(riemannXiKernel u : ℂ) * Complex.cos (z * u)‖
      ≤ (8 * Real.pi^2 * Real.exp Real.pi * Real.exp ((9/2 + Y) * U)
          * Real.exp (-Real.pi * Real.exp (2 * U)))
        / (2 * Real.pi * Real.exp (2 * U) - 9/2 - Y) := by
  set c' : ℝ := 2 * Real.pi * Real.exp (2 * U) - 9/2 - Y with hc'
  have hc0 : 0 < c' := by
    rw [hc']
    linarith
  set A : ℝ := 8 * Real.pi^2 * Real.exp Real.pi * Real.exp ((9/2 + Y) * U)
      * Real.exp (-Real.pi * Real.exp (2 * U)) with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    positivity
  clear_value c' A
  have hfun : (fun u : ℝ => A * Real.exp (-c' * (u - U)))
      = fun u : ℝ => (A * Real.exp (c' * U)) * Real.exp (-c' * u) := by
    funext u
    rw [mul_assoc, ← Real.exp_add,
      show c' * U + -c' * u = -c' * (u - U) by ring]
  have hmaj : MeasureTheory.IntegrableOn
      (fun u : ℝ => A * Real.exp (-c' * (u - U))) (Set.Ioi U) := by
    rw [hfun]
    exact (exp_neg_integrableOn_Ioi U hc0).const_mul _
  have hle : ∫ u in Set.Ioi U,
        ‖(riemannXiKernel u : ℂ) * Complex.cos (z * u)‖
      ≤ ∫ u in Set.Ioi U, A * Real.exp (-c' * (u - U)) := by
    apply MeasureTheory.integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall (fun u => norm_nonneg _)
    · exact hmaj
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      rw [hA, hc']
      exact kernel_tail_exp_domination hU (le_of_lt hu) hY hz
  have hval : ∫ u in Set.Ioi U, A * Real.exp (-c' * (u - U)) = A / c' := by
    rw [hfun, MeasureTheory.integral_const_mul,
      integral_exp_mul_Ioi (by linarith : -c' < 0) U]
    rw [show -c' * U = -(c' * U) by ring, Real.exp_neg]
    field_simp
  calc ∫ u in Set.Ioi U,
        ‖(riemannXiKernel u : ℂ) * Complex.cos (z * u)‖
      ≤ ∫ u in Set.Ioi U, A * Real.exp (-c' * (u - U)) := hle
    _ = A / c' := hval

/-- The Xi integrand is integrable beyond any extent `U` in the admissible
range — domination by the pure exponential of `kernel_tail_exp_domination`. -/
theorem xiIntegrand_integrableOn_Ioi {U Y : ℝ} (hU : 0 ≤ U) (hY : 0 ≤ Y)
    (hc : 9/2 + Y < 2 * Real.pi * Real.exp (2 * U)) {z : ℂ} (hz : |z.im| ≤ Y) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => (riemannXiKernel u : ℂ) * Complex.cos (z * u))
      (Set.Ioi U) := by
  set c' : ℝ := 2 * Real.pi * Real.exp (2 * U) - 9/2 - Y with hc'
  have hc0 : 0 < c' := by
    rw [hc']
    linarith
  set A : ℝ := 8 * Real.pi^2 * Real.exp Real.pi * Real.exp ((9/2 + Y) * U)
      * Real.exp (-Real.pi * Real.exp (2 * U)) with hA
  clear_value c' A
  have hfun : (fun u : ℝ => A * Real.exp (-c' * (u - U)))
      = fun u : ℝ => (A * Real.exp (c' * U)) * Real.exp (-c' * u) := by
    funext u
    rw [mul_assoc, ← Real.exp_add,
      show c' * U + -c' * u = -c' * (u - U) by ring]
  have hmaj : MeasureTheory.IntegrableOn
      (fun u : ℝ => A * Real.exp (-c' * (u - U))) (Set.Ioi U) := by
    rw [hfun]
    exact (exp_neg_integrableOn_Ioi U hc0).const_mul _
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun u : ℝ => (riemannXiKernel u : ℂ) * Complex.cos (z * u))
      (MeasureTheory.volume.restrict (Set.Ioi U)) := by
    apply Measurable.aestronglyMeasurable
    exact (Complex.measurable_ofReal.comp riemannXiKernel_measurable).mul
      (Complex.continuous_cos.comp
        (continuous_const.mul Complex.continuous_ofReal)).measurable
  apply MeasureTheory.Integrable.mono' hmaj hmeas
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
  rw [hA, hc']
  exact kernel_tail_exp_domination hU (le_of_lt hu) hY hz

/-- The Xi integrand is integrable on any initial segment — continuity of
the compiled kernel on its physical half-line. -/
theorem xiIntegrand_integrableOn_Ioc (U : ℝ) (z : ℂ) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => (riemannXiKernel u : ℂ) * Complex.cos (z * u))
      (Set.Ioc 0 U) := by
  have hcont : ContinuousOn
      (fun u : ℝ => (riemannXiKernel u : ℂ) * Complex.cos (z * u))
      (Set.Icc 0 U) := by
    apply ContinuousOn.mul
    · exact Complex.continuous_ofReal.comp_continuousOn
        (riemannXiKernel_continuousOn.mono (fun x hx => hx.1))
    · exact (Complex.continuous_cos.comp
        (continuous_const.mul Complex.continuous_ofReal)).continuousOn
  exact (hcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self

/-- **The Xi integrand is integrable on the whole half-line**, for every
frequency `z` — the integral object `2∫₀^∞ Φ(u)cos(zu)du` is well-defined. -/
theorem xiIntegrand_integrableOn (z : ℂ) :
    MeasureTheory.IntegrableOn
      (fun u : ℝ => (riemannXiKernel u : ℂ) * Complex.cos (z * u))
      (Set.Ioi 0) := by
  set Y : ℝ := |z.im| with hY
  have hY0 : 0 ≤ Y := abs_nonneg _
  have hc : 9/2 + Y < 2 * Real.pi * Real.exp (2 * Y) := by
    have h1 : 2 * Y + 1 ≤ Real.exp (2 * Y) := by
      have := Real.add_one_le_exp (2 * Y)
      linarith
    nlinarith [Real.pi_gt_three]
  have hsplit : Set.Ioc (0:ℝ) Y ∪ Set.Ioi Y = Set.Ioi (0:ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi hY0
  rw [← hsplit]
  exact MeasureTheory.IntegrableOn.union
    (xiIntegrand_integrableOn_Ioc Y z)
    (xiIntegrand_integrableOn_Ioi hY0 hY0 hc (le_refl Y))

/-- The finite-extent stage of the Xi cosine transform. -/
noncomputable def xiStage (U : ℝ) (z : ℂ) : ℂ :=
  2 * ∫ u in Set.Ioc 0 U, (riemannXiKernel u : ℂ) * Complex.cos (z * u)

/-- The full Xi cosine transform — the integral object of the route.
Its identification with `ZD.riemannXi` on the spectral chart is the L1
representation (Riemann 1859), the route's remaining classical-labor item. -/
noncomputable def xiIntegral (z : ℂ) : ℂ :=
  2 * ∫ u in Set.Ioi 0, (riemannXiKernel u : ℂ) * Complex.cos (z * u)

/-- **Stage convergence with explicit rate**: the stage differs from the
full integral object by at most `2·B(U,Y)` — doubly-exponentially small in
the extent, uniformly on every strip. -/
theorem xiIntegral_sub_stage_bound {U Y : ℝ} (hU : 0 ≤ U) (hY : 0 ≤ Y)
    (hc : 9/2 + Y < 2 * Real.pi * Real.exp (2 * U)) {z : ℂ} (hz : |z.im| ≤ Y) :
    ‖xiIntegral z - xiStage U z‖
      ≤ 2 * ((8 * Real.pi^2 * Real.exp Real.pi * Real.exp ((9/2 + Y) * U)
          * Real.exp (-Real.pi * Real.exp (2 * U)))
        / (2 * Real.pi * Real.exp (2 * U) - 9/2 - Y)) := by
  have hIoc := xiIntegrand_integrableOn_Ioc U z
  have hIoi := xiIntegrand_integrableOn_Ioi hU hY hc hz
  have hsplit : Set.Ioc (0:ℝ) U ∪ Set.Ioi U = Set.Ioi (0:ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi hU
  have hdisj : Disjoint (Set.Ioc (0:ℝ) U) (Set.Ioi U) := by
    apply Set.disjoint_left.mpr
    intro x hx1 hx2
    exact absurd hx1.2 (not_le.mpr hx2)
  have hint : ∫ u in Set.Ioi (0:ℝ),
        (riemannXiKernel u : ℂ) * Complex.cos (z * u)
      = (∫ u in Set.Ioc 0 U, (riemannXiKernel u : ℂ) * Complex.cos (z * u))
        + ∫ u in Set.Ioi U, (riemannXiKernel u : ℂ) * Complex.cos (z * u) := by
    rw [← hsplit]
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioi hIoc hIoi
  have hdiff : xiIntegral z - xiStage U z
      = 2 * ∫ u in Set.Ioi U, (riemannXiKernel u : ℂ) * Complex.cos (z * u) := by
    unfold xiIntegral xiStage
    rw [hint]
    ring
  rw [hdiff]
  rw [norm_mul, show ‖(2:ℂ)‖ = 2 by norm_num]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc ‖∫ u in Set.Ioi U, (riemannXiKernel u : ℂ) * Complex.cos (z * u)‖
      ≤ ∫ u in Set.Ioi U, ‖(riemannXiKernel u : ℂ) * Complex.cos (z * u)‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ _ := kernel_tail_integral_bound hU hY hc hz

/-- **Stage convergence, compiled**: the finite-extent stages converge to the
integral object at every frequency — the doubly-exponential tail bound
squeezed to zero along the extent. -/
theorem xiStage_tendsto_xiIntegral (z : ℂ) :
    Filter.Tendsto (fun n : ℕ => xiStage n z) Filter.atTop
      (nhds (xiIntegral z)) := by
  set Y : ℝ := |z.im| with hY
  have hY0 : 0 ≤ Y := abs_nonneg _
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set N : ℕ := ⌈Y⌉₊ + 4 with hN
  have hYle : ∀ n : ℕ, N ≤ n → Y ≤ (n:ℝ) := by
    intro n hn
    have h1 : Y ≤ (⌈Y⌉₊ : ℝ) := Nat.le_ceil Y
    have h2 : ((⌈Y⌉₊ : ℕ) : ℝ) ≤ (n:ℝ) := by
      exact_mod_cast le_trans (by omega : ⌈Y⌉₊ ≤ N) hn
    linarith
  have hexp2 : ∀ n : ℕ, (1 + (n:ℝ))^2 ≤ Real.exp (2*(n:ℝ)) := by
    intro n
    have h1 : 1 + (n:ℝ) ≤ Real.exp (n:ℝ) := by
      have := Real.add_one_le_exp ((n:ℝ))
      linarith
    have h2 : Real.exp (2*(n:ℝ)) = Real.exp (n:ℝ) * Real.exp (n:ℝ) := by
      rw [← Real.exp_add]
      ring_nf
    nlinarith [Nat.cast_nonneg (α := ℝ) n, Real.exp_pos ((n:ℝ))]
  have hcev : ∀ n : ℕ, N ≤ n →
      9/2 + Y + 1 ≤ 2 * Real.pi * Real.exp (2*(n:ℝ)) := by
    intro n hn
    have h1 := hexp2 n
    have h2 := hYle n hn
    have hπ := Real.pi_gt_three
    have hn4 : (4:ℝ) ≤ (n:ℝ) := by
      exact_mod_cast le_trans (by omega : 4 ≤ N) hn
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have hAev : ∀ n : ℕ, N ≤ n →
      Real.exp ((9/2 + Y) * (n:ℝ)) * Real.exp (-Real.pi * Real.exp (2*(n:ℝ)))
        ≤ Real.exp (-(n:ℝ)) := by
    intro n hn
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 := hexp2 n
    have h2 := hYle n hn
    have hπ := Real.pi_gt_three
    have hn4 : (4:ℝ) ≤ (n:ℝ) := by
      exact_mod_cast le_trans (by omega : 4 ≤ N) hn
    -- (9/2+Y)n − πe^{2n} ≤ −n  ⟸  π(1+n)² ≥ (11/2+Y)n
    nlinarith [mul_le_mul_of_nonneg_right hπ.le (sq_nonneg (1 + (n:ℝ))),
      Nat.cast_nonneg (α := ℝ) n]
  have hbound : ∀ n : ℕ, N ≤ n →
      ‖xiStage n z - xiIntegral z‖
        ≤ (16 * Real.pi^2 * Real.exp Real.pi) * Real.exp (-(n:ℝ)) := by
    intro n hn
    have hc : 9/2 + Y < 2 * Real.pi * Real.exp (2*(n:ℝ)) := by
      linarith [hcev n hn]
    have hdiff := xiIntegral_sub_stage_bound
      (Nat.cast_nonneg n) hY0 hc (le_refl Y)
    have hc1 : (1:ℝ) ≤ 2 * Real.pi * Real.exp (2*(n:ℝ)) - 9/2 - Y := by
      linarith [hcev n hn]
    have hA0 : (0:ℝ) ≤ 8 * Real.pi^2 * Real.exp Real.pi
        * Real.exp ((9/2 + Y) * (n:ℝ))
        * Real.exp (-Real.pi * Real.exp (2*(n:ℝ))) := by positivity
    have hdivle : (8 * Real.pi^2 * Real.exp Real.pi
          * Real.exp ((9/2 + Y) * (n:ℝ))
          * Real.exp (-Real.pi * Real.exp (2*(n:ℝ))))
        / (2 * Real.pi * Real.exp (2*(n:ℝ)) - 9/2 - Y)
        ≤ 8 * Real.pi^2 * Real.exp Real.pi
          * Real.exp ((9/2 + Y) * (n:ℝ))
          * Real.exp (-Real.pi * Real.exp (2*(n:ℝ))) :=
      div_le_self hA0 hc1
    have hAle : 8 * Real.pi^2 * Real.exp Real.pi
          * Real.exp ((9/2 + Y) * (n:ℝ))
          * Real.exp (-Real.pi * Real.exp (2*(n:ℝ)))
        ≤ 8 * Real.pi^2 * Real.exp Real.pi * Real.exp (-(n:ℝ)) := by
      have h := hAev n hn
      calc 8 * Real.pi^2 * Real.exp Real.pi
            * Real.exp ((9/2 + Y) * (n:ℝ))
            * Real.exp (-Real.pi * Real.exp (2*(n:ℝ)))
          = (8 * Real.pi^2 * Real.exp Real.pi)
            * (Real.exp ((9/2 + Y) * (n:ℝ))
                * Real.exp (-Real.pi * Real.exp (2*(n:ℝ)))) := by ring
        _ ≤ (8 * Real.pi^2 * Real.exp Real.pi) * Real.exp (-(n:ℝ)) :=
            mul_le_mul_of_nonneg_left h (by positivity)
    rw [norm_sub_rev]
    calc ‖xiIntegral z - xiStage n z‖
        ≤ 2 * ((8 * Real.pi^2 * Real.exp Real.pi
            * Real.exp ((9/2 + Y) * (n:ℝ))
            * Real.exp (-Real.pi * Real.exp (2*(n:ℝ))))
          / (2 * Real.pi * Real.exp (2*(n:ℝ)) - 9/2 - Y)) := hdiff
      _ ≤ 2 * (8 * Real.pi^2 * Real.exp Real.pi * Real.exp (-(n:ℝ))) := by
          linarith [hdivle, hAle]
      _ = (16 * Real.pi^2 * Real.exp Real.pi) * Real.exp (-(n:ℝ)) := by ring
  have hg : Filter.Tendsto
      (fun n : ℕ => (16 * Real.pi^2 * Real.exp Real.pi) * Real.exp (-(n:ℝ)))
      Filter.atTop (nhds 0) := by
    have hfun' : ∀ n : ℕ, Real.exp (-1:ℝ)^n = Real.exp (-(n:ℝ)) := by
      intro n
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hr0 : (0:ℝ) ≤ Real.exp (-1:ℝ) := (Real.exp_pos _).le
    have hr1 : Real.exp (-1:ℝ) < 1 := by
      rw [show (1:ℝ) = Real.exp 0 by rw [Real.exp_zero]]
      exact Real.exp_lt_exp.mpr (by norm_num)
    have h0 := tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
    have h1 := h0.const_mul (16 * Real.pi^2 * Real.exp Real.pi)
    rw [mul_zero] at h1
    exact h1.congr fun n => by rw [hfun' n]
  apply squeeze_zero_norm' _ hg
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact hbound n hn

/-- **The zero-flow generator — FTC at the extent boundary**: the stage moves
in the extent by exactly the boundary kernel, `∂_U Ξ_U(z) = 2Φ(U)cos(zU)`.
Hence a simple stage zero `z_e(U)` obeys the EXACT escort dynamics
`ż_e = −2Φ(U)cos(z_e U)/Ξ_U′(z_e)` — the object [M1-F]'s invariance
argument runs on. -/
theorem xiStage_extent_hasDerivAt {U : ℝ} (hU : 0 < U) (z : ℂ) :
    HasDerivAt (fun V : ℝ => xiStage V z)
      (2 * ((riemannXiKernel U : ℂ) * Complex.cos (z * U))) U := by
  set f : ℝ → ℂ := fun u => (riemannXiKernel u : ℂ) * Complex.cos (z * u)
    with hf
  have hcontf : ContinuousAt f U := by
    apply ContinuousAt.mul
    · exact Complex.continuous_ofReal.continuousAt.comp
        (riemannXiKernel_continuousOn.continuousAt (Ici_mem_nhds hU))
    · exact (Complex.continuous_cos.comp
        (continuous_const.mul Complex.continuous_ofReal)).continuousAt
  have hmeasf : Measurable f :=
    (Complex.measurable_ofReal.comp riemannXiKernel_measurable).mul
      (Complex.continuous_cos.comp
        (continuous_const.mul Complex.continuous_ofReal)).measurable
  have hii : IntervalIntegrable f MeasureTheory.volume 0 U := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hU.le]
    exact xiIntegrand_integrableOn_Ioc U z
  have hsmf : StronglyMeasurableAtFilter f (nhds U)
      MeasureTheory.volume :=
    hmeasf.stronglyMeasurable.stronglyMeasurableAtFilter
  have hFTC := intervalIntegral.integral_hasDerivAt_right hii hsmf hcontf
  have h2 := hFTC.const_mul (2:ℂ)
  have hev : (fun V : ℝ => xiStage V z)
      =ᶠ[nhds U] fun V : ℝ => 2 * ∫ x in (0:ℝ)..V, f x := by
    filter_upwards [eventually_gt_nhds hU] with V hV
    unfold xiStage
    rw [intervalIntegral.integral_of_le hV.le]
  exact h2.congr_of_eventuallyEq hev

end CriticalLinePhasor.ThetaWronskianSuzukiGram

#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiStage_extent_hasDerivAt
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiStage_tendsto_xiIntegral
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiIntegrand_integrableOn
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.xiIntegral_sub_stage_bound
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.pow_four_mul_exp_le
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.kernel_abs_bound
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.kernel_tail_integral_bound
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.mode_tail_exp_domination
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.mode_tail_integral_bound
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.mode_integrand_bound
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.cos_strip_bound
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.kernel_bound_aux
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.kernel_term_abs_bound
