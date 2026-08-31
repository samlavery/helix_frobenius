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

end CriticalLinePhasor.ThetaWronskianSuzukiGram

#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.mode_integrand_bound
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.cos_strip_bound
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.kernel_bound_aux
#print axioms CriticalLinePhasor.ThetaWronskianSuzukiGram.kernel_term_abs_bound
