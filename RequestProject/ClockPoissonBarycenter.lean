import RequestProject.BankHerglotzReduction

/-!
# The Euler clocks are the Poisson barycenters of the unitary clocks

The 3D geometric, harmonic, spectral statement behind the door-class law (ledger 517):
the unitary clocks `symClock α ℓ` (`‖α‖ = 1`, real spectrum, per-clock DC `ℓ/2`) and the
Euler clock (`‖α‖ = p^{−½}`, zeros on `Re s = 0`, no DC) are one object read at different
points of the face disk.

Fix a winding `ℓ > 0` and a spectral point `z` off the real axis.  As a function of the FACE
`a`, the clock's log-derivative is the rational function
`F(a) = (iℓ/2)·(1 + a·E)/(1 − a·E)`, `E = e^{−izℓ}` (`symClock_logDeriv_face_form`),
holomorphic on the closed unit disk of faces exactly when `‖E‖ < 1`, i.e. right of the line.
Mathlib's Poisson integral formula (`DiffContOnCl.circleAverage_poissonKernel_smul`) then
says: the Poisson average of the UNITARY clocks over the face circle, with kernel centred at
an interior face `w`, IS the clock with face `w`
(`unitaryClocks_poisson_barycenter_right`).  Left of the line the holomorphic variable is
the conjugate face, and the barycenter at `w` is the clock with face `(w̄)⁻¹`
(`unitaryClocks_poisson_barycenter_left`).

Read at the Euler face `w = p^{−½}` (`unitaryClocks_poisson_barycenter_eulerFace`,
`..._antiEulerFace`): right of the line the barycenter of the self-adjoint clocks is the
Euler factor's clock (zeros on `Re s = 0`, `clock_zero_depth`); left of the line it is the
reflected Euler clock (face `p^{½}`, zeros on `Re s = 1`).  The two ENDS of the
double-ended helix are the two Poisson barycenters of the unitary clock family, and the
mixing radius is the carrier radius `√p`.  The Euler product is a mixed state of the
self-adjoint clocks; its off-line spectrum is the barycenter's, and the unitary clocks'
divergent DC (`BankDoorClassLaw`) is the price of purity.  Measured 1e−12 on 2026-09-01
(ledger 517); compiled here.

No `sorry`, no `axiom`.
-/

open Complex Filter Topology Metric

noncomputable section

namespace CriticalLinePhasor.BankLimit

open CriticalLinePhasor.ChiralityHB

/-! ## The face function -/

/-- The clock's log-derivative as a rational function of the face, valid wherever the
denominator is nonzero (any face, either side of the line). -/
theorem symClock_logDeriv_face_form (α : ℂ) (ℓ : ℝ) (z : ℂ)
    (hne : 1 - α * Complex.exp (-(Complex.I * z * ℓ)) ≠ 0) :
    logDeriv (symClock α ℓ) z
      = (Complex.I * ℓ / 2) * ((1 + α * Complex.exp (-(Complex.I * z * ℓ)))
          / (1 - α * Complex.exp (-(Complex.I * z * ℓ)))) := by
  rw [symClock_logDeriv_eq]
  have hA : Complex.exp (Complex.I * z * ℓ / 2) ≠ 0 := Complex.exp_ne_zero _
  have hprod : Complex.exp (-(Complex.I * z * ℓ / 2))
      = Complex.exp (Complex.I * z * ℓ / 2) * Complex.exp (-(Complex.I * z * ℓ)) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hprod]
  have hden : Complex.exp (Complex.I * z * ℓ / 2)
      - α * (Complex.exp (Complex.I * z * ℓ / 2) * Complex.exp (-(Complex.I * z * ℓ))) ≠ 0 := by
    rw [show Complex.exp (Complex.I * z * ℓ / 2)
        - α * (Complex.exp (Complex.I * z * ℓ / 2) * Complex.exp (-(Complex.I * z * ℓ)))
        = Complex.exp (Complex.I * z * ℓ / 2)
          * (1 - α * Complex.exp (-(Complex.I * z * ℓ))) by ring]
    exact mul_ne_zero hA hne
  congr 1
  rw [div_eq_div_iff hden hne]
  ring

/-- Right of the line the face disk point `E = e^{−izℓ}` is inside the unit disk. -/
theorem rightDiskPoint_norm_lt_one {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ} (hz : z.im < 0) :
    ‖Complex.exp (-(Complex.I * z * ℓ))‖ < 1 := by
  rw [Complex.norm_exp]
  have hre : (-(Complex.I * z * (ℓ : ℂ))).re = z.im * ℓ := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  exact Real.exp_lt_one_iff.mpr (by nlinarith)

/-- Left of the line the conjugate disk point `q = e^{iℓz}` is inside the unit disk. -/
theorem leftDiskPoint_norm_lt_one {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ} (hz : 0 < z.im) :
    ‖Complex.exp (Complex.I * ℓ * z)‖ < 1 := by
  rw [Complex.norm_exp]
  have hre : (Complex.I * (ℓ : ℂ) * z).re = -(ℓ * z.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  exact Real.exp_lt_one_iff.mpr (by nlinarith)

/-- The face denominator never vanishes on the closed unit disk when `‖q‖ < 1`. -/
theorem face_denom_ne_zero {q : ℂ} (hq : ‖q‖ < 1) {a : ℂ} (ha : ‖a‖ ≤ 1) : 1 - a * q ≠ 0 := by
  intro h
  have h1 : a * q = 1 := by linear_combination -h
  have hlt : ‖a * q‖ < 1 := by
    rw [norm_mul]
    calc ‖a‖ * ‖q‖ ≤ 1 * ‖q‖ := by gcongr
      _ < 1 := by simpa using hq
  rw [h1, norm_one] at hlt
  exact lt_irrefl _ hlt

/-- The face function `a ↦ c·(1 + aq)/(1 − aq)` is holomorphic on the closed unit disk. -/
theorem faceFunction_differentiableOn (c : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    DifferentiableOn ℂ (fun a : ℂ => c * ((1 + a * q) / (1 - a * q))) (closedBall 0 1) := by
  refine DifferentiableOn.const_mul ?_ c
  apply DifferentiableOn.div
  · exact (differentiableOn_const _).add (differentiableOn_id.mul (differentiableOn_const _))
  · exact (differentiableOn_const _).sub (differentiableOn_id.mul (differentiableOn_const _))
  · intro a ha
    exact face_denom_ne_zero hq (mem_closedBall_zero_iff.mp ha)

theorem faceFunction_diffContOnCl (c : ℂ) {q : ℂ} (hq : ‖q‖ < 1) :
    DiffContOnCl ℂ (fun a : ℂ => c * ((1 + a * q) / (1 - a * q))) (ball 0 1) := by
  apply DifferentiableOn.diffContOnCl
  rw [closure_ball (0 : ℂ) one_ne_zero]
  exact faceFunction_differentiableOn c hq

/-! ## Right of the line: the barycenter is the clock with the barycentric face -/

/-- **Poisson barycenter, right of the line.**  For `Im z < 0` and any interior face
`‖w‖ < 1`, the Poisson average over the unitary faces of the clock log-derivatives equals the
log-derivative of the clock with face `w`.  The unitary clocks are the boundary values of one
holomorphic face function. -/
theorem unitaryClocks_poisson_barycenter_right {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ} (hz : z.im < 0)
    {w : ℂ} (hw : ‖w‖ < 1) :
    Real.circleAverage (fun a : ℂ => poissonKernel 0 w a • logDeriv (symClock a ℓ) z) 0 1
      = logDeriv (symClock w ℓ) z := by
  have hqn : ‖Complex.exp (-(Complex.I * z * ℓ))‖ < 1 := rightDiskPoint_norm_lt_one hℓ hz
  have hFdiff := faceFunction_diffContOnCl (Complex.I * ℓ / 2) hqn
  have hwb : w ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hw
  have hpoisson := hFdiff.circleAverage_poissonKernel_smul hwb
  have hsph : Set.EqOn (fun a : ℂ => poissonKernel 0 w a • logDeriv (symClock a ℓ) z)
      (poissonKernel 0 w • fun a : ℂ => (Complex.I * ℓ / 2)
        * ((1 + a * Complex.exp (-(Complex.I * z * ℓ)))
          / (1 - a * Complex.exp (-(Complex.I * z * ℓ)))))
      (sphere (0 : ℂ) |(1 : ℝ)|) := by
    intro a ha
    rw [abs_one, mem_sphere_zero_iff_norm] at ha
    have hne : 1 - a * Complex.exp (-(Complex.I * z * ℓ)) ≠ 0 :=
      face_denom_ne_zero hqn ha.le
    show poissonKernel 0 w a • logDeriv (symClock a ℓ) z
      = poissonKernel 0 w a • ((Complex.I * ℓ / 2)
        * ((1 + a * Complex.exp (-(Complex.I * z * ℓ)))
          / (1 - a * Complex.exp (-(Complex.I * z * ℓ)))))
    rw [symClock_logDeriv_face_form a ℓ z hne]
  rw [Real.circleAverage_congr_sphere hsph, hpoisson]
  have hne : 1 - w * Complex.exp (-(Complex.I * z * ℓ)) ≠ 0 := face_denom_ne_zero hqn hw.le
  exact (symClock_logDeriv_face_form w ℓ z hne).symm

/-- **The Euler face, right of the line.**  At a real barycentric face `0 ≤ r < 1` the
barycenter of the unitary clocks is the clock with face `r`: at `r = p^{−½}`, `ℓ = log p`,
this is the Euler factor's clock, with zeros at `Re s = 0` (`clock_zero_depth`) — the helix
end. -/
theorem unitaryClocks_poisson_barycenter_eulerFace {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ} (hz : z.im < 0)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Real.circleAverage (fun a : ℂ => poissonKernel 0 (r : ℂ) a • logDeriv (symClock a ℓ) z) 0 1
      = logDeriv (symClock (r : ℂ) ℓ) z := by
  apply unitaryClocks_poisson_barycenter_right hℓ hz
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  exact hr1

/-! ## Left of the line: the barycenter is the clock with the reflected face -/

/-- On the unit circle the Poisson kernel is conjugation-covariant: `P_w(a) = P_{w̄}(a⁻¹)`. -/
theorem poissonKernel_zero_inv_conj {w a : ℂ} (ha : ‖a‖ = 1) :
    poissonKernel 0 w a = poissonKernel 0 ((starRingEnd ℂ) w) a⁻¹ := by
  rw [poissonKernel_def, poissonKernel_def, inv_eq_conj ha]
  simp only [sub_zero]
  rw [← map_sub, RCLike.norm_conj, RCLike.norm_conj, RCLike.norm_conj]

/-- **Poisson barycenter, left of the line.**  For `Im z > 0` and `0 < ‖w‖ < 1`, the Poisson
average over the unitary faces, kernel centred at `w`, equals the log-derivative of the clock
with the REFLECTED face `(w̄)⁻¹` (modulus `> 1`). -/
theorem unitaryClocks_poisson_barycenter_left {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ} (hz : 0 < z.im)
    {w : ℂ} (hw0 : w ≠ 0) (hw : ‖w‖ < 1) :
    Real.circleAverage (fun a : ℂ => poissonKernel 0 w a • logDeriv (symClock a ℓ) z) 0 1
      = logDeriv (symClock ((starRingEnd ℂ) w)⁻¹ ℓ) z := by
  have hqn : ‖Complex.exp (Complex.I * ℓ * z)‖ < 1 := leftDiskPoint_norm_lt_one hℓ hz
  have hzne : z.im ≠ 0 := ne_of_gt hz
  set G : ℂ → ℂ := fun b => (-(((ℓ / 2 : ℝ) : ℂ) * Complex.I))
    * ((1 + b * Complex.exp (Complex.I * ℓ * z)) / (1 - b * Complex.exp (Complex.I * ℓ * z)))
    with hG
  have hGdiff : DiffContOnCl ℂ G (ball 0 1) := faceFunction_diffContOnCl _ hqn
  have hwc : (starRingEnd ℂ) w ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, RCLike.norm_conj]
    exact hw
  have hpoisson := hGdiff.circleAverage_poissonKernel_smul hwc
  have hsph : Set.EqOn (fun a : ℂ => poissonKernel 0 w a • logDeriv (symClock a ℓ) z)
      (fun a : ℂ => (poissonKernel 0 ((starRingEnd ℂ) w) • G) a⁻¹)
      (sphere (0 : ℂ) |(1 : ℝ)|) := by
    intro a ha
    rw [abs_one, mem_sphere_zero_iff_norm] at ha
    show poissonKernel 0 w a • logDeriv (symClock a ℓ) z
      = poissonKernel 0 ((starRingEnd ℂ) w) a⁻¹ • G a⁻¹
    rw [poissonKernel_zero_inv_conj ha, symClock_logDeriv_closed ha hℓ hzne, inv_eq_conj ha]
    simp only [hG]
    congr 1
    ring
  rw [Real.circleAverage_congr_sphere hsph, Real.circleAverage_zero_one_congr_inv, hpoisson]
  -- identify `G(w̄)` as the clock with face `(w̄)⁻¹`
  have hcne : (starRingEnd ℂ) w ≠ 0 := (map_ne_zero _).mpr hw0
  have hE : Complex.exp (-(Complex.I * z * ℓ)) * Complex.exp (Complex.I * ℓ * z) = 1 := by
    rw [← Complex.exp_add, show -(Complex.I * z * ℓ) + Complex.I * ℓ * z = 0 by ring]
    exact Complex.exp_zero
  have hEbig : 1 < ‖Complex.exp (-(Complex.I * z * ℓ))‖ := by
    have hprod : ‖Complex.exp (-(Complex.I * z * ℓ))‖ * ‖Complex.exp (Complex.I * ℓ * z)‖ = 1 := by
      rw [← norm_mul, hE, norm_one]
    nlinarith [norm_nonneg (Complex.exp (-(Complex.I * z * ℓ))),
      norm_nonneg (Complex.exp (Complex.I * ℓ * z))]
  have hne : 1 - ((starRingEnd ℂ) w)⁻¹ * Complex.exp (-(Complex.I * z * ℓ)) ≠ 0 := by
    intro h
    have h1 : ((starRingEnd ℂ) w)⁻¹ * Complex.exp (-(Complex.I * z * ℓ)) = 1 := by
      linear_combination -h
    have h2 : Complex.exp (-(Complex.I * z * ℓ)) = (starRingEnd ℂ) w := by
      calc Complex.exp (-(Complex.I * z * ℓ))
          = (starRingEnd ℂ) w * (((starRingEnd ℂ) w)⁻¹ * Complex.exp (-(Complex.I * z * ℓ))) := by
            rw [← mul_assoc, mul_inv_cancel₀ hcne, one_mul]
        _ = (starRingEnd ℂ) w := by rw [h1, mul_one]
    have h3 : ‖Complex.exp (-(Complex.I * z * ℓ))‖ < 1 := by
      rw [h2, RCLike.norm_conj]
      exact hw
    linarith
  rw [symClock_logDeriv_face_form _ ℓ z hne, hG]
  have hden1 : 1 - (starRingEnd ℂ) w * Complex.exp (Complex.I * ℓ * z) ≠ 0 :=
    face_denom_ne_zero hqn (by rw [RCLike.norm_conj]; exact hw.le)
  have hinv : ((starRingEnd ℂ) w)⁻¹ * (starRingEnd ℂ) w = 1 := inv_mul_cancel₀ hcne
  have key : (1 + ((starRingEnd ℂ) w)⁻¹ * Complex.exp (-(Complex.I * z * ℓ)))
        / (1 - ((starRingEnd ℂ) w)⁻¹ * Complex.exp (-(Complex.I * z * ℓ)))
      = (-(1 + (starRingEnd ℂ) w * Complex.exp (Complex.I * ℓ * z)))
        / (1 - (starRingEnd ℂ) w * Complex.exp (Complex.I * ℓ * z)) := by
    rw [div_eq_div_iff hne hden1]
    linear_combination (-2 * (((starRingEnd ℂ) w)⁻¹ * (starRingEnd ℂ) w)) * hE
      + (-2 : ℂ) * hinv
  rw [key, neg_div]
  push_cast
  ring

/-- **The anti-Euler face, left of the line.**  At a real barycentric face `0 < r < 1` the
barycenter of the unitary clocks is the clock with the reflected face `r⁻¹`: at `r = p^{−½}`,
`ℓ = log p`, this is the clock with face `p^{½}`, zeros at `Re s = 1` — the anti-helix end. -/
theorem unitaryClocks_poisson_barycenter_antiEulerFace {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : 0 < z.im) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Real.circleAverage (fun a : ℂ => poissonKernel 0 (r : ℂ) a • logDeriv (symClock a ℓ) z) 0 1
      = logDeriv (symClock ((r : ℂ)⁻¹) ℓ) z := by
  have h := unitaryClocks_poisson_barycenter_left hℓ hz (w := (r : ℂ))
    (by exact_mod_cast hr0.ne') (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]; exact hr1)
  rw [Complex.conj_ofReal] at h
  exact h

end CriticalLinePhasor.BankLimit

#print axioms CriticalLinePhasor.BankLimit.symClock_logDeriv_face_form
#print axioms CriticalLinePhasor.BankLimit.unitaryClocks_poisson_barycenter_right
#print axioms CriticalLinePhasor.BankLimit.unitaryClocks_poisson_barycenter_eulerFace
#print axioms CriticalLinePhasor.BankLimit.unitaryClocks_poisson_barycenter_left
#print axioms CriticalLinePhasor.BankLimit.unitaryClocks_poisson_barycenter_antiEulerFace
