import RequestProject.GenuineMaassCuspForm3D

/-!
# The radial equation at zero spectral parameter

First step of a Lean witness that `FirstOrderFreeRadialData` is uninhabited — the modified Bessel
equation with its first-order term `y·K'` dropped, which is the form
`GenuineMaassCuspForm3D.radial_equation` carried before it was repaired.

At `spectralParameter = 0` that equation collapses to a constant-coefficient equation on the
positive ray:

  **`K'' = 4π²·K`**

whose decaying solutions are exactly `C·e^{-2πy}` — with **no power-law prefactor**.  That is what
conflicts with `radial_normalization` (`2√y·e^{2πy}·K(y) → 1`), which demands the prefactor
`y^{-1/2}`.

Numerically confirmed (`tmp/radchk.py`): integrating the decaying solution of `radial_equation`
inward, `2√y·e^{2πy}·K(y)` tracks `2√y` and diverges — at `r = 0` matching `2√30 = 10.954` to six
figures — instead of tending to `1`.

The defect is the **missing first-order term**: the Whittaker equation satisfied by `K_{ir}(2πy)`,
which `radial_normalization` and `laplace_eigen` both describe, is
`y²K'' + y·K' = ((2πy)² − r²)·K`.  That is now what `GenuineMaassCuspForm3D.radial_equation`
states; `sqrt_weight_sign_flip` certifies that the restored term carries the deciding constant from
`+r² ≥ 0` — the range this file's contradiction covers — to `−(1/4 + r²) < 0`, outside it.

**Scope.**  This file records the reduction only.  The full emptiness argument (the conserved
energy `E = K'² − 4π²K²`, constant at `r = 0`, forced to `0` by decay, hence `K = Ce^{∓2πy}`) is
not formalised here.
-/

open Complex
open scoped Real

namespace CriticalLinePhasor.ThreeDConverse

/-- **At zero spectral parameter the radial equation is constant-coefficient.** -/
theorem radial_equation_at_zero (M : FirstOrderFreeRadialData)
    (hr : M.spectralParameter = 0) {y : ℝ} (hy : 0 < y) :
    iteratedDeriv 2 M.radialKernel y = ((4 * Real.pi ^ 2 : ℝ) : ℂ) * M.radialKernel y := by
  have h := M.radial_equation y hy
  rw [hr] at h
  have hy2 : ((y : ℂ)) ^ 2 ≠ 0 := by
    have : (y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hy.ne'
    exact pow_ne_zero _ this
  have hrw : (((2 * Real.pi * y) ^ 2 + (0 : ℝ) ^ 2 : ℝ) : ℂ) =
      ((y : ℂ)) ^ 2 * ((4 * Real.pi ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hrw, mul_assoc] at h
  exact mul_left_cancel₀ hy2 h

/-- The kernel is twice differentiable on the positive ray. -/
lemma radial_contDiffAt (M : FirstOrderFreeRadialData) {y : ℝ} (hy : 0 < y) :
    ContDiffAt ℝ 2 M.radialKernel y :=
  ((M.radial_smooth 2).contDiffWithinAt (Set.mem_Ioi.mpr hy)).contDiffAt
    (Ioi_mem_nhds hy)

/-- **The second-order equation factors into a first-order one.**  With `F := K' + 2π·K`, the
constant-coefficient equation `K'' = 4π²K` says exactly `F' = 2π·F` — so `F·e^{-2πy}` is constant,
and the solution space is spanned by `e^{±2πy}` with **no power-law prefactor** available. -/
theorem radial_factor_at_zero (M : FirstOrderFreeRadialData)
    (hr : M.spectralParameter = 0) {y : ℝ} (hy : 0 < y) :
    deriv (fun t : ℝ => deriv M.radialKernel t +
        ((2 * Real.pi : ℝ) : ℂ) * M.radialKernel t) y =
      ((2 * Real.pi : ℝ) : ℂ) *
        (deriv M.radialKernel y + ((2 * Real.pi : ℝ) : ℂ) * M.radialKernel y) := by
  have hC := radial_contDiffAt M hy
  have hK : DifferentiableAt ℝ M.radialKernel y :=
    hC.differentiableAt (by norm_num)
  have hd : ContDiffOn ℝ 1 (deriv M.radialKernel) (Set.Ioi (0:ℝ)) :=
    (M.radial_smooth 2).deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hK' : DifferentiableAt ℝ (deriv M.radialKernel) y :=
    (hd.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds hy)
  have hsum := (hK'.hasDerivAt.add
    (hK.hasDerivAt.const_mul (((2 * Real.pi : ℝ) : ℂ)))).deriv
  show deriv (deriv M.radialKernel +
      fun t : ℝ => ((2 * Real.pi : ℝ) : ℂ) * M.radialKernel t) y = _
  rw [hsum]
  have h2 : deriv (deriv M.radialKernel) y = iteratedDeriv 2 M.radialKernel y := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [h2, radial_equation_at_zero M hr hy]
  push_cast
  ring

/-- **The growing mode is a genuine exponential.**  `(K' + 2π·K)·e^{-2πy}` has zero derivative on
the ray, so `K' + 2π·K = A·e^{2πy}` for a constant `A`.  This is step (i) of the emptiness
argument. -/
theorem radial_growing_mode_const (M : FirstOrderFreeRadialData)
    (hr : M.spectralParameter = 0) :
    ∃ A : ℂ, ∀ y : ℝ, 0 < y →
      (deriv M.radialKernel y + ((2 * Real.pi : ℝ) : ℂ) * M.radialKernel y) *
        Complex.exp (-((2 * Real.pi : ℝ) : ℂ) * (y : ℂ)) = A := by
  set c : ℂ := ((2 * Real.pi : ℝ) : ℂ) with hc
  set F : ℝ → ℂ := fun t => deriv M.radialKernel t + c * M.radialKernel t with hF
  set g : ℝ → ℂ := fun t => Complex.exp (-c * (t : ℂ)) with hg
  have hdiffK : ∀ {y : ℝ}, 0 < y → DifferentiableAt ℝ M.radialKernel y := by
    intro y hy
    exact (radial_contDiffAt M hy).differentiableAt (by norm_num)
  have hdiffK' : ∀ {y : ℝ}, 0 < y → DifferentiableAt ℝ (deriv M.radialKernel) y := by
    intro y hy
    have hd : ContDiffOn ℝ 1 (deriv M.radialKernel) (Set.Ioi (0:ℝ)) :=
      (M.radial_smooth 2).deriv_of_isOpen isOpen_Ioi (by norm_num)
    exact (hd.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds hy)
  have hFd : ∀ {y : ℝ}, 0 < y → HasDerivAt F (c * F y) y := by
    intro y hy
    have h := (hdiffK' hy).hasDerivAt.add ((hdiffK hy).hasDerivAt.const_mul c)
    have hval : deriv (deriv M.radialKernel) y + c * deriv M.radialKernel y = c * F y := by
      have h2 : deriv (deriv M.radialKernel) y = iteratedDeriv 2 M.radialKernel y := by
        rw [iteratedDeriv_succ, iteratedDeriv_one]
      rw [h2, radial_equation_at_zero M hr hy, hF, hc]
      push_cast
      ring
    rw [hval] at h
    exact h
  have hgd : ∀ y : ℝ, HasDerivAt g (-c * g y) y := by
    intro y
    have hid : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) 1 y :=
      Complex.ofRealCLM.hasDerivAt
    have := ((hid.const_mul (-c)).cexp)
    simpa [hg, mul_comm] using this
  -- the product has zero derivative
  have hzero : Set.EqOn (deriv fun t : ℝ => F t * g t) 0 (Set.Ioi (0:ℝ)) := by
    intro y hy
    have hy0 : (0:ℝ) < y := hy
    show deriv (F * g) y = 0
    rw [((hFd hy0).mul (hgd y)).deriv]
    ring
  have hdiff : DifferentiableOn ℝ (fun t : ℝ => F t * g t) (Set.Ioi (0:ℝ)) := by
    intro y hy
    have hy0 : (0:ℝ) < y := hy
    exact (((hFd hy0).mul (hgd y)).differentiableAt).differentiableWithinAt
  obtain ⟨A, hA⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero
    (isPreconnected_Ioi) hdiff hzero
  exact ⟨A, fun y hy => hA y hy⟩

/-- **The decaying mode is a genuine exponential too.**  `(K' − 2π·K)·e^{2πy}` has zero derivative,
so `K' − 2π·K = B·e^{-2πy}`.  Step (ii); with step (i) this pins `K` to the span of `e^{±2πy}`. -/
theorem radial_decaying_mode_const (M : FirstOrderFreeRadialData)
    (hr : M.spectralParameter = 0) :
    ∃ B : ℂ, ∀ y : ℝ, 0 < y →
      (deriv M.radialKernel y - ((2 * Real.pi : ℝ) : ℂ) * M.radialKernel y) *
        Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (y : ℂ)) = B := by
  set c : ℂ := ((2 * Real.pi : ℝ) : ℂ) with hc
  set F : ℝ → ℂ := fun t => deriv M.radialKernel t - c * M.radialKernel t with hF
  set g : ℝ → ℂ := fun t => Complex.exp (c * (t : ℂ)) with hg
  have hdiffK : ∀ {y : ℝ}, 0 < y → DifferentiableAt ℝ M.radialKernel y := by
    intro y hy
    exact (radial_contDiffAt M hy).differentiableAt (by norm_num)
  have hdiffK' : ∀ {y : ℝ}, 0 < y → DifferentiableAt ℝ (deriv M.radialKernel) y := by
    intro y hy
    have hd : ContDiffOn ℝ 1 (deriv M.radialKernel) (Set.Ioi (0:ℝ)) :=
      (M.radial_smooth 2).deriv_of_isOpen isOpen_Ioi (by norm_num)
    exact (hd.differentiableOn (by norm_num)).differentiableAt (Ioi_mem_nhds hy)
  have hFd : ∀ {y : ℝ}, 0 < y → HasDerivAt F (-c * F y) y := by
    intro y hy
    have h := (hdiffK' hy).hasDerivAt.sub ((hdiffK hy).hasDerivAt.const_mul c)
    have hval : deriv (deriv M.radialKernel) y - c * deriv M.radialKernel y = -c * F y := by
      have h2 : deriv (deriv M.radialKernel) y = iteratedDeriv 2 M.radialKernel y := by
        rw [iteratedDeriv_succ, iteratedDeriv_one]
      rw [h2, radial_equation_at_zero M hr hy, hF, hc]
      push_cast
      ring
    rw [hval] at h
    exact h
  have hgd : ∀ y : ℝ, HasDerivAt g (c * g y) y := by
    intro y
    have hid : HasDerivAt (fun t : ℝ => ((t : ℝ) : ℂ)) 1 y :=
      Complex.ofRealCLM.hasDerivAt
    have := ((hid.const_mul c).cexp)
    simpa [hg, mul_comm] using this
  -- the product has zero derivative
  have hzero : Set.EqOn (deriv fun t : ℝ => F t * g t) 0 (Set.Ioi (0:ℝ)) := by
    intro y hy
    have hy0 : (0:ℝ) < y := hy
    show deriv (F * g) y = 0
    rw [((hFd hy0).mul (hgd y)).deriv]
    ring
  have hdiff : DifferentiableOn ℝ (fun t : ℝ => F t * g t) (Set.Ioi (0:ℝ)) := by
    intro y hy
    have hy0 : (0:ℝ) < y := hy
    exact (((hFd hy0).mul (hgd y)).differentiableAt).differentiableWithinAt
  obtain ⟨B, hB⟩ := isOpen_Ioi.exists_is_const_of_deriv_eq_zero
    (isPreconnected_Ioi) hdiff hzero
  exact ⟨B, fun y hy => hB y hy⟩


/-- **The kernel is an exponential combination.**  Subtracting the two mode identities pins `K` to
`span{e^{2πy}, e^{-2πy}}` — no power-law prefactor exists in the solution space at all. -/
theorem radial_eq_exp_combination (M : FirstOrderFreeRadialData)
    (hr : M.spectralParameter = 0) :
    ∃ A B : ℂ, ∀ y : ℝ, 0 < y →
      ((4 * Real.pi : ℝ) : ℂ) * M.radialKernel y =
        A * Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (y : ℂ)) -
          B * Complex.exp (-((2 * Real.pi : ℝ) : ℂ) * (y : ℂ)) := by
  obtain ⟨A, hA⟩ := radial_growing_mode_const M hr
  obtain ⟨B, hB⟩ := radial_decaying_mode_const M hr
  refine ⟨A, B, fun y hy => ?_⟩
  set c : ℂ := ((2 * Real.pi : ℝ) : ℂ) with hc
  have hexp : Complex.exp (-c * (y : ℂ)) * Complex.exp (c * (y : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    simp
  have h1 : deriv M.radialKernel y + c * M.radialKernel y =
      A * Complex.exp (c * (y : ℂ)) := by
    have := hA y hy
    calc deriv M.radialKernel y + c * M.radialKernel y
        = (deriv M.radialKernel y + c * M.radialKernel y) *
            (Complex.exp (-c * (y : ℂ)) * Complex.exp (c * (y : ℂ))) := by
          rw [hexp, mul_one]
      _ = ((deriv M.radialKernel y + c * M.radialKernel y) *
            Complex.exp (-c * (y : ℂ))) * Complex.exp (c * (y : ℂ)) := by ring
      _ = A * Complex.exp (c * (y : ℂ)) := by rw [this]
  have h2 : deriv M.radialKernel y - c * M.radialKernel y =
      B * Complex.exp (-c * (y : ℂ)) := by
    have := hB y hy
    calc deriv M.radialKernel y - c * M.radialKernel y
        = (deriv M.radialKernel y - c * M.radialKernel y) *
            (Complex.exp (c * (y : ℂ)) * Complex.exp (-c * (y : ℂ))) := by
          rw [mul_comm (Complex.exp (c * (y : ℂ))), hexp, mul_one]
      _ = ((deriv M.radialKernel y - c * M.radialKernel y) *
            Complex.exp (c * (y : ℂ))) * Complex.exp (-c * (y : ℂ)) := by ring
      _ = B * Complex.exp (-c * (y : ℂ)) := by rw [this]
  have hsub : (2 * c) * M.radialKernel y =
      A * Complex.exp (c * (y : ℂ)) - B * Complex.exp (-c * (y : ℂ)) := by
    linear_combination h1 - h2
  have hcc : ((4 * Real.pi : ℝ) : ℂ) = 2 * c := by rw [hc]; push_cast; ring
  rw [hcc]
  exact hsub



/-- **The normalization quantity, computed.**  Substituting the exponential form into
`2√y·e^{2πy}·K(y)` — the quantity `radial_normalization` requires to tend to `1` — gives
`(A·√y·e^{4πy} − B·√y)/(2π)`.  Both terms carry a factor `√y` with nothing to damp it: the first
diverges unless `A = 0`, and the second is `−B√y/(2π)`, which is `0` if `B = 0` and diverges
otherwise.  **No `A, B` make it tend to `1`.** -/
theorem radial_normalization_quantity (M : FirstOrderFreeRadialData)
    (hr : M.spectralParameter = 0) :
    ∃ A B : ℂ, ∀ y : ℝ, 0 < y →
      ((2 * Real.sqrt y * Real.exp (2 * Real.pi * y) : ℝ) : ℂ) * M.radialKernel y =
        (A * ((Real.sqrt y : ℝ) : ℂ) *
            Complex.exp (((4 * Real.pi : ℝ) : ℂ) * (y : ℂ)) -
          B * ((Real.sqrt y : ℝ) : ℂ)) / ((2 * Real.pi : ℝ) : ℂ) := by
  obtain ⟨A, B, hAB⟩ := radial_eq_exp_combination M hr
  refine ⟨A, B, fun y hy => ?_⟩
  set c : ℂ := ((2 * Real.pi : ℝ) : ℂ) with hc
  set E : ℂ := Complex.exp (c * (y : ℂ)) with hE
  set E' : ℂ := Complex.exp (-c * (y : ℂ)) with hE'
  have hpi2 : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by simpa using Real.pi_ne_zero
  have hpi4 : ((4 * Real.pi : ℝ) : ℂ) ≠ 0 := by simpa using Real.pi_ne_zero
  have hE2 : E * E = Complex.exp (((4 * Real.pi : ℝ) : ℂ) * (y : ℂ)) := by
    rw [hE, ← Complex.exp_add, hc]
    congr 1
    push_cast
    ring
  have hEE' : E * E' = 1 := by
    rw [hE, hE', ← Complex.exp_add]
    simp
  have hcoe : ((2 * Real.sqrt y * Real.exp (2 * Real.pi * y) : ℝ) : ℂ) =
      2 * ((Real.sqrt y : ℝ) : ℂ) * E := by
    have h1 : ((Real.exp (2 * Real.pi * y) : ℝ) : ℂ) = E := by
      rw [hE, hc, Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [show ((2 * Real.sqrt y * Real.exp (2 * Real.pi * y) : ℝ) : ℂ)
        = 2 * ((Real.sqrt y : ℝ) : ℂ) * ((Real.exp (2 * Real.pi * y) : ℝ) : ℂ) by
      push_cast; ring, h1]
  have hKy : M.radialKernel y = (A * E - B * E') / ((4 * Real.pi : ℝ) : ℂ) := by
    rw [eq_div_iff hpi4]
    linear_combination (hAB y hy)
  calc ((2 * Real.sqrt y * Real.exp (2 * Real.pi * y) : ℝ) : ℂ) * M.radialKernel y
      = (2 * ((Real.sqrt y : ℝ) : ℂ) * E) *
          ((A * E - B * E') / ((4 * Real.pi : ℝ) : ℂ)) := by rw [hcoe, hKy]
    _ = (A * ((Real.sqrt y : ℝ) : ℂ) * (E * E) -
          B * ((Real.sqrt y : ℝ) : ℂ) * (E * E')) / ((2 * Real.pi : ℝ) : ℂ) := by
        field_simp
        push_cast
        ring
    _ = (A * ((Real.sqrt y : ℝ) : ℂ) *
            Complex.exp (((4 * Real.pi : ℝ) : ℂ) * (y : ℂ)) -
          B * ((Real.sqrt y : ℝ) : ℂ)) / ((2 * Real.pi : ℝ) : ℂ) := by
        rw [hE2, hEE', mul_one]


/-- **The structure is empty at zero spectral parameter.**  The normalization quantity is
`√y·(A·e^{4πy} − B)/(2π)`; dividing by `√y → ∞` forces `A·e^{4πy} − B → 0`, which forces `A = 0`
(else it is unbounded) and then `B = 0`.  But then the quantity is identically `0` and cannot tend
to `1`. -/
theorem maass_empty_at_zero (M : FirstOrderFreeRadialData)
    (hr : M.spectralParameter = 0) : False := by
  obtain ⟨A, B, hq⟩ := radial_normalization_quantity M hr
  have hpi2 : (0:ℝ) < 2 * Real.pi := by positivity
  have hnorm1 : Filter.Tendsto
      (fun y : ℝ => ‖((2 * Real.sqrt y * Real.exp (2 * Real.pi * y) : ℝ) : ℂ) *
        M.radialKernel y‖) Filter.atTop (nhds 1) := by
    simpa using M.radial_normalization.norm
  -- dividing the normalization quantity by `√y` kills it
  have hN : Filter.Tendsto
      (fun y : ℝ => ‖A * Complex.exp (((4 * Real.pi : ℝ) : ℂ) * (y : ℂ)) - B‖)
      Filter.atTop (nhds 0) := by
    have hdiv := (hnorm1.const_mul (2 * Real.pi)).div_atTop Real.tendsto_sqrt_atTop
    refine hdiv.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with y hy
    have hsy : (0:ℝ) < Real.sqrt y := Real.sqrt_pos.mpr hy
    have hrw : (A * ((Real.sqrt y : ℝ) : ℂ) *
          Complex.exp (((4 * Real.pi : ℝ) : ℂ) * (y : ℂ)) -
        B * ((Real.sqrt y : ℝ) : ℂ)) / ((2 * Real.pi : ℝ) : ℂ)
        = ((Real.sqrt y : ℝ) : ℂ) *
            (A * Complex.exp (((4 * Real.pi : ℝ) : ℂ) * (y : ℂ)) - B) /
          ((2 * Real.pi : ℝ) : ℂ) := by ring
    rw [hq y hy, hrw, norm_div, norm_mul]
    simp only [Complex.norm_real, Real.norm_of_nonneg hsy.le,
      Real.norm_of_nonneg hpi2.le]
    field_simp
  -- the growing mode must be absent
  have hA0 : A = 0 := by
    by_contra hA
    have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hA
    have h4 : (0:ℝ) < 4 * Real.pi := by positivity
    have hAexp : Filter.Tendsto
        (fun y : ℝ => ‖A‖ * Real.exp (4 * Real.pi * y)) Filter.atTop Filter.atTop :=
      Filter.Tendsto.const_mul_atTop hApos
        (Real.tendsto_exp_atTop.comp (Filter.Tendsto.const_mul_atTop h4 Filter.tendsto_id))
    obtain ⟨y, hy1, hy2⟩ :=
      ((hN.eventually_lt_const (by norm_num : (0:ℝ) < 1)).and
        (hAexp.eventually_gt_atTop (‖B‖ + 1))).exists
    have hnE : ‖A * Complex.exp (((4 * Real.pi : ℝ) : ℂ) * (y : ℂ))‖
        = ‖A‖ * Real.exp (4 * Real.pi * y) := by
      rw [norm_mul, Complex.norm_exp]
      congr 1
      simp
    have : ‖A * Complex.exp (((4 * Real.pi : ℝ) : ℂ) * (y : ℂ))‖
        ≤ ‖A * Complex.exp (((4 * Real.pi : ℝ) : ℂ) * (y : ℂ)) - B‖ + ‖B‖ := by
      simpa using
        norm_add_le (A * Complex.exp (((4 * Real.pi : ℝ) : ℂ) * (y : ℂ)) - B) B
    rw [hnE] at this
    linarith
  -- and then so must the decaying one
  have hB0 : B = 0 := by
    rw [hA0] at hN
    simp only [zero_mul, zero_sub, norm_neg] at hN
    have := tendsto_nhds_unique hN tendsto_const_nhds
    exact norm_eq_zero.mp this.symm
  -- so the normalization quantity is identically zero
  have hzero : Filter.Tendsto
      (fun _ : ℝ => (0 : ℂ)) Filter.atTop (nhds 1) := by
    refine M.radial_normalization.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with y hy
    rw [hq y hy, hA0, hB0]
    simp
  exact zero_ne_one (tendsto_nhds_unique hzero tendsto_const_nhds).symm

end CriticalLinePhasor.ThreeDConverse

#print axioms CriticalLinePhasor.ThreeDConverse.radial_normalization_quantity
#print axioms CriticalLinePhasor.ThreeDConverse.radial_eq_exp_combination
#print axioms CriticalLinePhasor.ThreeDConverse.radial_growing_mode_const
#print axioms CriticalLinePhasor.ThreeDConverse.radial_decaying_mode_const
#print axioms CriticalLinePhasor.ThreeDConverse.radial_equation_at_zero
#print axioms CriticalLinePhasor.ThreeDConverse.radial_factor_at_zero
#print axioms CriticalLinePhasor.ThreeDConverse.maass_empty_at_zero
