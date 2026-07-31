import RequestProject.RankLadderParity

/-!
# The Bessel order ladder: rank = Bessel order, exactly

Certifier (b)'s exact resummation brick, promoted from the measured probe law
(`tmp/eps_from_parity.py`, route (b): rank = Bessel order exact to 1e−13): the
elliptic dual kernel at rank `r` IS its Bessel-ORDER-ladder resummation — rank `r`
enters the dual side ONLY through orders `r` and `r + 2` of the cosine kernel.
Exact, identity-class, uniform in the rank; no asymptotics anywhere.

* `chebU_cos_sin` — the clock form of the Satake character:
  `U_r(cos θ)·sin θ = sin((r+1)θ)`, by strong induction from the `chebU` recurrence.
* `cosKernel` — the order channel: `∫_0^π cos(nθ)·e^{-iz·cosθ} dθ`.  Classically this
  is `π·(−i)^n·J_n(z)` (Bessel's integral); here it is the DEFINITION of the order-`n`
  channel — no Bessel asymptotics are imported.
* `semicircleTransform_eq_orderLadder` — **the ladder theorem**: for every rank `r`
  and every frequency `z`,

    `∫_{-1}^{1} √(1−x²)·U_r(x)·e^{-izx} dx = ½·(cosKernel r z − cosKernel (r+2) z)`.

  One classical substitution `x = cos θ` (Mathlib's change-of-variables on the
  interval) plus finite trig algebra (`2 sinθ·sin((r+1)θ) = cos(rθ) − cos((r+2)θ)`).
* `cosKernel_neg` — the μ₂ parity of the order channel:
  `cosKernel n (−z) = (−1)^n · cosKernel n z`, by the substitution `θ ↦ π − θ`.
* `semicircleTransform_neg` — rank parity = order parity: the `(−1)^r` clock of
  `RankLadderParity` is recovered through the order ladder, since orders `r` and
  `r + 2` share one parity.
* `dualIntegral_semicircle` — the tie to the compiled rank-ladder object: the
  semicircle-profile `dualIntegral` of `RankLadderParity` at frequency `ξ`, scale `c`
  is exactly the order ladder at `z = 2πξc`.

Everything here is unconditional: interval-integral identities, continuity, and
finite trig algebra.  No integrability is assumed (continuity supplies it), no
L-function enters.
-/

open Complex intervalIntegral
open CriticalLinePhasor.RankLadderParity

namespace CriticalLinePhasor.BesselOrderLadder

/-! ## The clock form of the Satake character -/

/-- **The clock form of `U_r`**: `U_r(cos θ)·sin θ = sin((r+1)θ)` — the `(r+1)`-clock
reading of the second-kind Chebyshev character, by strong induction from the
`chebU` recurrence. -/
theorem chebU_cos_sin (r : ℕ) (θ : ℝ) :
    chebU r (Real.cos θ) * Real.sin θ = Real.sin (((r : ℝ) + 1) * θ) := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r with
    | 0 => simp [chebU]
    | 1 =>
      show 2 * Real.cos θ * Real.sin θ = Real.sin ((((1 : ℕ) : ℝ) + 1) * θ)
      have h2 : (((1 : ℕ) : ℝ) + 1) * θ = 2 * θ := by ring
      rw [h2, Real.sin_two_mul]
      ring
    | (n + 2) =>
      have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      show (2 * Real.cos θ * chebU (n + 1) (Real.cos θ) - chebU n (Real.cos θ)) *
          Real.sin θ = Real.sin ((((n + 2 : ℕ) : ℝ) + 1) * θ)
      have e2 : (((n + 1 : ℕ) : ℝ) + 1) * θ = ((n : ℝ) + 2) * θ := by push_cast; ring
      have e1 : (((n : ℕ) : ℝ) + 1) * θ = ((n : ℝ) + 2) * θ - θ := by ring
      have e3 : (((n + 2 : ℕ) : ℝ) + 1) * θ = ((n : ℝ) + 2) * θ + θ := by push_cast; ring
      rw [e2] at h1
      rw [e1, Real.sin_sub] at h0
      rw [e3, Real.sin_add]
      linear_combination 2 * Real.cos θ * h1 - h0

/-- Continuity of the Satake clock character, uniformly in the rank. -/
theorem continuous_chebU (r : ℕ) : Continuous (chebU r) := by
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    match r with
    | 0 =>
      show Continuous fun _ : ℝ => (1 : ℝ)
      exact continuous_const
    | 1 =>
      show Continuous fun x : ℝ => 2 * x
      exact continuous_const.mul continuous_id
    | (n + 2) =>
      have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      show Continuous fun x : ℝ => 2 * x * chebU (n + 1) x - chebU n x
      exact ((continuous_const.mul continuous_id).mul h1).sub h0

/-! ## The order channel -/

/-- The order-`n` integrand of the cosine kernel on the carrier clock `θ ∈ [0, π]`. -/
noncomputable def cosKernelIntegrand (n : ℕ) (z : ℝ) (θ : ℝ) : ℂ :=
  ((Real.cos ((n : ℝ) * θ) : ℝ) : ℂ) *
    Complex.exp (-Complex.I * (z : ℂ) * ((Real.cos θ : ℝ) : ℂ))

/-- **The order channel**: `cosKernel n z = ∫_0^π cos(nθ)·e^{-iz·cosθ} dθ`.
Classically this equals `π·(−i)^n·J_n(z)` (Bessel's integral); here it is the
definition of the order-`n` channel — no asymptotics, no special-function
theory imported. -/
noncomputable def cosKernel (n : ℕ) (z : ℝ) : ℂ :=
  ∫ θ in (0 : ℝ)..Real.pi, cosKernelIntegrand n z θ

/-- The order-channel integrand is continuous. -/
theorem continuous_cosKernelIntegrand (n : ℕ) (z : ℝ) :
    Continuous (cosKernelIntegrand n z) := by
  unfold cosKernelIntegrand
  exact (Complex.continuous_ofReal.comp
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))).mul
    (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp Real.continuous_cos)))

/-! ## The elliptic dual kernel and the ladder theorem -/

/-- The elliptic dual kernel at rank `r` and frequency `z`: the semicircle-weighted
`U_r`-transform `∫_{-1}^{1} √(1−x²)·U_r(x)·e^{-izx} dx` — the shape of the rank-`r`
dual term of the ladder. -/
noncomputable def semicircleTransform (r : ℕ) (z : ℝ) : ℂ :=
  ∫ x in (-1 : ℝ)..1,
    ((Real.sqrt (1 - x ^ 2) * chebU r x : ℝ) : ℂ) *
      Complex.exp (-Complex.I * (z : ℂ) * ((x : ℝ) : ℂ))

/-- **The Bessel order ladder**: rank `r` enters the dual side only through orders
`r` and `r + 2` of the cosine kernel —

  `∫_{-1}^{1} √(1−x²)·U_r(x)·e^{-izx} dx = ½·(cosKernel r z − cosKernel (r+2) z)`.

Exact and identity-class, for every rank and every frequency: the substitution
`x = cos θ` plus `2 sinθ·sin((r+1)θ) = cos(rθ) − cos((r+2)θ)`.  No asymptotics. -/
theorem semicircleTransform_eq_orderLadder (r : ℕ) (z : ℝ) :
    semicircleTransform r z = (1 / 2 : ℂ) * (cosKernel r z - cosKernel (r + 2) z) := by
  set g : ℝ → ℂ := fun x =>
    ((Real.sqrt (1 - x ^ 2) * chebU r x : ℝ) : ℂ) *
      Complex.exp (-Complex.I * (z : ℂ) * ((x : ℝ) : ℂ)) with hgdef
  have hgc : Continuous g := by
    rw [hgdef]
    exact (Complex.continuous_ofReal.comp
        ((Real.continuous_sqrt.comp (continuous_const.sub (continuous_pow 2))).mul
          (continuous_chebU r))).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  -- the substitution x = cos θ
  have hsub := intervalIntegral.integral_deriv_smul_comp
    (f := Real.cos) (f' := fun x => -Real.sin x) (a := 0) (b := Real.pi)
    (fun x _ => Real.hasDerivAt_cos x) (Real.continuous_sin.neg.continuousOn) hgc
  simp only [Function.comp_apply, Real.cos_zero, Real.cos_pi] at hsub
  have hL : (∫ θ in (0 : ℝ)..Real.pi, -Real.sin θ • g (Real.cos θ))
      = -∫ θ in (0 : ℝ)..Real.pi, Real.sin θ • g (Real.cos θ) := by
    calc (∫ θ in (0 : ℝ)..Real.pi, -Real.sin θ • g (Real.cos θ))
        = ∫ θ in (0 : ℝ)..Real.pi, -(Real.sin θ • g (Real.cos θ)) :=
          intervalIntegral.integral_congr fun θ _ => neg_smul _ _
      _ = -∫ θ in (0 : ℝ)..Real.pi, Real.sin θ • g (Real.cos θ) :=
          intervalIntegral.integral_neg
  have hR : (∫ x in (1 : ℝ)..(-1), g x) = -∫ x in (-1 : ℝ)..1, g x :=
    intervalIntegral.integral_symm (-1) 1
  rw [hL, hR] at hsub
  have hmain : semicircleTransform r z
      = ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ • g (Real.cos θ) := by
    calc semicircleTransform r z = ∫ x in (-1 : ℝ)..1, g x := by rw [hgdef]; rfl
      _ = ∫ θ in (0 : ℝ)..Real.pi, Real.sin θ • g (Real.cos θ) :=
          (neg_injective hsub).symm
  -- the pointwise trig closure on the clock
  have hpt : Set.EqOn (fun θ => Real.sin θ • g (Real.cos θ))
      (fun θ => (1 / 2 : ℂ) * (cosKernelIntegrand r z θ - cosKernelIntegrand (r + 2) z θ))
      (Set.uIcc (0 : ℝ) Real.pi) := by
    intro θ hθ
    rw [Set.uIcc_of_le Real.pi_pos.le] at hθ
    have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ.1 hθ.2
    have hsqrt : Real.sqrt (1 - Real.cos θ ^ 2) = Real.sin θ := by
      rw [← Real.sin_sq, Real.sqrt_sq hsin]
    have hkey : Real.sin θ * (Real.sqrt (1 - Real.cos θ ^ 2) * chebU r (Real.cos θ))
        = 1 / 2 * (Real.cos ((r : ℝ) * θ) - Real.cos (((r : ℝ) + 2) * θ)) := by
      rw [hsqrt]
      have hU := chebU_cos_sin r θ
      have h2 := Real.two_mul_sin_mul_sin θ (((r : ℝ) + 1) * θ)
      have e1 : θ - ((r : ℝ) + 1) * θ = -((r : ℝ) * θ) := by ring
      have e2 : θ + ((r : ℝ) + 1) * θ = ((r : ℝ) + 2) * θ := by ring
      rw [e1, e2, Real.cos_neg] at h2
      linear_combination Real.sin θ * hU + h2 / 2
    have hkeyC := congrArg (fun t : ℝ => (t : ℂ)) hkey
    push_cast at hkeyC
    show Real.sin θ • g (Real.cos θ)
        = (1 / 2 : ℂ) * (cosKernelIntegrand r z θ - cosKernelIntegrand (r + 2) z θ)
    rw [hgdef, Complex.real_smul]
    unfold cosKernelIntegrand
    push_cast
    linear_combination Complex.exp (-Complex.I * (z : ℂ) * Complex.cos (θ : ℂ)) * hkeyC
  rw [hmain, intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub
      ((continuous_cosKernelIntegrand r z).intervalIntegrable _ _)
      ((continuous_cosKernelIntegrand (r + 2) z).intervalIntegrable _ _)]
  rfl

/-! ## The μ₂ parity of the order channel -/

/-- **The μ₂ parity of the order channel**: `cosKernel n (−z) = (−1)^n·cosKernel n z`,
by the clock substitution `θ ↦ π − θ` — the order channel ticks the same μ₂ clock as
the rank channel of `RankLadderParity`. -/
theorem cosKernel_neg (n : ℕ) (z : ℝ) :
    cosKernel n (-z) = (-1 : ℂ) ^ n * cosKernel n z := by
  have key : cosKernel n z = (-1 : ℂ) ^ n * cosKernel n (-z) := by
    have hflip := intervalIntegral.integral_comp_sub_left
      (a := (0 : ℝ)) (b := Real.pi) (cosKernelIntegrand n z) Real.pi
    rw [sub_self, sub_zero] at hflip
    have hcongr : Set.EqOn (fun θ => cosKernelIntegrand n z (Real.pi - θ))
        (fun θ => (-1 : ℂ) ^ n * cosKernelIntegrand n (-z) θ)
        (Set.uIcc (0 : ℝ) Real.pi) := by
      intro θ _
      unfold cosKernelIntegrand
      have hc : Real.cos ((n : ℝ) * (Real.pi - θ)) = (-1 : ℝ) ^ n * Real.cos ((n : ℝ) * θ) := by
        have e : (n : ℝ) * (Real.pi - θ) = (n : ℝ) * Real.pi - (n : ℝ) * θ := by ring
        rw [e]
        exact Real.cos_nat_mul_pi_sub ((n : ℝ) * θ) n
      have he : Complex.exp (-Complex.I * (z : ℂ) * ((Real.cos (Real.pi - θ) : ℝ) : ℂ))
          = Complex.exp (-Complex.I * ((-z : ℝ) : ℂ) * ((Real.cos θ : ℝ) : ℂ)) := by
        congr 1
        rw [Real.cos_pi_sub]
        push_cast
        ring
      simp only []
      rw [hc, he]
      push_cast
      ring
    calc cosKernel n z
        = ∫ θ in (0 : ℝ)..Real.pi, cosKernelIntegrand n z (Real.pi - θ) := hflip.symm
      _ = ∫ θ in (0 : ℝ)..Real.pi, (-1 : ℂ) ^ n * cosKernelIntegrand n (-z) θ :=
          intervalIntegral.integral_congr hcongr
      _ = (-1 : ℂ) ^ n * cosKernel n (-z) := intervalIntegral.integral_const_mul _ _
  have h2 : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
    rw [← mul_pow]; norm_num
  calc cosKernel n (-z)
      = (((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n)) * cosKernel n (-z) := by rw [h2, one_mul]
    _ = ((-1 : ℂ) ^ n) * (((-1 : ℂ) ^ n) * cosKernel n (-z)) := by rw [mul_assoc]
    _ = ((-1 : ℂ) ^ n) * cosKernel n z := by rw [← key]

/-- Even orders: the order channel is symmetric in the frequency. -/
theorem cosKernel_neg_even {n : ℕ} (hn : Even n) (z : ℝ) :
    cosKernel n (-z) = cosKernel n z := by
  rw [cosKernel_neg, hn.neg_one_pow, one_mul]

/-- Odd orders: the order channel is antisymmetric in the frequency. -/
theorem cosKernel_neg_odd {n : ℕ} (hn : Odd n) (z : ℝ) :
    cosKernel n (-z) = -cosKernel n z := by
  rw [cosKernel_neg, hn.neg_one_pow, neg_one_mul]

/-- **Rank parity = order parity**: the μ₂ clock of the rank channel is read off the
order ladder, since orders `r` and `r + 2` share one parity —
`semicircleTransform r (−z) = (−1)^r·semicircleTransform r z`. -/
theorem semicircleTransform_neg (r : ℕ) (z : ℝ) :
    semicircleTransform r (-z) = (-1 : ℂ) ^ r * semicircleTransform r z := by
  rw [semicircleTransform_eq_orderLadder, semicircleTransform_eq_orderLadder,
    cosKernel_neg, cosKernel_neg]
  have h : (-1 : ℂ) ^ (r + 2) = (-1 : ℂ) ^ r := by
    rw [pow_add]; norm_num
  rw [h]
  ring

/-! ## The tie to the compiled rank ladder -/

/-- **The semicircle dual channel IS the order ladder**: the rank-`r` `dualIntegral`
of `RankLadderParity` with the semicircle profile `Φ(x) = √(1−x²)` at frequency `ξ`
and scale `c` equals the order ladder at `z = 2πξc` — rank `r` enters the compiled
dual side only through orders `r` and `r + 2`. -/
theorem dualIntegral_semicircle (r : ℕ) (c ξ : ℝ) :
    dualIntegral (fun x => Real.sqrt (1 - x ^ 2)) r c ξ
      = (1 / 2 : ℂ) * (cosKernel r (2 * Real.pi * ξ * c)
          - cosKernel (r + 2) (2 * Real.pi * ξ * c)) := by
  rw [← semicircleTransform_eq_orderLadder r (2 * Real.pi * ξ * c)]
  unfold dualIntegral dualKernel semicircleTransform
  apply intervalIntegral.integral_congr
  intro x _
  simp only []
  congr 1
  congr 1
  push_cast
  ring

end CriticalLinePhasor.BesselOrderLadder

#print axioms CriticalLinePhasor.BesselOrderLadder.chebU_cos_sin
#print axioms CriticalLinePhasor.BesselOrderLadder.continuous_chebU
#print axioms CriticalLinePhasor.BesselOrderLadder.cosKernelIntegrand
#print axioms CriticalLinePhasor.BesselOrderLadder.cosKernel
#print axioms CriticalLinePhasor.BesselOrderLadder.continuous_cosKernelIntegrand
#print axioms CriticalLinePhasor.BesselOrderLadder.semicircleTransform
#print axioms CriticalLinePhasor.BesselOrderLadder.semicircleTransform_eq_orderLadder
#print axioms CriticalLinePhasor.BesselOrderLadder.cosKernel_neg
#print axioms CriticalLinePhasor.BesselOrderLadder.cosKernel_neg_even
#print axioms CriticalLinePhasor.BesselOrderLadder.cosKernel_neg_odd
#print axioms CriticalLinePhasor.BesselOrderLadder.semicircleTransform_neg
#print axioms CriticalLinePhasor.BesselOrderLadder.dualIntegral_semicircle
