import RequestProject.ZetaContourArgument
import RequestProject.XiPartialFraction
import RequestProject.XiOrderSummable

/-!
# The S(t) explicit bridge: `S_classical` as an exact zero-packet sum

The finite-height, all-terms-retained bridge between the independently continued
classical argument `classicalSContour` and a source-defined spectral functional:
a sum of per-zero *packets* over the actual zero multiset (wherever the zeros
are), plus explicitly retained smooth terms.  Everything here is unconditional.

## The chain

* `xiContourLog_zero_im` — the completed contour lift starts at a real value:
  its imaginary part at the contour start `s = 2` is zero.
* `pi_mul_classicalSContour_eq_contour_im` (**Rung A**) — the classical
  argument in `π`-units is the imaginary part of the two-leg `logDeriv ξ`
  contour integral, minus the clock `ϑ(T)` and the completion polynomial's
  half-turn `π`:

  `π·S_classical(T) = (i·∫₀ᵀ logDeriv ξ(2+iy) dy − ∫_{1/2}^2 logDeriv ξ(x+iT) dx).im − ϑ(T) − π`.

* `horizontal_integral_eq_packets` (**Rung B**, interchange) — substituting the
  unconditional Hadamard partial fraction (`ZD.xi_logDeriv_partial_fraction`)
  into the horizontal leg and interchanging sum and integral (dominated by the
  compiled zero-density majorant `ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros`):

  `∫_{1/2}^2 logDeriv ξ(x+iT) dx = (3/2)·A + Σ'_ρ m_ρ·∫_{1/2}^2 (1/(x+iT−ρ) + 1/ρ) dx`.

* `exists_stExplicitBridge` (**capstone**) — combining the two rungs: there is
  one global constant `A` (the Hadamard constant) such that at every good
  height

  `π·S_classical(T) = (i·∫₀ᵀ logDeriv ξ(2+iy) dy).im − (3/2)·A.im − Σ'_ρ m_ρ·zeroPacket T ρ − ϑ(T) − π`,

  with `zeroPacket T ρ = (∫_{1/2}^2 (1/(x+iT−ρ) + 1/ρ) dx).im` the arctan-type
  packet of the zero `ρ` against the horizontal leg.  Every term is retained:
  the vertical leg (the arithmetic side, prime-power expandable at `Re = 2`),
  the Hadamard constant, the per-zero packets with multiplicity, the clock,
  and the endpoint half-turn.

## Scope (exact)

Unconditional throughout; no RH/GRH is assumed or proven.  The packets are
indexed by the zeros *wherever they are* — no on-line hypothesis enters.  The
identification of the packet sum with a function of on-line ordinates alone is
exactly the off-line-census question (`classicalSContour_eq_Smult_iff_offLine_eq_zero`)
and is deliberately not made here.
-/

open Complex Set MeasureTheory intervalIntegral
open scoped Real Topology BigOperators

noncomputable section

namespace CriticalLinePhasor.StBridge

open CriticalLinePhasor CriticalLinePhasor.CarrierScale
  CriticalLinePhasor.ContourArgument CriticalLinePhasor.ResolventLimit

/-! ## §0 The zero index is countable -/

/-- The nontrivial zeros are countable: they are a union over `n : ℕ` of the
finite ball intersections supplied by the Jensen count. -/
theorem countable_nontrivialZeros : ZD.NontrivialZeros.Countable := by
  have hsub : ZD.NontrivialZeros ⊆
      ⋃ n : ℕ, ZD.NontrivialZeros ∩ Metric.closedBall 0 (n : ℝ) := by
    intro ρ hρ
    refine Set.mem_iUnion.mpr ⟨⌈‖ρ‖⌉₊, hρ, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact Nat.le_ceil ‖ρ‖
  exact Set.Countable.mono hsub
    (Set.countable_iUnion fun n =>
      (ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite (n : ℝ)).countable)

instance : Countable {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} :=
  countable_nontrivialZeros.to_subtype

/-! ## §1 The start of the completed lift is real -/

/-- The completed contour lift starts at a real value: at the contour start
`s = 2` all three summands (`log` of the completion polynomial, the Gamma
branch, and the normalized zeta lift) are real. -/
theorem xiContourLog_zero_im {T : ℝ} (hT : GoodHeight T) :
    (xiContourLog hT 0).im = 0 := by
  have hstart : standardContour T 0 = 2 := (standardContour T).source
  have hlift : contourLogLift hT 0 = initialLog :=
    IsCoveringMap.liftPath_zero _ _ _ _
  rw [xiContourLog]
  simp only [ContinuousMap.coe_mk, hstart, hlift]
  have hpoly : (xiPolynomialLog 2).im = 0 := by
    rw [xiPolynomialLog]
    have h21 : (2 : ℂ) - 1 = 1 := by norm_num
    rw [h21, Complex.log_one]
    have harg : Complex.arg 2 = 0 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num]
      exact Complex.arg_ofReal_of_nonneg (by norm_num)
    simp [Complex.log_im, harg]
  have hgamma : (gammaLog 2).im = 0 := by
    rw [gammaLog]
    simp
  have hinit : initialLog.im = 0 := by
    rw [initialLog]
    simp
  simp [Complex.add_im, hpoly, hgamma, hinit]

/-! ## §2 Rung A: the classical argument as a two-leg contour integral -/

/-- **Rung A.**  The classical continued argument, in `π`-units, is the
imaginary part of the `logDeriv ξ` integral along `2 → 2+iT → 1/2+iT`, minus
the Gamma clock and the completion polynomial's half-turn.  Every term is
retained; nothing is asymptotic. -/
theorem pi_mul_classicalSContour_eq_contour_im {T : ℝ} (hT : GoodHeight T) :
    Real.pi * classicalSContour hT =
      (I * (∫ y in (0:ℝ)..T, logDeriv ZD.riemannXi (2 + (y : ℂ) * I)) -
        ∫ x in (1/2 : ℝ)..2, logDeriv ZD.riemannXi ((x : ℂ) + (T : ℂ) * I)).im
      - theta T - Real.pi := by
  have h := halfContourIntegral_logDeriv_riemannXi_eq_lift_sub hT
  have him := congrArg Complex.im h
  rw [Complex.sub_im, Complex.sub_im, xiContourLog_one_im hT,
    xiContourLog_zero_im hT, sub_zero] at him
  rw [Complex.sub_im]
  have hclock : Real.pi * (theta T / Real.pi) = theta T :=
    mul_div_cancel₀ _ Real.pi_ne_zero
  have hexp : Real.pi * (classicalSContour hT + theta T / Real.pi + 1)
      = Real.pi * classicalSContour hT + theta T + Real.pi := by
    rw [mul_add, mul_add, hclock, mul_one]
  rw [hexp] at him
  linarith [him]

/-! ## §3 The zero packets and their majorant -/

/-- The horizontal packet integrand of the zero `ρ` at height `T`: the
Hadamard pair term read on the segment `x + iT`, `x ∈ [1/2, 2]`. -/
def packetTerm (T : ℝ) (ρ : ℂ) (x : ℝ) : ℂ :=
  1 / ((x : ℂ) + (T : ℂ) * I - ρ) + 1 / ρ

/-- The real zero-packet: the imaginary part of the horizontal packet
integral.  This is the per-zero contribution to `S_classical`. -/
def zeroPacket (T : ℝ) (ρ : ℂ) : ℝ :=
  (∫ x in (1/2 : ℝ)..2, packetTerm T ρ x).im

/-- At a good height the packet denominator never vanishes for real `x`. -/
theorem packet_denom_ne_zero {T : ℝ} (hT : GoodHeight T) {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) (x : ℝ) :
    (x : ℂ) + (T : ℂ) * I - ρ ≠ 0 := by
  intro h
  apply hT.2 ρ hρ
  have hρeq : ρ = (x : ℂ) + (T : ℂ) * I := (sub_eq_zero.mp h).symm
  rw [hρeq]
  simp

/-- Nontrivial zeros are nonzero (their real part is positive). -/
theorem nontrivialZero_ne_zero {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) : ρ ≠ 0 := by
  intro h
  have h1 : (0 : ℝ) < ρ.re := hρ.1
  rw [h] at h1
  simp at h1

/-- Points of the horizontal segment are not nontrivial zeros: their
imaginary part is the good height `T`. -/
theorem segment_not_mem_nontrivialZeros {T : ℝ} (hT : GoodHeight T) (x : ℝ) :
    ((x : ℂ) + (T : ℂ) * I) ∉ ZD.NontrivialZeros := by
  intro hmem
  exact hT.2 _ hmem (by simp)

/-- The bundled continuous packet: for each zero `ρ`, the map
`x ↦ m_ρ · (1/(x+iT−ρ) + 1/ρ)` is continuous on all of `ℝ` (the good height
keeps the denominator away from zero). -/
def packetMap {T : ℝ} (hT : GoodHeight T)
    (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) : C(ℝ, ℂ) :=
  ⟨fun x => (ZD.xiOrderNat ρ.val : ℂ) * packetTerm T ρ.val x, by
    apply Continuous.mul continuous_const
    apply Continuous.add ?_ continuous_const
    apply Continuous.div continuous_const
    · exact (Complex.continuous_ofReal.add continuous_const).sub continuous_const
    · intro x
      exact packet_denom_ne_zero hT ρ.2 x⟩

/-- **The packet majorant.**  Away from the finite ball `‖ρ‖ < 2T+6`, the
packet integrand is uniformly dominated on the segment by
`2(T+2)/‖ρ‖²` — the summable zero-density weight. -/
theorem packetTerm_norm_le {T : ℝ} (hT : GoodHeight T) (hT0 : 0 < T) {ρ : ℂ}
    (hρ : ρ ∈ ZD.NontrivialZeros) (hbig : 2 * T + 6 ≤ ‖ρ‖) {x : ℝ}
    (hx : x ∈ Set.uIcc (1/2 : ℝ) 2) :
    ‖packetTerm T ρ x‖ ≤ 2 * (T + 2) / ‖ρ‖ ^ 2 := by
  rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 2)] at hx
  set s : ℂ := (x : ℂ) + (T : ℂ) * I with hs
  have hd : s - ρ ≠ 0 := sub_ne_zero.mpr fun h =>
    segment_not_mem_nontrivialZeros hT x (by rw [← hs, h]; exact hρ)
  have hρ0 : ρ ≠ 0 := nontrivialZero_ne_zero hρ
  have hids : packetTerm T ρ x = s / (ρ * (s - ρ)) := by
    rw [packetTerm, ← hs]
    field_simp
    ring
  have hsnorm : ‖s‖ ≤ T + 2 := by
    calc ‖s‖ ≤ ‖(x : ℂ)‖ + ‖(T : ℂ) * I‖ := norm_add_le _ _
    _ = |x| + |T| := by simp
    _ ≤ 2 + T := by
        have hx2 : |x| ≤ 2 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
        rw [abs_of_pos hT0]
        linarith
    _ = T + 2 := by ring
  have hρpos : (0 : ℝ) < ‖ρ‖ := lt_of_lt_of_le (by linarith) hbig
  have hhalf : T + 2 ≤ ‖ρ‖ / 2 := by linarith
  have hdenom : ‖ρ‖ / 2 ≤ ‖s - ρ‖ := by
    have h1 : ‖ρ‖ - ‖s‖ ≤ ‖s - ρ‖ := by
      have h2 := norm_sub_norm_le ρ s
      rwa [norm_sub_rev ρ s] at h2
    linarith
  have heq : (T + 2) / (‖ρ‖ * (‖ρ‖ / 2)) = 2 * (T + 2) / ‖ρ‖ ^ 2 := by
    have hne : ‖ρ‖ ≠ 0 := ne_of_gt hρpos
    field_simp
  rw [hids, norm_div, norm_mul, ← heq]
  gcongr

/-- The set of zeros inside any ball is finite, read on the subtype index. -/
theorem finite_smallZeros (R : ℝ) :
    {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} | ‖ρ.val‖ < R}.Finite := by
  have hfin := ZD.ZeroCount.NontrivialZeros_inter_closedBall_finite R
  have hpre : (Subtype.val ⁻¹'
      (ZD.NontrivialZeros ∩ Metric.closedBall 0 R) :
      Set {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}).Finite :=
    hfin.preimage Subtype.val_injective.injOn
  apply hpre.subset
  intro ρ hρ
  exact ⟨ρ.2, by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_lt hρ⟩

/-- The eventual (cofinite) lower bound on the zero norms. -/
theorem eventually_cofinite_norm_ge (R : ℝ) :
    ∀ᶠ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} in Filter.cofinite,
      R ≤ ‖ρ.val‖ :=
  Filter.eventually_cofinite.mpr (by simpa [not_le] using finite_smallZeros R)

/-- **Summability of the packet sup-norms** on the segment: the restricted
continuous packets are norm-summable, dominated eventually by the compiled
zero-density majorant. -/
theorem summable_packet_restrict_norm {T : ℝ} (hT : GoodHeight T) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      ‖ContinuousMap.restrict
        (↑(⟨Set.uIcc (1/2 : ℝ) 2, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ))
        (packetMap hT ρ)‖) := by
  have hg : Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      (2 * (T + 2)) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2)) :=
    (ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros).mul_left _
  apply Summable.of_norm_bounded_eventually hg
  filter_upwards [eventually_cofinite_norm_ge (2 * T + 6)] with ρ hbig
  have hC0 : (0 : ℝ) ≤ (2 * (T + 2)) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) :=
    mul_nonneg (by linarith [hT.1])
      (div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hnorm_le : ‖ContinuousMap.restrict
      (↑(⟨Set.uIcc (1/2 : ℝ) 2, isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ))
      (packetMap hT ρ)‖ ≤
      (2 * (T + 2)) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
    apply (ContinuousMap.norm_le _ hC0).mpr
    intro x
    show ‖(ZD.xiOrderNat ρ.val : ℂ) * packetTerm T ρ.val x.val‖ ≤ _
    rw [norm_mul]
    have hm : ‖(ZD.xiOrderNat ρ.val : ℂ)‖ = (ZD.xiOrderNat ρ.val : ℝ) := by
      simp
    rw [hm]
    calc (ZD.xiOrderNat ρ.val : ℝ) * ‖packetTerm T ρ.val x.val‖
        ≤ (ZD.xiOrderNat ρ.val : ℝ) * (2 * (T + 2) / ‖ρ.val‖ ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
          exact packetTerm_norm_le hT hT.1 ρ.2 hbig x.2
    _ = (2 * (T + 2)) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by ring
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  exact hnorm_le

/-! ## §4 Nonvanishing and continuity on the horizontal segment -/

/-- `ξ` does not vanish on the horizontal segment of a good contour. -/
theorem xi_ne_zero_on_segment {T : ℝ} (hT : GoodHeight T) {x : ℝ}
    (hx : x ∈ Set.uIcc (1/2 : ℝ) 2) :
    ZD.riemannXi ((x : ℂ) + (T : ℂ) * I) ≠ 0 := by
  rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 2)] at hx
  set s : ℂ := (x : ℂ) + (T : ℂ) * I with hs
  have hsre : s.re = x := by simp [hs]
  have hsim : s.im = T := by simp [hs]
  have hre : 0 < s.re := by rw [hsre]; linarith [hx.1]
  have hs1 : s ≠ 1 := by
    intro h
    have : s.im = 0 := by rw [h]; simp
    rw [hsim] at this
    exact hT.1.ne' this
  have hs0 : s ≠ 0 := by
    intro h
    have : s.im = 0 := by rw [h]; simp
    rw [hsim] at this
    exact hT.1.ne' this
  rw [riemannXi_eq_unit_mul_zeta hre hs1]
  apply mul_ne_zero
  · apply div_ne_zero (mul_ne_zero hs0 (sub_ne_zero.mpr hs1)) two_ne_zero
  apply mul_ne_zero
  · exact Complex.Gammaℝ_ne_zero_of_re_pos hre
  · -- ζ(s) ≠ 0: on `re ≥ 1` by the zero-free region; on `re < 1` a zero
    -- would be a nontrivial zero with ordinate `T`, excluded by goodness.
    intro hzeta
    rcases lt_or_ge s.re 1 with hlt | hge
    · exact hT.2 s ⟨hre, hlt, hzeta⟩ hsim
    · exact riemannZeta_ne_zero_of_one_le_re hge hzeta

/-- `logDeriv ξ` is continuous on the horizontal segment. -/
theorem continuousOn_logDeriv_xi_segment {T : ℝ} (hT : GoodHeight T) :
    ContinuousOn (fun x : ℝ => logDeriv ZD.riemannXi ((x : ℂ) + (T : ℂ) * I))
      (Set.uIcc (1/2 : ℝ) 2) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  have hs : Continuous (fun x : ℝ => (x : ℂ) + (T : ℂ) * I) :=
    Complex.continuous_ofReal.add continuous_const
  have hxi : AnalyticAt ℂ ZD.riemannXi ((x : ℂ) + (T : ℂ) * I) :=
    ZD.riemannXi_differentiable.analyticAt _
  have hlog : ContinuousAt (logDeriv ZD.riemannXi) ((x : ℂ) + (T : ℂ) * I) := by
    have heq : logDeriv ZD.riemannXi =
        fun s => deriv ZD.riemannXi s / ZD.riemannXi s := by
      funext s
      exact logDeriv_apply _ _
    rw [heq]
    exact ContinuousAt.div (hxi.deriv.continuousAt) hxi.continuousAt
      (xi_ne_zero_on_segment hT hx)
  exact ContinuousAt.comp (g := logDeriv ZD.riemannXi)
    (f := fun x : ℝ => (x : ℂ) + (T : ℂ) * I) hlog hs.continuousAt

/-! ## §5 Rung B: the horizontal leg is the Hadamard constant plus the packets -/

/-- **Rung B (interchange).**  At a good height, substituting the Hadamard
partial fraction into the horizontal leg and interchanging sum and integral:

`∫_{1/2}^2 logDeriv ξ(x+iT) dx = (3/2)·A + Σ'_ρ m_ρ·∫_{1/2}^2 (1/(x+iT−ρ) + 1/ρ) dx`.

The interchange is dominated: the packets' sup-norms are summable against the
compiled zero-density weight.  No term is dropped and nothing is asymptotic. -/
theorem horizontal_integral_eq_packets {T : ℝ} (hT : GoodHeight T) {A : ℂ}
    (hA : ∀ s : ℂ, s ∉ ZD.NontrivialZeros →
      deriv ZD.riemannXi s / ZD.riemannXi s =
        A + ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          (ZD.xiOrderNat ρ.val : ℂ) * (1 / (s - ρ.val) + 1 / ρ.val)) :
    (∫ x in (1/2 : ℝ)..2, logDeriv ZD.riemannXi ((x : ℂ) + (T : ℂ) * I)) =
      (3/2 : ℝ) • A + ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        ∫ x in (1/2 : ℝ)..2, (ZD.xiOrderNat ρ.val : ℂ) * packetTerm T ρ.val x := by
  have hint : IntervalIntegrable
      (fun x : ℝ => logDeriv ZD.riemannXi ((x : ℂ) + (T : ℂ) * I))
      volume (1/2 : ℝ) 2 :=
    (continuousOn_logDeriv_xi_segment hT).intervalIntegrable
  have hkey : (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      ∫ x in (1/2 : ℝ)..2, (packetMap hT ρ) x) =
      ∫ x in (1/2 : ℝ)..2, ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (packetMap hT ρ) x :=
    intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm
      (summable_packet_restrict_norm hT)
  have hpt : Set.EqOn
      (fun x : ℝ => ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, (packetMap hT ρ) x)
      (fun x : ℝ => logDeriv ZD.riemannXi ((x : ℂ) + (T : ℂ) * I) - A)
      (Set.uIcc (1/2 : ℝ) 2) := by
    intro x _
    have hmem := segment_not_mem_nontrivialZeros hT x
    have hAx := hA _ hmem
    show (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) * packetTerm T ρ.val x) =
      logDeriv ZD.riemannXi ((x : ℂ) + (T : ℂ) * I) - A
    rw [logDeriv_apply, hAx]
    simp only [packetTerm]
    ring
  rw [intervalIntegral.integral_congr hpt] at hkey
  rw [intervalIntegral.integral_sub hint intervalIntegrable_const,
    intervalIntegral.integral_const] at hkey
  have h32 : ((2 : ℝ) - 1/2) = (3/2 : ℝ) := by norm_num
  rw [h32] at hkey
  -- `hkey : Σ' ∫ packet = ∫ logDeriv − (3/2)•A`; rearrange.
  have hgoal : (∫ x in (1/2 : ℝ)..2, logDeriv ZD.riemannXi ((x : ℂ) + (T : ℂ) * I)) =
      (3/2 : ℝ) • A + (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        ∫ x in (1/2 : ℝ)..2, (packetMap hT ρ) x) := by
    rw [hkey]
    abel
  rw [hgoal]
  rfl

/-! ## §6 Summability of the packet integrals -/

/-- The complex packet integrals are summable (norm-bounded by the majorant
times the segment length). -/
theorem summable_packet_integral {T : ℝ} (hT : GoodHeight T) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      ∫ x in (1/2 : ℝ)..2, (ZD.xiOrderNat ρ.val : ℂ) * packetTerm T ρ.val x) := by
  have hg : Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      (3/2 : ℝ) * ((2 * (T + 2)) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2))) :=
    ((ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros).mul_left _).mul_left _
  apply Summable.of_norm_bounded_eventually hg
  filter_upwards [eventually_cofinite_norm_ge (2 * T + 6)] with ρ hbig
  have hbound : ∀ x ∈ Set.uIcc (1/2 : ℝ) 2,
      ‖(ZD.xiOrderNat ρ.val : ℂ) * packetTerm T ρ.val x‖ ≤
        (2 * (T + 2)) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
    intro x hx
    rw [norm_mul]
    have hm : ‖(ZD.xiOrderNat ρ.val : ℂ)‖ = (ZD.xiOrderNat ρ.val : ℝ) := by simp
    rw [hm]
    calc (ZD.xiOrderNat ρ.val : ℝ) * ‖packetTerm T ρ.val x‖
        ≤ (ZD.xiOrderNat ρ.val : ℝ) * (2 * (T + 2) / ‖ρ.val‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (packetTerm_norm_le hT hT.1 ρ.2 hbig hx)
            (Nat.cast_nonneg _)
    _ = (2 * (T + 2)) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by ring
  have hle : ‖∫ x in (1/2 : ℝ)..2, (ZD.xiOrderNat ρ.val : ℂ) * packetTerm T ρ.val x‖ ≤
      (2 * (T + 2)) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) * |2 - 1/2| :=
    intervalIntegral.norm_integral_le_of_norm_le_const (fun x hx => by
      apply hbound
      rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 2)]
      rw [Set.uIoc_of_le (by norm_num : (1/2 : ℝ) ≤ 2)] at hx
      exact Set.Ioc_subset_Icc_self hx)
  rw [show |(2 : ℝ) - 1/2| = 3/2 by norm_num] at hle
  calc ‖∫ x in (1/2 : ℝ)..2, (ZD.xiOrderNat ρ.val : ℂ) * packetTerm T ρ.val x‖
      ≤ (2 * (T + 2)) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) * (3/2) := hle
  _ = (3/2 : ℝ) * ((2 * (T + 2)) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2)) := by
      ring

/-! ## §7 The capstone: `S_classical` as an exact zero-packet sum -/

/-- **The explicit bridge.**  There is a single global constant `A` — the
Hadamard constant of `ξ'/ξ` — such that at every good height `T`:

`π·S_classical(T) = (i·∫₀ᵀ logDeriv ξ(2+iy) dy).im − (3/2)·A.im − Σ'_ρ m_ρ·zeroPacket T ρ − ϑ(T) − π`.

The sum runs over the actual zero multiset (no on-line hypothesis); the
vertical leg is the arithmetic side (prime-power expandable at `Re = 2`); the
clock `ϑ` and the endpoint half-turn are retained exactly.  Unconditional. -/
theorem exists_stExplicitBridge :
    ∃ A : ℂ, ∀ T : ℝ, ∀ hT : GoodHeight T,
      Real.pi * classicalSContour hT =
        (I * (∫ y in (0:ℝ)..T, logDeriv ZD.riemannXi (2 + (y : ℂ) * I))).im
        - (3/2 : ℝ) * A.im
        - (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
            (ZD.xiOrderNat ρ.val : ℝ) * zeroPacket T ρ.val)
        - theta T - Real.pi := by
  obtain ⟨A, hA⟩ := ZD.xi_logDeriv_partial_fraction
  refine ⟨A, fun T hT => ?_⟩
  rw [pi_mul_classicalSContour_eq_contour_im hT, Complex.sub_im,
    horizontal_integral_eq_packets hT hA]
  rw [Complex.add_im]
  have hsmul : ((3/2 : ℝ) • A).im = (3/2 : ℝ) * A.im := by
    rw [Complex.real_smul]
    simp
  rw [hsmul]
  have htsum_im : (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      ∫ x in (1/2 : ℝ)..2, (ZD.xiOrderNat ρ.val : ℂ) * packetTerm T ρ.val x).im =
      ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℝ) * zeroPacket T ρ.val := by
    have hmap := ContinuousLinearMap.map_tsum Complex.imCLM
      (summable_packet_integral hT)
    simp only [Complex.imCLM_apply] at hmap
    rw [hmap]
    apply tsum_congr
    intro ρ
    rw [intervalIntegral.integral_const_mul]
    show ((ZD.xiOrderNat ρ.val : ℂ) * _).im = _
    rw [zeroPacket]
    have : ((ZD.xiOrderNat ρ.val : ℂ) *
        (∫ x in (1/2 : ℝ)..2, packetTerm T ρ.val x)).im =
        (ZD.xiOrderNat ρ.val : ℝ) *
        (∫ x in (1/2 : ℝ)..2, packetTerm T ρ.val x).im := by
      rw [Complex.mul_im]
      simp
    rw [this]
  rw [htsum_im]
  ring

end CriticalLinePhasor.StBridge

#print axioms CriticalLinePhasor.StBridge.countable_nontrivialZeros
#print axioms CriticalLinePhasor.StBridge.xiContourLog_zero_im
#print axioms CriticalLinePhasor.StBridge.pi_mul_classicalSContour_eq_contour_im
#print axioms CriticalLinePhasor.StBridge.packetTerm_norm_le
#print axioms CriticalLinePhasor.StBridge.summable_packet_restrict_norm
#print axioms CriticalLinePhasor.StBridge.xi_ne_zero_on_segment
#print axioms CriticalLinePhasor.StBridge.horizontal_integral_eq_packets
#print axioms CriticalLinePhasor.StBridge.summable_packet_integral
#print axioms CriticalLinePhasor.StBridge.exists_stExplicitBridge
