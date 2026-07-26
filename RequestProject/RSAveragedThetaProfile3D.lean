import RequestProject.RSMaster
import RequestProject.GDecay
import RequestProject.RSEntireHolo

/-!
# The r = 2 rung's theta profile: the averaged lattice bank of a genuine cusp form

The Petersson average of the general lattice theta,

  `θ̄_f(t) = ∫_𝒟 P_f(z) · Θ_z(t)`,

is the theta profile of the Rankin–Selberg second moment of an actual level-one cusp form — the
carrier object whose Mellin transform is the completed `L(f×f)`-series of `rs_master`.  This file
derives, from the compiled pointwise weld `latticeTheta_inv` and nothing else:

* the exact weight-one reflection `θ̄_f(1/t) = t · θ̄_f(t)` (`averagedTheta_inv`) — pointwise, with
  no analytic candidate, no supplied functional equation, and no Poisson input beyond the compiled
  lattice weld;
* integrability, monotonicity, and the superpolynomial tail decay of `θ̄_f - ‖f‖²` from the
  compiled saddle bound `ptwise_bound`;
* the packaged `WeakFEPair` (`rsAveragedWeakFEPair`) with weight `1`, root number `1`, and both
  constant terms equal to the Petersson mass — from which Mathlib's abstract functional-equation
  machinery returns the entire part, the two poles with residues `±‖f‖²`, the global functional
  equation `Λ(1-s) = Λ(s)`, and the Mellin identification on `Re s > 1`.

This is the r = 2 continuation engine at the profile interface.  The profile genuinely carries a
constant term (the `ζ`-factor pole of `L(f×f)`), so its home is the weak pair, not the strong
one: the remaining r = 2-rung inputs are the ζ-peel from `L(f×f)` to the `Sym²` bank and the
coefficient identification with the literal twisted Satake bank — identification-layer steps,
named, not hidden.  No RH/GRH anywhere.
-/

open MeasureTheory Complex UpperHalfPlane ModularGroup Filter Set
open scoped Real MatrixGroups Topology

namespace CriticalLinePhasor.Unfolding

open CriticalLinePhasor.HeckeSupBound CriticalLinePhasor.EpsteinTheta

variable {k : ℤ}

/-! ## The averaged profile and the Petersson mass -/

/-- The Petersson mass of the form: the fundamental-domain integral of its Petersson density. -/
noncomputable def peterssonMass (k : ℤ) (f : CuspForm 𝒮ℒ k) : ℝ :=
  ∫ z in ModularGroup.fd, P k f z ∂volume

/-- The averaged lattice theta: the Petersson density paired with the general lattice bank at
carrier height `t`.  This is the theta profile of the Rankin–Selberg second moment. -/
noncomputable def averagedTheta (k : ℤ) (f : CuspForm 𝒮ℒ k) (t : ℝ) : ℝ :=
  ∫ z in ModularGroup.fd, P k f z * latticeTheta z t ∂volume

/-! ## Monotonicity of the lattice bank in the carrier height -/

/-- The Gram form is nonnegative. -/
lemma gram_nonneg (z : ℍ) (p : ℤ × ℤ) : 0 ≤ gram z p := by
  refine le_trans ?_ (gram_ge z p)
  have hy : 0 < z.im := z.im_pos
  have hd : 0 < z.re ^ 2 + z.im ^ 2 + 1 := by positivity
  positivity

/-- The lattice bank is antitone in the carrier height. -/
lemma latticeTheta_anti (z : ℍ) {t₁ t₂ : ℝ} (h0 : 0 < t₁) (h : t₁ ≤ t₂) :
    latticeTheta z t₂ ≤ latticeTheta z t₁ := by
  refine Summable.tsum_le_tsum (fun p => ?_)
    (summable_latticeTheta_term z (h0.trans_le h)) (summable_latticeTheta_term z h0)
  apply Real.exp_le_exp.mpr
  have hg := gram_nonneg z p
  nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr h)) hg]

/-! ## Integrability of the averaged integrands -/

/-- The Petersson density is integrable on the fundamental domain. -/
lemma integrableOn_P_fd (f : CuspForm 𝒮ℒ k) :
    IntegrableOn (P k f) ModularGroup.fd volume := by
  obtain ⟨M, hM⟩ := P_fd_bound f
  exact integrableOn_fd_of_bounded (P_continuous f)
    (C := M) fun z hz => by
      rw [Real.norm_of_nonneg (P_nonneg f z)]
      exact hM z hz

/-- The saddle weight is bounded on the nonnegative axis. -/
lemma wt_bddAbove (C₁ : ℝ) (_hC₁ : 0 ≤ C₁) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, 0 ≤ y → wt C₁ y ≤ B := by
  have hπ : Tendsto (fun y : ℝ => π * y) atTop atTop :=
    Tendsto.const_mul_atTop Real.pi_pos tendsto_id
  have h1 : Tendsto (fun y : ℝ => Real.exp (-(π * y))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atBot_iff.mpr hπ)
  have h2' : Tendsto (fun y : ℝ => (π * y) ^ 2 * Real.exp (-(π * y))) atTop (𝓝 0) :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hπ
  have h2 : Tendsto (fun y : ℝ => y ^ 2 * Real.exp (-(π * y))) atTop (𝓝 0) := by
    have h := h2'.const_mul ((π : ℝ) ^ 2)⁻¹
    simp only [mul_zero] at h
    refine h.congr fun y => ?_
    have hπ0 : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    field_simp
  have htend : Tendsto (fun y : ℝ => wt C₁ y) atTop (𝓝 0) := by
    have h3 := h1.add (h2.const_mul C₁)
    simp only [mul_zero, add_zero] at h3
    refine Tendsto.congr (fun y => ?_) h3
    unfold wt
    ring_nf
  have hev : ∀ᶠ y in atTop, wt C₁ y ≤ 1 :=
    htend.eventually (eventually_le_nhds one_pos)
  obtain ⟨A, hA⟩ := hev.exists_forall_of_atTop
  have hwt_cont : Continuous fun y : ℝ => wt C₁ y := by
    unfold wt
    fun_prop
  obtain ⟨B₀, hB₀⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := A)).exists_bound_of_continuousOn
    hwt_cont.continuousOn
  refine ⟨max B₀ 1, le_max_of_le_right one_pos.le, fun y hy => ?_⟩
  rcases le_or_gt y A with h | h
  · exact le_trans (le_trans (le_abs_self _)
      (by simpa [Real.norm_eq_abs] using hB₀ y ⟨hy, h⟩)) (le_max_left _ _)
  · exact le_trans (hA y h.le) (le_max_right _ _)

/-- The averaged tail integrand is integrable on the fundamental domain, at every carrier height
`t ≥ 1` — dominated by the compiled saddle bound. -/
lemma integrableOn_P_mul_tail (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {t : ℝ} (ht : 1 ≤ t) :
    IntegrableOn (fun z : ℍ => P k f z * (latticeTheta z t - 1))
      ModularGroup.fd volume := by
  obtain ⟨C₁, C₆, hC₁, hC₆, hbound⟩ := ptwise_bound f hk
  obtain ⟨B, hB0, hB⟩ := wt_bddAbove C₁ hC₁
  have hmeas : Measurable (fun z : ℍ => P k f z * (latticeTheta z t - 1)) :=
    (P_continuous f).measurable.mul
      ((measurable_latticeTheta.comp (measurable_id.prodMk measurable_const)).sub
        measurable_const)
  refine Integrable.mono' (g := fun _ => C₆ * B)
    (integrableOn_const volume_fd_lt_top.ne) hmeas.aestronglyMeasurable.restrict ?_
  filter_upwards [ae_restrict_mem measurableSet_fd] with z hz
  have h1 := hbound z hz t ht
  have hnn : 0 ≤ P k f z * (latticeTheta z t - 1) :=
    mul_nonneg (P_nonneg f z)
      (by linarith [one_le_latticeTheta z (lt_of_lt_of_le one_pos ht)])
  rw [Real.norm_of_nonneg hnn]
  calc P k f z * (latticeTheta z t - 1)
      ≤ C₆ * wt C₁ z.im * Real.exp (-(π * Real.sqrt (3 * t / 2))) := h1
    _ ≤ C₆ * B * 1 := by
        apply mul_le_mul _ (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity)))
          (Real.exp_pos _).le (mul_nonneg hC₆ hB0)
        exact mul_le_mul_of_nonneg_left (hB z.im z.im_pos.le) hC₆
    _ = C₆ * B := mul_one _

/-- The averaged tail integrand is integrable at every positive carrier height: below height one
the compiled weld transports the statement from above height one. -/
lemma integrableOn_P_mul_tail' (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun z : ℍ => P k f z * (latticeTheta z t - 1))
      ModularGroup.fd volume := by
  rcases le_or_gt 1 t with h | h
  · exact integrableOn_P_mul_tail f hk h
  · have hinv : (1 : ℝ) ≤ t⁻¹ := (one_le_inv₀ ht).mpr h.le
    have key : (fun z : ℍ => P k f z * (latticeTheta z t - 1)) =
        fun z : ℍ => t⁻¹ * (P k f z * (latticeTheta z t⁻¹ - 1)) +
          (t⁻¹ - 1) * P k f z := by
      funext z
      have h1 := latticeTheta_inv z (inv_pos.mpr ht)
      rw [inv_inv] at h1
      rw [h1]
      ring
    rw [key]
    exact ((integrableOn_P_mul_tail f hk hinv).const_mul _).add
      ((integrableOn_P_fd f).const_mul _)

/-- The averaged full integrand is integrable at every positive carrier height. -/
lemma integrableOn_P_mul_theta (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun z : ℍ => P k f z * latticeTheta z t) ModularGroup.fd volume := by
  have key : (fun z : ℍ => P k f z * latticeTheta z t) =
      fun z : ℍ => P k f z * (latticeTheta z t - 1) + P k f z := by
    funext z
    ring
  rw [key]
  exact (integrableOn_P_mul_tail' f hk ht).add (integrableOn_P_fd f)

/-! ## The derived reflection and the tail bound -/

/-- **The weight-one reflection of the averaged bank, derived from the compiled lattice weld.**
`θ̄_f(1/t) = t · θ̄_f(t)`: the pointwise `latticeTheta_inv` integrated against the Petersson
density.  No analytic candidate, no supplied theta reflection, no Poisson input. -/
theorem averagedTheta_inv (f : CuspForm 𝒮ℒ k) {t : ℝ} (ht : 0 < t) :
    averagedTheta k f t⁻¹ = t * averagedTheta k f t := by
  unfold averagedTheta
  rw [← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_fd fun z _ => ?_
  rw [latticeTheta_inv z ht]
  ring

/-- The averaged bank exceeds its Petersson mass: the tail is nonnegative. -/
lemma peterssonMass_le_averagedTheta (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) {t : ℝ}
    (ht : 0 < t) : peterssonMass k f ≤ averagedTheta k f t := by
  have hsub : averagedTheta k f t - peterssonMass k f =
      ∫ z in ModularGroup.fd, P k f z * (latticeTheta z t - 1) ∂volume := by
    unfold averagedTheta peterssonMass
    rw [← MeasureTheory.integral_sub (integrableOn_P_mul_theta f hk ht)
      (integrableOn_P_fd f)]
    refine setIntegral_congr_fun measurableSet_fd fun z _ => ?_
    ring
  have hnn : 0 ≤ averagedTheta k f t - peterssonMass k f := by
    rw [hsub]
    refine setIntegral_nonneg measurableSet_fd fun z _ => ?_
    exact mul_nonneg (P_nonneg f z) (by linarith [one_le_latticeTheta z ht])
  linarith

/-- **The superpolynomial tail bound**: above carrier height one the averaged bank approaches its
Petersson mass at the saddle rate, uniformly. -/
theorem averagedTheta_tail_bound (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t →
      averagedTheta k f t - peterssonMass k f ≤
        C * Real.exp (-(π * Real.sqrt (3 * t / 2))) := by
  obtain ⟨C₁, C₆, hC₁, hC₆, hbound⟩ := ptwise_bound f hk
  obtain ⟨B, hB0, hB⟩ := wt_bddAbove C₁ hC₁
  refine ⟨C₆ * B * volume.real ModularGroup.fd,
    mul_nonneg (mul_nonneg hC₆ hB0) measureReal_nonneg, fun t ht => ?_⟩
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht
  have hsub : averagedTheta k f t - peterssonMass k f =
      ∫ z in ModularGroup.fd, P k f z * (latticeTheta z t - 1) ∂volume := by
    unfold averagedTheta peterssonMass
    rw [← MeasureTheory.integral_sub (integrableOn_P_mul_theta f hk ht0)
      (integrableOn_P_fd f)]
    refine setIntegral_congr_fun measurableSet_fd fun z _ => ?_
    ring
  rw [hsub]
  calc ∫ z in ModularGroup.fd, P k f z * (latticeTheta z t - 1) ∂volume
      ≤ ∫ _z in ModularGroup.fd,
          C₆ * B * Real.exp (-(π * Real.sqrt (3 * t / 2))) ∂volume := by
        refine setIntegral_mono_on (integrableOn_P_mul_tail f hk ht)
          (integrableOn_const volume_fd_lt_top.ne) measurableSet_fd fun z hz => ?_
        calc P k f z * (latticeTheta z t - 1)
            ≤ C₆ * wt C₁ z.im * Real.exp (-(π * Real.sqrt (3 * t / 2))) :=
              hbound z hz t ht
          _ ≤ C₆ * B * Real.exp (-(π * Real.sqrt (3 * t / 2))) := by
              apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
              exact mul_le_mul_of_nonneg_left (hB z.im z.im_pos.le) hC₆
    _ = C₆ * B * volume.real ModularGroup.fd *
          Real.exp (-(π * Real.sqrt (3 * t / 2))) := by
        rw [setIntegral_const, smul_eq_mul]
        ring

/-- The averaged bank is antitone on the positive carrier axis. -/
lemma averagedTheta_antitoneOn (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) :
    AntitoneOn (averagedTheta k f) (Ioi (0 : ℝ)) := by
  intro t₁ ht₁ t₂ _ h
  unfold averagedTheta
  refine setIntegral_mono_on (integrableOn_P_mul_theta f hk (ht₁.trans_le h))
    (integrableOn_P_mul_theta f hk ht₁) measurableSet_fd fun z _ => ?_
  exact mul_le_mul_of_nonneg_left (latticeTheta_anti z ht₁ h) (P_nonneg f z)

/-! ## The packaged weak functional-equation pair -/

/-- The complex-valued averaged theta profile. -/
noncomputable def averagedThetaC (k : ℤ) (f : CuspForm 𝒮ℒ k) (t : ℝ) : ℂ :=
  ((averagedTheta k f t : ℝ) : ℂ)

/-- The averaged profile is locally integrable on the positive axis: it is antitone there. -/
lemma averagedThetaC_locallyIntegrableOn (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) :
    LocallyIntegrableOn (averagedThetaC k f) (Ioi (0 : ℝ)) volume := by
  rw [MeasureTheory.locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed]
  intro K hK hKc
  have hreal : IntegrableOn (averagedTheta k f) K volume :=
    ((averagedTheta_antitoneOn f hk).mono hK).integrableOn_isCompact hKc
  exact hreal.ofReal

/-- **The r = 2 profile pair.**  The averaged lattice bank of a genuine level-one cusp form,
packaged as a Mathlib `WeakFEPair`: weight one, root number one, both constant terms the
Petersson mass, reflection derived from the compiled lattice weld, decay from the compiled saddle
bound.  Mathlib's abstract machinery then returns the entire part, both poles with residues
`±‖f‖²`, the global functional equation, and the Mellin identification on `Re s > 1`. -/
noncomputable def rsAveragedWeakFEPair (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) :
    WeakFEPair ℂ where
  f := averagedThetaC k f
  g := averagedThetaC k f
  k := 1
  ε := 1
  f₀ := ((peterssonMass k f : ℝ) : ℂ)
  g₀ := ((peterssonMass k f : ℝ) : ℂ)
  hf_int := averagedThetaC_locallyIntegrableOn f hk
  hg_int := averagedThetaC_locallyIntegrableOn f hk
  hk := one_pos
  hε := one_ne_zero
  h_feq := fun x hx => by
    have hx0 : (0 : ℝ) < x := hx
    unfold averagedThetaC
    rw [one_div, averagedTheta_inv f hx0, Real.rpow_one]
    push_cast
    ring
  hf_top := fun r => by
    obtain ⟨C, hC0, hC⟩ := averagedTheta_tail_bound f hk
    have h1 : (fun t : ℝ => averagedThetaC k f t - ((peterssonMass k f : ℝ) : ℂ))
        =O[atTop] fun t : ℝ => Real.exp (-(π * Real.sqrt (3 * t / 2))) := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨C, ?_⟩
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      have hnn := peterssonMass_le_averagedTheta f hk (lt_of_lt_of_le one_pos ht)
      have habs : ‖averagedThetaC k f t - ((peterssonMass k f : ℝ) : ℂ)‖ =
          averagedTheta k f t - peterssonMass k f := by
        unfold averagedThetaC
        rw [← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_of_nonneg (by linarith)]
      rw [habs, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact hC t ht
    exact h1.trans ((exp_sqrt_isBigO (-r)).congr_right fun t => by rw [neg_neg])
  hg_top := fun r => by
    obtain ⟨C, hC0, hC⟩ := averagedTheta_tail_bound f hk
    have h1 : (fun t : ℝ => averagedThetaC k f t - ((peterssonMass k f : ℝ) : ℂ))
        =O[atTop] fun t : ℝ => Real.exp (-(π * Real.sqrt (3 * t / 2))) := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨C, ?_⟩
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      have hnn := peterssonMass_le_averagedTheta f hk (lt_of_lt_of_le one_pos ht)
      have habs : ‖averagedThetaC k f t - ((peterssonMass k f : ℝ) : ℂ)‖ =
          averagedTheta k f t - peterssonMass k f := by
        unfold averagedThetaC
        rw [← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_of_nonneg (by linarith)]
      rw [habs, Real.norm_of_nonneg (Real.exp_pos _).le]
      exact hC t ht
    exact h1.trans ((exp_sqrt_isBigO (-r)).congr_right fun t => by rw [neg_neg])

/-! ## The continuation, poles, and functional equation — read off the pair -/

/-- The weight of the packaged second-moment pair is one. -/
@[simp] lemma rsAveragedWeakFEPair_k (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) :
    (rsAveragedWeakFEPair f hk).k = 1 := rfl

/-- The root number of the packaged second-moment pair is one. -/
@[simp] lemma rsAveragedWeakFEPair_ε (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) :
    (rsAveragedWeakFEPair f hk).ε = 1 := rfl

/-- The constant term of the packaged second-moment pair is the Petersson mass. -/
@[simp] lemma rsAveragedWeakFEPair_g₀ (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) :
    (rsAveragedWeakFEPair f hk).g₀ = ((peterssonMass k f : ℝ) : ℂ) := rfl

/-- The entire part of the completed second-moment transform. -/
theorem rsAveraged_entirePart_differentiable (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) :
    Differentiable ℂ (rsAveragedWeakFEPair f hk).Λ₀ :=
  (rsAveragedWeakFEPair f hk).differentiable_Λ₀

/-- **The completed second-moment functional equation**, `Λ(1-s) = Λ(s)`: derived from the
compiled lattice weld through the Petersson average — no candidate consumed. -/
theorem rsAveraged_functional_equation (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) (s : ℂ) :
    (rsAveragedWeakFEPair f hk).Λ (1 - s) = (rsAveragedWeakFEPair f hk).symm.Λ s := by
  have h := (rsAveragedWeakFEPair f hk).functional_equation s
  rw [rsAveragedWeakFEPair_k, rsAveragedWeakFEPair_ε] at h
  simpa using h

/-- **The pole at `s = 1` carries the Petersson mass**: the residue of the completed
second-moment transform at the edge is `‖f‖²` — rank-is-DC-residue at the Rankin–Selberg
level, now at the profile interface. -/
theorem rsAveraged_residue_one (f : CuspForm 𝒮ℒ k) (hk : 0 ≤ k) :
    Tendsto (fun s : ℂ => (s - 1) * (rsAveragedWeakFEPair f hk).Λ s)
      (𝓝[≠] 1) (𝓝 ((peterssonMass k f : ℝ) : ℂ)) := by
  have h := (rsAveragedWeakFEPair f hk).Λ_residue_k
  rw [rsAveragedWeakFEPair_k, rsAveragedWeakFEPair_ε, rsAveragedWeakFEPair_g₀] at h
  simpa using h

end CriticalLinePhasor.Unfolding

#print axioms CriticalLinePhasor.Unfolding.averagedTheta_inv
#print axioms CriticalLinePhasor.Unfolding.averagedTheta_tail_bound
#print axioms CriticalLinePhasor.Unfolding.rsAveragedWeakFEPair
#print axioms CriticalLinePhasor.Unfolding.rsAveraged_entirePart_differentiable
#print axioms CriticalLinePhasor.Unfolding.rsAveraged_functional_equation
#print axioms CriticalLinePhasor.Unfolding.rsAveraged_residue_one
