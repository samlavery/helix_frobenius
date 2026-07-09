import RequestProject.GradedModeDictionary
import RequestProject.XiOrderSummable

/-!
# The differenced resolvent trace: the `T → ∞` limit exists

Stage 1, arrow (2) — the second and final arrow named by the `ResidueJump` audited
frontier: *"the `T → ∞` limit of the resolvent trace requires summability/regularization
(the raw sum `Σ m_ρ/(γ_ρ−w)` diverges; the classical remedies are conjugate pairing or
differencing at two resolvent points)."*  This file supplies the differenced limit,
unconditionally.

Chain:

* the **event set** `Events = {γ > 0 | ζ(½+iγ) = 0}` injects into the nontrivial zero set
  by `γ ↦ ½+iγ` (`line_mem_nontrivialZeros`, `line_injective`);
* the **order bridge** (`eventOrder_eq_xiOrderNat`): at a line point the vanishing order
  of ζ equals the vanishing order of ξ — `ξ = (s(s−1)/2)·Γℝ(s)·ζ(s)` near the point, and
  the non-ζ factor is analytic and nonvanishing there, so orders agree;
* the promoted **counting summability** `ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros`
  (Jensen at `2R` + order-one growth of ξ: `Σ m_ρ/‖ρ‖² < ∞`) then transports to the event
  set by comparison: `Σ_γ m_γ/γ² < ∞` (`summable_eventOrder_div_sq`);
* hence the **differenced resolvent** `Σ'_γ m_γ·((γ−w)⁻¹ − γ⁻¹)` converges absolutely for
  every `w` off the events (`summable_diffResolvent`), and
* the **windowed differenced resolvent trace converges to it as `T → ∞`**
  (`windowedDiffResolvent_tendsto`): the event windows are a monotone cofinal exhaustion,
  so the `HasSum` net restricts to the window filtration.

With `GradedModeDictionary` (arrow 1) this completes Stage 1: the native operator's
graded blocks realize the ledger, and their differenced resolvent trace has an honest
`T → ∞` limit.  Everything is unconditional; no RH/GRH is assumed or proved; the limit
object is a statement about the *sourced* spectrum (the event ledger), and nothing here
asserts where zeros lie.  No `sorry`, no `axiom` beyond the standard three.
-/

open Complex Filter Topology CriticalLinePhasor.ResidueJump CriticalLinePhasor.CarrierScale ZD

namespace CriticalLinePhasor.ResolventLimit

/-! ## §1 The event set and its injection into the nontrivial zero set -/

/-- **The event set**: all positive ordinates where the line readout closes —
`{γ > 0 | ζ(½+iγ) = 0}`. -/
def Events : Set ℝ := {γ : ℝ | 0 < γ ∧ riemannZeta (line γ) = 0}

theorem events_inter_window (T : ℝ) :
    {γ : ℝ | γ ∈ Set.Ioc 0 T ∧ riemannZeta (line γ) = 0}
      = {γ ∈ Events | γ ≤ T} := by
  ext γ
  simp only [Set.mem_setOf_eq, Set.mem_Ioc, Events]
  tauto

/-- Every event's line point is a nontrivial zero (it sits on the line, inside the strip). -/
theorem line_mem_nontrivialZeros {γ : ℝ} (hγ : γ ∈ Events) :
    line γ ∈ ZD.NontrivialZeros := by
  refine ⟨?_, ?_, hγ.2⟩ <;> rw [line_re] <;> norm_num

/-- Events have positive multiplicity. -/
theorem events_order_pos {γ : ℝ} (hγ : γ ∈ Events) : 0 < eventOrder γ :=
  Nat.pos_of_ne_zero fun h0 => (eventOrder_eq_zero_iff γ).mp h0 hγ.2

/-! ## §2 The order bridge: `ord_ζ = ord_ξ` at line points -/

/-- On `Re s > 0` off `s = 1`, ξ agrees with `(s(s−1)/2)·Γℝ(s)·ζ(s)`. -/
theorem riemannXi_eq_unit_mul_zeta {s : ℂ} (hre : 0 < s.re) (hs1 : s ≠ 1) :
    riemannXi s = (s * (s - 1) / 2) * (Gammaℝ s * riemannZeta s) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hre
    exact lt_irrefl 0 hre
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hre
  rw [riemannXi_eq_classical_of_ne_zero_of_ne_one s hs0 hs1,
    riemannZeta_def_of_ne_zero hs0, mul_comm (Gammaℝ s), div_mul_cancel₀ _ hΓ]

/-- The non-ζ factor `u(s) = (s(s−1)/2)·Γℝ(s)` is analytic at every line point.  (Γℝ is
recovered from its entire reciprocal: nonvanishing at the point, so the double inverse is
analytic and `inv_inv` closes.) -/
theorem unitFactor_analyticAt (γ : ℝ) :
    AnalyticAt ℂ (fun s : ℂ => s * (s - 1) / 2 * Gammaℝ s) (line γ) := by
  have hΓinv : AnalyticAt ℂ (fun s : ℂ => (Gammaℝ s)⁻¹) (line γ) :=
    (differentiable_Gammaℝ_inv).analyticAt _
  have hΓne : (Gammaℝ (line γ))⁻¹ ≠ 0 :=
    inv_ne_zero (Gammaℝ_ne_zero_of_re_pos (line_re_pos γ))
  have h2 : AnalyticAt ℂ (fun s : ℂ => ((Gammaℝ s)⁻¹)⁻¹) (line γ) := hΓinv.inv hΓne
  have hfun : (fun s : ℂ => ((Gammaℝ s)⁻¹)⁻¹) = Gammaℝ := funext fun s => inv_inv _
  rw [hfun] at h2
  have hpoly : AnalyticAt ℂ (fun s : ℂ => s * (s - 1) / 2) (line γ) := by
    have hnum : AnalyticAt ℂ (fun s : ℂ => s * (s - 1)) (line γ) :=
      analyticAt_id.mul (analyticAt_id.sub analyticAt_const)
    exact hnum.div analyticAt_const two_ne_zero
  exact hpoly.mul h2

/-- The non-ζ factor is nonvanishing at every line point of positive ordinate. -/
theorem unitFactor_ne_zero {γ : ℝ} (hγ : 0 < γ) :
    line γ * (line γ - 1) / 2 * Gammaℝ (line γ) ≠ 0 := by
  have h0 : line γ ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [line_re, Complex.zero_re] at this
    norm_num at this
  have h1 : line γ - 1 ≠ 0 := sub_ne_zero.mpr (line_ne_one γ)
  exact mul_ne_zero (div_ne_zero (mul_ne_zero h0 h1) two_ne_zero)
    (Gammaℝ_ne_zero_of_re_pos (line_re_pos γ))

/-- **The order bridge**: at any line point of positive ordinate, ζ and ξ vanish to the
same order — the non-ζ factor of ξ is an analytic unit there
(`analyticOrderAt_mul` + `analyticOrderAt_congr`). -/
theorem eventOrder_eq_xiOrderNat (γ : ℝ) (hγ : 0 < γ) :
    eventOrder γ = ZD.xiOrderNat (line γ) := by
  have hopen : {s : ℂ | 0 < s.re ∧ s ≠ 1} ∈ nhds (line γ) := by
    refine IsOpen.mem_nhds ?_ ⟨line_re_pos γ, line_ne_one γ⟩
    exact (isOpen_lt continuous_const Complex.continuous_re).inter isOpen_ne
  have hev : riemannXi =ᶠ[nhds (line γ)]
      fun s => s * (s - 1) / 2 * Gammaℝ s * riemannZeta s := by
    filter_upwards [hopen] with s hs
    rw [riemannXi_eq_unit_mul_zeta hs.1 hs.2, mul_assoc]
  have horder : analyticOrderAt riemannXi (line γ)
      = analyticOrderAt riemannZeta (line γ) := by
    rw [analyticOrderAt_congr hev]
    show analyticOrderAt
      ((fun s : ℂ => s * (s - 1) / 2 * Gammaℝ s) * riemannZeta) (line γ) = _
    rw [analyticOrderAt_mul (unitFactor_analyticAt γ) (zeta_analyticAt_line γ),
      (unitFactor_analyticAt γ).analyticOrderAt_eq_zero.mpr (unitFactor_ne_zero hγ),
      zero_add]
  show analyticOrderNatAt riemannZeta (line γ) = analyticOrderNatAt riemannXi (line γ)
  unfold analyticOrderNatAt
  exact congrArg ENat.toNat horder.symm

/-! ## §3 Summability over the event set -/

/-- The squared norm of a line point: `‖½+iγ‖² = ¼ + γ²`. -/
theorem normSq_line (γ : ℝ) : ‖line γ‖ ^ 2 = 1 / 4 + γ ^ 2 := by
  have h2 : (line γ).im = γ := by
    simp [line, lineC]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, line_re, h2]
  ring

/-- The injection of events into the nontrivial-zero subtype. -/
noncomputable def toZero (γ : Events) : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} :=
  ⟨line γ.val, line_mem_nontrivialZeros γ.2⟩

theorem toZero_injective : Function.Injective toZero := by
  intro a b hab
  exact Subtype.ext (line_injective (congrArg Subtype.val hab))

/-- The base comparison family, pulled back to the event set along `toZero`. -/
theorem summable_base :
    Summable (fun γ : Events =>
      (ZD.xiOrderNat (line γ.val) : ℝ) / ‖line γ.val‖ ^ 2) := by
  have h := ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros.comp_injective
    toZero_injective
  exact h.congr fun γ => rfl

/-- **The transported counting bound**: `Σ_γ m_γ/γ² < ∞` over the event set — the promoted
Jensen/order-one summability (`ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros`),
pulled back along `γ ↦ ½+iγ` through the order bridge, with the finitely many events of
height `≤ 1` handled cofinitely. -/
theorem summable_eventOrder_div_sq :
    Summable (fun γ : Events => (eventOrder γ.val : ℝ) / γ.val ^ 2) := by
  refine Summable.of_norm_bounded_eventually (summable_base.mul_left 2) ?_
  have hfin : {γ : Events | γ.val ≤ 1}.Finite := by
    have hf : {γ' : ℝ | γ' ∈ Set.Ioc 0 1 ∧ riemannZeta (line γ') = 0}.Finite :=
      events_finite 1
    refine Set.Finite.of_finite_image (hf.subset ?_) Subtype.val_injective.injOn
    rintro x ⟨γsub, hγle, rfl⟩
    exact ⟨⟨γsub.2.1, hγle⟩, γsub.2.2⟩
  refine Filter.mem_of_superset hfin.compl_mem_cofinite ?_
  intro γ hγ
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hγ
  have hγpos : (0 : ℝ) < γ.val := lt_trans one_pos hγ
  have hord : eventOrder γ.val = ZD.xiOrderNat (line γ.val) :=
    eventOrder_eq_xiOrderNat γ.val γ.2.1
  have hnn : (0 : ℝ) ≤ (eventOrder γ.val : ℝ) / γ.val ^ 2 := by positivity
  simp only [Set.mem_setOf_eq]
  rw [Real.norm_of_nonneg hnn, hord, normSq_line, ← mul_div_assoc]
  have hγsq : (1 : ℝ) ≤ γ.val ^ 2 := one_le_pow₀ hγ.le
  have hm : (0 : ℝ) ≤ (ZD.xiOrderNat (line γ.val) : ℝ) := Nat.cast_nonneg _
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hm (by linarith : (0 : ℝ) ≤ γ.val ^ 2 - 1)]

/-! ## §4 The differenced resolvent -/

/-- Events of height at most `c` form a finite set (pullback of `events_finite`). -/
theorem events_le_finite (c : ℝ) : {γ : Events | γ.val ≤ c}.Finite := by
  have hf : {γ' : ℝ | γ' ∈ Set.Ioc 0 c ∧ riemannZeta (line γ') = 0}.Finite :=
    events_finite c
  refine Set.Finite.of_finite_image (hf.subset ?_) Subtype.val_injective.injOn
  rintro x ⟨γsub, hγle, rfl⟩
  exact ⟨⟨γsub.2.1, hγle⟩, γsub.2.2⟩

/-- The differenced resolvent term at an event: `m_γ·((γ−w)⁻¹ − γ⁻¹)` — the frontier's
"differencing at two resolvent points", taken at `w` and `0`. -/
noncomputable def diffTerm (w : ℂ) (γ : ℝ) : ℂ :=
  (eventOrder γ : ℂ) * (((γ : ℂ) - w)⁻¹ - (γ : ℂ)⁻¹)

/-- The two-point difference collapses to `w/((γ−w)γ)`. -/
theorem inv_sub_inv_eq {w : ℂ} {γ : ℝ} (hγ : (γ : ℂ) ≠ 0) (hw : (γ : ℂ) - w ≠ 0) :
    ((γ : ℂ) - w)⁻¹ - (γ : ℂ)⁻¹ = w * (((γ : ℂ) - w)⁻¹ * (γ : ℂ)⁻¹) := by
  field_simp
  ring

/-- Termwise bound: for `γ ≥ 1` and `γ ≥ 2‖w‖`, `‖diffTerm w γ‖ ≤ 2‖w‖·(m_γ/γ²)`. -/
theorem diffTerm_bound {w : ℂ} {γ : ℝ} (hγ1 : 1 ≤ γ) (hγw : 2 * ‖w‖ ≤ γ) :
    ‖diffTerm w γ‖ ≤ 2 * ‖w‖ * ((eventOrder γ : ℝ) / γ ^ 2) := by
  have hγpos : (0 : ℝ) < γ := lt_of_lt_of_le one_pos hγ1
  have hγC : (γ : ℂ) ≠ 0 := by exact_mod_cast hγpos.ne'
  have hdist : γ / 2 ≤ ‖(γ : ℂ) - w‖ := by
    have h1 : ‖(γ : ℂ)‖ - ‖w‖ ≤ ‖(γ : ℂ) - w‖ := norm_sub_norm_le _ _
    have h2 : ‖(γ : ℂ)‖ = γ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hγpos.le]
    nlinarith [h1, h2]
  have hwne : (γ : ℂ) - w ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdist
    nlinarith
  rw [diffTerm, inv_sub_inv_eq hγC hwne, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv]
  have hmnorm : ‖((eventOrder γ : ℕ) : ℂ)‖ = (eventOrder γ : ℝ) := by
    rw [Complex.norm_natCast]
  rw [hmnorm]
  have hγnorm : ‖(γ : ℂ)‖ = γ := by
    rw [Complex.norm_real, Real.norm_of_nonneg hγpos.le]
  rw [hγnorm]
  have hbound : ‖(γ : ℂ) - w‖⁻¹ ≤ (γ / 2)⁻¹ := by
    gcongr
  calc (eventOrder γ : ℝ) * (‖w‖ * (‖(γ : ℂ) - w‖⁻¹ * γ⁻¹))
      ≤ (eventOrder γ : ℝ) * (‖w‖ * ((γ / 2)⁻¹ * γ⁻¹)) := by
        gcongr
      _ = 2 * ‖w‖ * ((eventOrder γ : ℝ) / γ ^ 2) := by
        field_simp

/-- **Absolute convergence of the differenced resolvent** over the event set, for every
resolvent point `w`. -/
theorem summable_diffTerm (w : ℂ) :
    Summable (fun γ : Events => diffTerm w γ.val) := by
  refine Summable.of_norm_bounded_eventually
    ((summable_eventOrder_div_sq.mul_left (2 * ‖w‖))) ?_
  refine Filter.mem_of_superset ((events_le_finite (max 1 (2 * ‖w‖))).compl_mem_cofinite) ?_
  intro γ hγ
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, max_lt_iff] at hγ
  exact diffTerm_bound hγ.1.le hγ.2.le

/-- **The differenced resolvent**: `R(w) = Σ'_γ m_γ·((γ−w)⁻¹ − γ⁻¹)` — the `T → ∞` object. -/
noncomputable def diffResolvent (w : ℂ) : ℂ :=
  ∑' γ : Events, diffTerm w γ.val

/-! ## §5 The `T → ∞` limit of the windowed trace -/

/-- Window members are events. -/
theorem mem_events_of_mem_window {T γ : ℝ} (hγ : γ ∈ eventWindow T) : γ ∈ Events := by
  have h := (events_finite T).mem_toFinset.mp hγ
  exact ⟨h.1.1, h.2⟩

/-- The event window as a `Finset` of the event subtype. -/
noncomputable def windowSub (T : ℝ) : Finset Events :=
  (eventWindow T).attach.map
    ⟨fun x => ⟨x.val, mem_events_of_mem_window x.2⟩,
      fun a b hab => Subtype.ext (Subtype.mk_eq_mk.mp hab)⟩

theorem mem_windowSub {T : ℝ} {γ : Events} :
    γ ∈ windowSub T ↔ γ.val ∈ eventWindow T := by
  constructor
  · rintro h
    simp only [windowSub, Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk,
      true_and] at h
    obtain ⟨x, hx⟩ := h
    rw [← hx]
    exact x.2
  · intro h
    simp only [windowSub, Finset.mem_map, Finset.mem_attach, Function.Embedding.coeFn_mk,
      true_and]
    exact ⟨⟨γ.val, h⟩, Subtype.ext rfl⟩

/-- Sums over the window subtype agree with sums over the window. -/
theorem sum_windowSub (T : ℝ) (f : ℝ → ℂ) :
    ∑ γ ∈ windowSub T, f γ.val = ∑ γ ∈ eventWindow T, f γ := by
  rw [windowSub, Finset.sum_map]
  exact Finset.sum_attach _ _

/-- The windows exhaust the event set monotonically and cofinally. -/
theorem windowSub_tendsto : Filter.Tendsto windowSub Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop_finset_of_monotone ?_ ?_
  · intro T T' hTT' γ hγ
    rw [mem_windowSub] at hγ ⊢
    have h := (events_finite T).mem_toFinset.mp hγ
    exact (events_finite T').mem_toFinset.mpr ⟨⟨h.1.1, le_trans h.1.2 hTT'⟩, h.2⟩
  · intro γ
    refine ⟨γ.val, ?_⟩
    rw [mem_windowSub]
    exact (events_finite γ.val).mem_toFinset.mpr ⟨⟨γ.2.1, le_refl _⟩, γ.2.2⟩

/-- **Stage 1, arrow (2) — the `T → ∞` limit of the differenced resolvent trace exists**:

    `Tr_T [(D−w)⁻¹ − D⁻¹] = Σ_{γ ≤ T} m_γ·((γ−w)⁻¹ − γ⁻¹)  ⟶  R(w)`.

The windowed trace at the differenced resolvent observable converges to the absolutely
convergent ledger sum — the audited frontier's second arrow, discharged by the promoted
counting bound.  Unconditional. -/
theorem windowedDiffResolvent_tendsto (w : ℂ) :
    Filter.Tendsto
      (fun T => windowedTrace (fun γ => ((γ : ℂ) - w)⁻¹ - (γ : ℂ)⁻¹) T)
      Filter.atTop (nhds (diffResolvent w)) := by
  have hsum : HasSum (fun γ : Events => diffTerm w γ.val) (diffResolvent w) :=
    (summable_diffTerm w).hasSum
  have hcomp := hsum.comp windowSub_tendsto
  refine hcomp.congr fun T => ?_
  show (∑ γ ∈ windowSub T, diffTerm w γ.val) = _
  rw [sum_windowSub T (fun t => diffTerm w t)]
  rfl

/-- The differenced trace is the difference of two windowed resolvent traces — the
"two resolvent points" are `w` and `0`. -/
theorem windowedDiffResolvent_eq (w : ℂ) (T : ℝ) :
    windowedTrace (fun γ => ((γ : ℂ) - w)⁻¹ - (γ : ℂ)⁻¹) T
      = windowedResolventTrace w T - windowedResolventTrace 0 T := by
  unfold windowedResolventTrace windowedTrace
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun γ _ => ?_
  simp only [sub_zero]
  ring

end CriticalLinePhasor.ResolventLimit
