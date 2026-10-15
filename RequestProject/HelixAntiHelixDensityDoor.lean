import RequestProject.HelixAntiHelixFamily
import RequestProject.HelixHalfLineSource
import RequestProject.HelixSourceEndSwap

/-!
# The density door, closed on the anti-helix family (ledger 1317)

1283's `no_source_of_dense`: a drifted source (`Re v > 0`) is excluded by any dense family below the origin that
its functional annihilates. 1316 built the family on the helix side and proved the annihilation. Here the family
is placed in the native half-line space `L²(h ≤ 0, dh)` and paired with the source's functional:

* `siteFn k h = e^{h/4} · siteFun k (e^{−h/2})` on `h ≤ 0` (the anti-helix coordinate `u = e^{−h/2} ≥ 1`);
  `memLp_siteFn`, `fk k : Lp ℂ 2 below`.
* `inner_ψ_site`: `⟪ψ_v, fk k⟫ = 2 · mellinSite k (½ + 2v)` — the substitution `h = −2 log u`.
* `inner_ψ_site_zero_of_source`: a drifted cancellation at offset `v` is orthogonal to every `fk k`.
* `no_drifted_source_of_dense`: if the span of the family is dense, no drifted evaluation cancels.
* `zeros_on_line_of_antiHelix_density`: density of the family ⟹ every nontrivial zero has `Re = ½`.

What is left is the density itself, Báez-Duarte's form of Nyman–Beurling (ledger 003 measured its Gram distances).
-/

open Complex MeasureTheory Set Filter
open scoped ComplexConjugate InnerProductSpace

noncomputable section

namespace CriticalLinePhasor.AntiHelixDensityDoor

open CriticalLinePhasor.AntiHelixFamily CriticalLinePhasor.HelixHalfLineSource CriticalLinePhasor.HelixNativeDilation
open CriticalLinePhasor.HelixZetaSource CriticalLinePhasor.HelixSourceEndSwap GRH.EulerMaclaurinDirichlet

/-- The site function in the anti-helix coordinate: `e^{h/4} · siteFun k (e^{−h/2})`. -/
def siteFn (k : ℕ) (h : ℝ) : ℂ := ((Real.exp (h / 4) * siteFun k (Real.exp (-h / 2)) : ℝ) : ℂ)

theorem siteFun_abs_le {k : ℕ} (hk : 1 ≤ k) (u : ℝ) : |siteFun k u| ≤ 2 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  unfold siteFun
  calc |fract (u / k) - fract u / k| ≤ |fract (u / k)| + |fract u / k| := abs_sub _ _
    _ ≤ 1 + 1 := by
        refine add_le_add (fract_abs_le _) ?_
        rw [abs_div, abs_of_pos hkpos, div_le_one hkpos]
        exact (fract_abs_le u).trans hk1
    _ = 2 := by norm_num

theorem measurable_siteFn (k : ℕ) : Measurable (siteFn k) := by
  unfold siteFn
  refine Complex.measurable_ofReal.comp (Measurable.mul ?_ ?_)
  · exact Real.continuous_exp.measurable.comp (measurable_id.div_const _)
  · exact (AntiHelixFamily.measurable_fract.comp ((measurable_id.neg.div_const _).exp.div_const _)).sub
      ((AntiHelixFamily.measurable_fract.comp (measurable_id.neg.div_const _).exp).div_const _)

/-- **The site function is square-integrable below the origin.** -/
theorem memLp_siteFn {k : ℕ} (hk : 1 ≤ k) : MemLp (siteFn k) 2 below := by
  rw [memLp_two_iff_integrable_sq_norm (measurable_siteFn k).aestronglyMeasurable]
  have hg : IntegrableOn (fun h : ℝ => 4 * Real.exp ((1 / 2 : ℝ) * h)) (Iic 0) :=
    (integrableOn_exp_mul_Iic (a := 1 / 2) (by norm_num) 0).const_mul 4
  refine hg.integrable.mono' ((measurable_siteFn k).norm.pow_const 2).aestronglyMeasurable ?_
  refine Eventually.of_forall fun h => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  unfold siteFn
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_pow]
  have h1 : |siteFun k (Real.exp (-h / 2))| ^ 2 ≤ 2 ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) (siteFun_abs_le hk _) 2
  have h2 : Real.exp (h / 4) ^ 2 = Real.exp ((1 / 2 : ℝ) * h) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h2]
  nlinarith [Real.exp_pos ((1 / 2 : ℝ) * h)]

/-- The family member as an element of the native half-line space. -/
def fk (k : ℕ) (hk : 1 ≤ k) : Lp ℂ 2 below := (memLp_siteFn hk).toLp _

/-- The pointwise form of the substituted integrand on `u > 1`. -/
theorem substituted_integrand (v : ℂ) (k : ℕ) {u : ℝ} (hu : 1 < u) :
    (u⁻¹ : ℝ) • (expMode v (-2 * Real.log u) * siteFn k (-2 * Real.log u)) =
      (siteFun k u : ℂ) * (u : ℂ) ^ (-((1 / 2 + 2 * v) + 1)) := by
  have hu0 : 0 < u := lt_trans one_pos hu
  have huc : (u : ℂ) ≠ 0 := by exact_mod_cast hu0.ne'
  have hexp1 : expMode v (-2 * Real.log u) = (u : ℂ) ^ (-2 * v) := by
    unfold expMode
    rw [Complex.cpow_def_of_ne_zero huc, ← Complex.ofReal_log hu0.le]
    congr 1; push_cast; ring
  have hexp2 : Real.exp (-2 * Real.log u / 4) = u ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_def_of_pos hu0]; congr 1; ring
  have hexp3 : Real.exp (-(-2 * Real.log u) / 2) = u := by
    rw [show -(-2 * Real.log u) / 2 = Real.log u by ring, Real.exp_log hu0]
  unfold siteFn
  rw [hexp2, hexp3, hexp1, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_cpow hu0.le,
    Complex.ofReal_inv]
  rw [show ((u : ℂ))⁻¹ = (u : ℂ) ^ (-1 : ℂ) by rw [Complex.cpow_neg_one]]
  rw [show -((1 / 2 + 2 * v) + 1) = (-1 : ℂ) + ((-2 * v) + (-(1 / 2 : ℂ))) by ring,
    Complex.cpow_add _ _ huc, Complex.cpow_add _ _ huc]
  push_cast
  ring

/-- **The source's functional on a family member is the site transform at its readout**:
`⟪ψ_v, fk k⟫ = 2 · mellinSite k (½ + 2v)`. -/
theorem inner_ψ_site {v : ℂ} (hv : 0 < v.re) {k : ℕ} (hk : 1 ≤ k) :
    ⟪ψ v hv, fk k hk⟫_ℂ = 2 * mellinSite k (1 / 2 + 2 * v) := by
  rw [inner_ψ hv]
  have hcoe : ∫ h in Iic (0 : ℝ), expMode v h * (fk k hk) h = ∫ h in Iic (0 : ℝ), expMode v h * siteFn k h := by
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_siteFn hk)] with h hh
    rw [show (fk k hk) h = ((memLp_siteFn hk).toLp _) h from rfl, hh]
  -- h ↦ −x : Iic 0 ← Ioi 0
  have hstep1 : ∫ h in Iic (0 : ℝ), expMode v h * siteFn k h =
      ∫ x in Ioi (0 : ℝ), expMode v (-x) * siteFn k (-x) := by
    have h := integral_comp_neg_Ioi (0 : ℝ) (fun h : ℝ => expMode v h * siteFn k h)
    rw [neg_zero] at h
    exact h.symm
  -- x = 2y
  have hstep2 : ∫ x in Ioi (0 : ℝ), expMode v (-x) * siteFn k (-x) =
      2 * ∫ y in Ioi (0 : ℝ), expMode v (-(2 * y)) * siteFn k (-(2 * y)) := by
    have h := integral_comp_mul_left_Ioi (fun x : ℝ => expMode v (-x) * siteFn k (-x)) 0 (b := 2)
      (by norm_num)
    simp only [mul_zero] at h
    rw [h, Complex.real_smul]
    push_cast
    ring
  -- y = log u
  have hstep3 : ∫ y in Ioi (0 : ℝ), expMode v (-(2 * y)) * siteFn k (-(2 * y)) =
      ∫ u in Ioi (1 : ℝ), (u⁻¹ : ℝ) • (expMode v (-(2 * Real.log u)) * siteFn k (-(2 * Real.log u))) := by
    have h := integral_comp_log_Ioi (fun y : ℝ => expMode v (-(2 * y)) * siteFn k (-(2 * y)))
      (a := (1 : ℝ)) one_pos
    rw [Real.log_one] at h
    exact h.symm
  -- the substituted integrand is the site transform's
  have hstep4 : ∫ u in Ioi (1 : ℝ), (u⁻¹ : ℝ) • (expMode v (-(2 * Real.log u)) * siteFn k (-(2 * Real.log u))) =
      mellinSite k (1 / 2 + 2 * v) := by
    unfold mellinSite
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have h := substituted_integrand v k (hu : 1 < u)
    rw [show -(2 * Real.log u) = -2 * Real.log u by ring]
    exact h
  rw [hcoe, hstep1, hstep2, hstep3, hstep4]

/-- **A drifted cancellation is orthogonal to every family member.** -/
theorem inner_ψ_site_zero_of_source {v : ℂ} (hv : 0 < v.re) (hv' : v.re < 1 / 4) (Z hc : ℝ)
    (hcancel : (sourceConfig v Z hc).Cancels) {k : ℕ} (hk : 1 ≤ k) : ⟪ψ v hv, fk k hk⟫_ℂ = 0 := by
  rw [inner_ψ_site hv hk, site_annihilated_of_source (by rw [abs_lt]; constructor <;> linarith) Z hc hcancel hk,
    mul_zero]

/-- The family's span in the native half-line space. -/
def familySpan : Submodule ℂ (Lp ℂ 2 below) :=
  Submodule.span ℂ (Set.range fun k : ℕ => fk (k + 1) (Nat.le_add_left 1 k))

/-- **Density of the family excludes every drifted cancellation** (1283's door, consumed by this family). -/
theorem no_drifted_source_of_dense (hdense : familySpan.topologicalClosure = ⊤) {v : ℂ} (hv : 0 < v.re)
    (hv' : v.re < 1 / 4) (Z hc : ℝ) : ¬ (sourceConfig v Z hc).Cancels := by
  intro hcancel
  refine no_source_of_dense hv familySpan hdense fun f hf => ?_
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact inner_ψ_site_zero_of_source hv hv' Z hc hcancel _
  | zero => exact inner_zero_right _
  | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  | smul a x _ hx => rw [inner_smul_right, hx, mul_zero]

/-- **Density of the anti-helix family puts every nontrivial zero on the line.** -/
theorem zeros_on_line_of_antiHelix_density (hdense : familySpan.topologicalClosure = ⊤) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 := by
  intro ρ hρ
  by_contra hne
  have hcancel := (every_zero_has_source hρ 0).1
  have hre := source_offset_re ρ
  have hband := zero_offset_band hρ
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- Re ρ < ½: the J-partner source has positive drift
    have hre' : (-conj (ρ / 2 - 1 / 4)).re = -(ρ / 2 - 1 / 4).re := by
      rw [Complex.neg_re, Complex.conj_re]
    have hpos : 0 < (-conj (ρ / 2 - 1 / 4)).re := by rw [hre', hre]; linarith
    have hlt' : (-conj (ρ / 2 - 1 / 4)).re < 1 / 4 := by
      rw [hre', hre]; linarith [hρ.1]
    have hcancel' : (sourceConfig (-conj (ρ / 2 - 1 / 4)) (Real.exp ρ.im) (-0)).Cancels :=
      (partnerSource_cancels_iff _ _ _).mpr hcancel
    exact no_drifted_source_of_dense hdense hpos hlt' _ _ hcancel'
  · -- Re ρ > ½: the source itself has positive drift
    have hpos : 0 < (ρ / 2 - 1 / 4).re := by rw [hre]; linarith
    have hlt' : (ρ / 2 - 1 / 4).re < 1 / 4 := by rw [hre]; linarith [hρ.2.1]
    exact no_drifted_source_of_dense hdense hpos hlt' _ _ hcancel

/-! ## The sharper door: the native constant in the closure suffices (Báez-Duarte's form)

Full density is more than the door needs. The native constant `g₀ = e^{h/4}` on `h ≤ 0` — the cell position at the
origin site — pairs with every drifted source to `1/(v + ¼) ≠ 0`. So it is enough that `g₀` lie in the CLOSURE of
the family's span: that is Báez-Duarte's form of the Nyman–Beurling criterion, read natively. -/

/-- The native constant below the origin: `e^{h/4}`, i.e. the mode `expMode (1/4)`. -/
def g0 : Lp ℂ 2 below := (memLp_expMode (v := (1 / 4 : ℂ)) (by norm_num)).toLp _

/-- **The source's functional on the native constant is `1/(v + ¼)`**, never zero. -/
theorem inner_ψ_g0 {v : ℂ} (hv : 0 < v.re) : ⟪ψ v hv, g0⟫_ℂ = 1 / (v + 1 / 4) := by
  rw [inner_ψ hv]
  have hcoe : ∫ h in Iic (0 : ℝ), expMode v h * g0 h =
      ∫ h in Iic (0 : ℝ), Complex.exp ((v + 1 / 4) * h) := by
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (memLp_expMode (v := (1 / 4 : ℂ)) (by norm_num))] with h hh
    rw [show g0 h = ((memLp_expMode (v := (1 / 4 : ℂ)) (by norm_num)).toLp _) h from rfl, hh]
    unfold expMode
    rw [← Complex.exp_add]
    congr 1; ring
  have hre : 0 < (v + 1 / 4 : ℂ).re := by simp; linarith
  rw [hcoe, integral_exp_mul_complex_Iic hre 0]
  simp

/-- **The native constant in the closure of the family excludes every drifted cancellation.** -/
theorem no_drifted_source_of_g0_mem (h0 : g0 ∈ familySpan.topologicalClosure) {v : ℂ} (hv : 0 < v.re)
    (hv' : v.re < 1 / 4) (Z hc : ℝ) : ¬ (sourceConfig v Z hc).Cancels := by
  intro hcancel
  have hann : ∀ f ∈ familySpan, ⟪ψ v hv, f⟫_ℂ = 0 := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      exact inner_ψ_site_zero_of_source hv hv' Z hc hcancel _
    | zero => exact inner_zero_right _
    | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
    | smul a x _ hx => rw [inner_smul_right, hx, mul_zero]
  have hle : familySpan ≤ LinearMap.ker (innerSL ℂ (ψ v hv)).toLinearMap := by
    intro f hf
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply]
    exact hann f hf
  have hclos := Submodule.topologicalClosure_minimal familySpan hle
    (ContinuousLinearMap.isClosed_ker (innerSL ℂ (ψ v hv)))
  have h0' := hclos h0
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, innerSL_apply_apply, inner_ψ_g0 hv] at h0'
  have hne : (v + 1 / 4 : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  exact (one_div_ne_zero hne) h0'

/-- **Báez-Duarte's form, natively: the native constant in the closure of the anti-helix family puts every
nontrivial zero on the line.** -/
theorem zeros_on_line_of_g0_mem (h0 : g0 ∈ familySpan.topologicalClosure) :
    ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 := by
  intro ρ hρ
  by_contra hne
  have hcancel := (every_zero_has_source hρ 0).1
  have hre := source_offset_re ρ
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hre' : (-conj (ρ / 2 - 1 / 4)).re = -(ρ / 2 - 1 / 4).re := by
      rw [Complex.neg_re, Complex.conj_re]
    have hpos : 0 < (-conj (ρ / 2 - 1 / 4)).re := by rw [hre', hre]; linarith
    have hlt' : (-conj (ρ / 2 - 1 / 4)).re < 1 / 4 := by
      rw [hre', hre]; linarith [hρ.1]
    have hcancel' : (sourceConfig (-conj (ρ / 2 - 1 / 4)) (Real.exp ρ.im) (-0)).Cancels :=
      (partnerSource_cancels_iff _ _ _).mpr hcancel
    exact no_drifted_source_of_g0_mem h0 hpos hlt' _ _ hcancel'
  · have hpos : 0 < (ρ / 2 - 1 / 4).re := by rw [hre]; linarith
    have hlt' : (ρ / 2 - 1 / 4).re < 1 / 4 := by rw [hre]; linarith [hρ.2.1]
    exact no_drifted_source_of_g0_mem h0 hpos hlt' _ _ hcancel

end CriticalLinePhasor.AntiHelixDensityDoor

end

#print axioms CriticalLinePhasor.AntiHelixDensityDoor.inner_ψ_g0
#print axioms CriticalLinePhasor.AntiHelixDensityDoor.zeros_on_line_of_g0_mem

#print axioms CriticalLinePhasor.AntiHelixDensityDoor.inner_ψ_site
#print axioms CriticalLinePhasor.AntiHelixDensityDoor.no_drifted_source_of_dense
#print axioms CriticalLinePhasor.AntiHelixDensityDoor.zeros_on_line_of_antiHelix_density
