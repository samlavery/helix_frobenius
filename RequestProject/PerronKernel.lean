import Mathlib
import RequestProject.PerronReduction

/-!
# The Perron kernel — the effective step-function approximation, both regimes

Toward the Perron/Tauberian step of the functoriality cancellation, this file develops the
effective Perron kernel `K(c,T,y) = (1/2π)∫_{-T}^{T} y^{c+it}/(c+it) dt` and proves, **both
unconditionally at the standard axiom footprint**, that it approximates the step function `[y > 1]`
with an explicit error:

* `perron_kernel_bound`    (`y > 1`):  `‖K(c,T,y) − 1‖ ≤ y^c/(πT·log y)`;
* `perron_kernel_bound_lt` (`y < 1`):  `‖K(c,T,y)‖     ≤ y^c/(πT·(−log y))`.

The engine is the residue theorem for the simple pole of `y^s/s` at `s = 0` (residue `1`) inside a
Perron rectangle:

* `perron_horizontal_bound` / `perron_horizontal_bound_lt` — the horizontal-leg estimates
  `‖∫ y^{x+ih}/(x+ih) dx‖ ≤ y^c/(|h|·|log y|)` (`y > 1` shifts left, `y < 1` shifts right);
* `perron_vertical_bound` — the vertical-leg estimate `‖∫ y^{s+iv}/(s+iv) dv‖ ≤ y^s·2T/|s|`;
* `perron_rect_residue` — `∮ y^s/s = 2πi` with the pole enclosed (via the removable singularity of
  `(y^s−1)/s`), and `perron_rect_holo` — `∮ y^s/s = 0` with the pole outside (Cauchy–Goursat).

Both kernel bounds follow by a `U → ∞` squeeze: the far vertical leg vanishes.

**Scope (honest).**  This is the effective *kernel* — the per-term Perron approximation
`K(c,T,x/n) ≈ [n < x]`, the analytic core of the Perron side.  It does not by itself assemble the
named `PerronTauberian` hypothesis of `FunctorialityCancellation`, but the two inputs that assembly
would consume are **already in the tree**, not external — in particular there is no Deligne/convexity
dependency:

* **The `∑`/`∫` interchange is compiled.**  `∫_{-T}^{T} ∑ₙ aₙ(x/n)^{c+it}/(c+it) dt =
  ∑ₙ aₙ ∫_{-T}^{T} (x/n)^{c+it}/(c+it) dt` is the coefficient-bank Fubini already used in-tree
  (`integral_tsum_of_summable_integral_norm`, cf. `CarrierThetaIdentification`; `StripFubini`,
  `RSSwap`); on the truncated contour the summand-norm series is finite.
* **The vertical-strip growth bound is carrier-compiled**, not a convexity/Deligne input:
  `CarrierMellinContinuation.strongFEPair_boundedOn_verticalStrip` bounds the completed transform on
  every closed vertical strip directly from the theta reflection (bundled into the niceness the
  cancellation rides on — `zeroConstants_twistedNiceness`, `cpsDualPair_twistedNiceness`).  The 1-D
  "convergence abscissa / critical strip" is itself a projection-chart artifact with no 3-D
  counterpart (`CarrierScaleCompensation`) — a chart gate, never an obstruction on the carrier.

What remains is therefore mechanical: the effective truncated-Perron error balancing `T = T(x)` that
sums the kernel errors above (including the near-diagonal `n ≈ x` terms) into the `O(x^θ)` bound — a
formalization-effort step over compiled 3-D inputs, with no RH/GRH and no cited deep theorem.
-/

open Complex MeasureTheory intervalIntegral Set Filter Topology Asymptotics
open CriticalLinePhasor.ContourArgument
open scoped Real

namespace CriticalLinePhasor.Perron

/-- `fun x => y^x` is continuous for `y > 0`. -/
private theorem continuous_rpow_base {y : ℝ} (hy : 0 < y) : Continuous fun x : ℝ => y ^ x := by
  have : (fun x : ℝ => y ^ x) = fun x => Real.exp (Real.log y * x) :=
    funext fun x => Real.rpow_def_of_pos hy x
  rw [this]; fun_prop

/-- The real exponential antiderivative: `∫_a^c y^x dx = (y^c - y^a)/log y` for `y > 0`, `log y ≠ 0`. -/
private theorem integral_rpow_base {y : ℝ} (hy0 : 0 < y) (hL : Real.log y ≠ 0) (a c : ℝ) :
    ∫ x in a..c, y ^ x = (y ^ c - y ^ a) / Real.log y := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun t => y ^ t / Real.log y) (y ^ x) x := by
    intro x
    have he : HasDerivAt (fun t : ℝ => Real.exp (Real.log y * t))
        (Real.exp (Real.log y * x) * Real.log y) x := by
      simpa using ((hasDerivAt_id x).const_mul (Real.log y)).exp
    rw [show (fun t : ℝ => Real.exp (Real.log y * t)) = fun t => y ^ t from
        funext fun t => (Real.rpow_def_of_pos hy0 t).symm,
      show Real.exp (Real.log y * x) = y ^ x from (Real.rpow_def_of_pos hy0 x).symm] at he
    have := he.div_const (Real.log y)
    rwa [mul_div_assoc, div_self hL, mul_one] at this
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
    ((continuous_rpow_base hy0).intervalIntegrable a c)]
  ring

/-- **Horizontal-leg estimate for the Perron rectangle.**  For `y > 1`, height `h ≠ 0`, and any
`a ≤ c`, the horizontal segment of `y^s/s` at height `h` is bounded by `y^c/(|h|·log y)`.  The
numerator norm is `‖y^{x+ih}‖ = y^x`, the denominator norm is `‖x+ih‖ ≥ |h|`, and
`∫_a^c y^x dx ≤ y^c/log y`. -/
theorem perron_horizontal_bound {y : ℝ} (hy : 1 < y) {h : ℝ} (hh : h ≠ 0) {a c : ℝ} (hac : a ≤ c) :
    ‖∫ x in a..c, (y : ℂ) ^ ((x : ℂ) + (h : ℂ) * I) / ((x : ℂ) + (h : ℂ) * I)‖
      ≤ y ^ c / (|h| * Real.log y) := by
  have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
  have hLpos : 0 < Real.log y := Real.log_pos hy
  have hhabs : (0 : ℝ) < |h| := abs_pos.mpr hh
  have hne : ∀ x : ℝ, (x : ℂ) + (h : ℂ) * I ≠ 0 := by
    intro x hx
    have := congrArg Complex.im hx
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.ofReal_re,
      Complex.I_re, mul_zero, mul_one, zero_add, add_zero, Complex.zero_im] at this
    exact hh this
  have hden : ∀ x : ℝ, |h| ≤ ‖(x : ℂ) + (h : ℂ) * I‖ := by
    intro x
    calc |h| = |((x : ℂ) + (h : ℂ) * I).im| := by simp
      _ ≤ ‖(x : ℂ) + (h : ℂ) * I‖ := Complex.abs_im_le_norm _
  have hpt : ∀ x ∈ Set.Icc a c,
      ‖(y : ℂ) ^ ((x : ℂ) + (h : ℂ) * I) / ((x : ℂ) + (h : ℂ) * I)‖ ≤ y ^ x / |h| := by
    intro x _
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0,
      show ((x : ℂ) + (h : ℂ) * I).re = x by simp]
    have hznn : (0 : ℝ) < ‖(x : ℂ) + (h : ℂ) * I‖ := lt_of_lt_of_le hhabs (hden x)
    gcongr
    exact hden x
  have hcont : Continuous fun x : ℝ =>
      (y : ℂ) ^ ((x : ℂ) + (h : ℂ) * I) / ((x : ℂ) + (h : ℂ) * I) := by
    apply Continuous.div
    · exact (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + (h : ℂ) * I).const_cpow
        (Or.inl (by exact_mod_cast hy0.ne'))
    · fun_prop
    · exact hne
  have hint : IntervalIntegrable
      (fun x : ℝ => (y : ℂ) ^ ((x : ℂ) + (h : ℂ) * I) / ((x : ℂ) + (h : ℂ) * I)) volume a c :=
    hcont.intervalIntegrable a c
  have hbnd : IntervalIntegrable (fun x : ℝ => y ^ x / |h|) volume a c :=
    ((continuous_rpow_base hy0).div_const |h|).intervalIntegrable a c
  calc ‖∫ x in a..c, (y : ℂ) ^ ((x : ℂ) + (h : ℂ) * I) / ((x : ℂ) + (h : ℂ) * I)‖
      ≤ ∫ x in a..c, ‖(y : ℂ) ^ ((x : ℂ) + (h : ℂ) * I) / ((x : ℂ) + (h : ℂ) * I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hac
    _ ≤ ∫ x in a..c, y ^ x / |h| :=
        intervalIntegral.integral_mono_on hac hint.norm hbnd hpt
    _ = (∫ x in a..c, y ^ x) / |h| := by rw [← intervalIntegral.integral_div]
    _ ≤ y ^ c / (|h| * Real.log y) := by
        have hya : (0 : ℝ) < y ^ a := Real.rpow_pos_of_pos hy0 a
        rw [integral_rpow_base hy0 hLpos.ne' a c, div_div, mul_comm (Real.log y) |h|]
        gcongr
        linarith [hya]

/-- **Horizontal-leg estimate for the Perron rectangle (`y < 1`).**  For `0 < y < 1`, height
`h ≠ 0`, and any `c ≤ b`, the horizontal segment of `y^s/s` at height `h` over `[c,b]` is bounded by
`y^c/(|h|·(-log y))`.  Same estimate as the `y > 1` case with `log y` replaced by `|log y| = -log y`;
now `y^x` is decreasing, so `∫_c^b y^x dx = (y^c - y^b)/(-log y) ≤ y^c/(-log y)`. -/
theorem perron_horizontal_bound_lt {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) {h : ℝ} (hh : h ≠ 0)
    {c b : ℝ} (hcb : c ≤ b) :
    ‖∫ x in c..b, (y : ℂ) ^ ((x : ℂ) + (h : ℂ) * I) / ((x : ℂ) + (h : ℂ) * I)‖
      ≤ y ^ c / (|h| * (- Real.log y)) := by
  have hLneg : Real.log y < 0 := Real.log_neg hy0 hy1
  have hhabs : (0 : ℝ) < |h| := abs_pos.mpr hh
  have hne : ∀ x : ℝ, (x : ℂ) + (h : ℂ) * I ≠ 0 := by
    intro x hx
    have := congrArg Complex.im hx
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.ofReal_re,
      Complex.I_re, mul_zero, mul_one, zero_add, add_zero, Complex.zero_im] at this
    exact hh this
  have hden : ∀ x : ℝ, |h| ≤ ‖(x : ℂ) + (h : ℂ) * I‖ := by
    intro x
    calc |h| = |((x : ℂ) + (h : ℂ) * I).im| := by simp
      _ ≤ ‖(x : ℂ) + (h : ℂ) * I‖ := Complex.abs_im_le_norm _
  have hpt : ∀ x ∈ Set.Icc c b,
      ‖(y : ℂ) ^ ((x : ℂ) + (h : ℂ) * I) / ((x : ℂ) + (h : ℂ) * I)‖ ≤ y ^ x / |h| := by
    intro x _
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0,
      show ((x : ℂ) + (h : ℂ) * I).re = x by simp]
    have hznn : (0 : ℝ) < ‖(x : ℂ) + (h : ℂ) * I‖ := lt_of_lt_of_le hhabs (hden x)
    gcongr
    exact hden x
  have hcont : Continuous fun x : ℝ =>
      (y : ℂ) ^ ((x : ℂ) + (h : ℂ) * I) / ((x : ℂ) + (h : ℂ) * I) := by
    apply Continuous.div
    · exact (by fun_prop : Continuous fun x : ℝ => (x : ℂ) + (h : ℂ) * I).const_cpow
        (Or.inl (by exact_mod_cast hy0.ne'))
    · fun_prop
    · exact hne
  have hint : IntervalIntegrable
      (fun x : ℝ => (y : ℂ) ^ ((x : ℂ) + (h : ℂ) * I) / ((x : ℂ) + (h : ℂ) * I)) volume c b :=
    hcont.intervalIntegrable c b
  have hbnd : IntervalIntegrable (fun x : ℝ => y ^ x / |h|) volume c b :=
    ((continuous_rpow_base hy0).div_const |h|).intervalIntegrable c b
  calc ‖∫ x in c..b, (y : ℂ) ^ ((x : ℂ) + (h : ℂ) * I) / ((x : ℂ) + (h : ℂ) * I)‖
      ≤ ∫ x in c..b, ‖(y : ℂ) ^ ((x : ℂ) + (h : ℂ) * I) / ((x : ℂ) + (h : ℂ) * I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hcb
    _ ≤ ∫ x in c..b, y ^ x / |h| :=
        intervalIntegral.integral_mono_on hcb hint.norm hbnd hpt
    _ = (∫ x in c..b, y ^ x) / |h| := by rw [← intervalIntegral.integral_div]
    _ ≤ y ^ c / (|h| * (- Real.log y)) := by
        have hyb : (0 : ℝ) ≤ y ^ b := (Real.rpow_pos_of_pos hy0 b).le
        have hpos : (0 : ℝ) < |h| * (- Real.log y) := mul_pos hhabs (by linarith)
        have hint_eq : (y ^ b - y ^ c) / Real.log y = (y ^ c - y ^ b) / (- Real.log y) := by
          rw [div_neg, ← neg_div, neg_sub]
        rw [integral_rpow_base hy0 hLneg.ne c b, hint_eq, div_div, mul_comm (- Real.log y) |h|]
        gcongr
        linarith [hyb]

/-- **The Perron rectangle residue.**  For `y > 0` and a rectangle `[-U,c] × [-T,T]` with the pole
`s = 0` strictly interior, `∮ y^s/s = 2πi`.  Decompose `y^s/s = (y^s-1)/s + 1/s`: the second is the
inverse kernel (residue `2πi`), the first extends holomorphically over `0` (removable singularity,
`(y^s-1)/s = o(1/s)`), so its rectangle integral vanishes. -/
theorem perron_rect_residue {y : ℝ} (hy0 : 0 < y) {U c T : ℝ}
    (hU : 0 < U) (hc : 0 < c) (hT : 0 < T) :
    rectangleBoundaryIntegral (fun s => (y : ℂ) ^ s / s) (-U) c (-T) T = 2 * (Real.pi : ℂ) * I := by
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
  set f : ℂ → ℂ := fun s => ((y : ℂ) ^ s - 1) / s with hf
  set G : ℂ → ℂ := Function.update f 0 (limUnder (𝓝[≠] (0 : ℂ)) f) with hG
  set R : Set ℂ := Set.Icc (-U) c ×ℂ Set.Icc (-T) T with hR
  -- `R` is a neighbourhood of `0`
  have hR0 : R ∈ 𝓝 (0 : ℂ) := by
    have hopen : IsOpen (Set.Ioo (-U) c ×ℂ Set.Ioo (-T) T) :=
      isOpen_Ioo.reProdIm isOpen_Ioo
    have hmem : (0 : ℂ) ∈ Set.Ioo (-U) c ×ℂ Set.Ioo (-T) T := by
      rw [Complex.mem_reProdIm]
      simp only [Complex.zero_re, Complex.zero_im, Set.mem_Ioo]
      exact ⟨⟨by linarith, hc⟩, ⟨by linarith, hT⟩⟩
    refine mem_of_superset (hopen.mem_nhds hmem) ?_
    intro z hz
    rw [Complex.mem_reProdIm] at hz ⊢
    exact ⟨Set.Ioo_subset_Icc_self hz.1, Set.Ioo_subset_Icc_self hz.2⟩
  -- `y^s` is entire; `f` is differentiable away from `0`
  have hyz : Differentiable ℂ (fun s : ℂ => (y : ℂ) ^ s) := fun s =>
    DifferentiableAt.const_cpow differentiableAt_id (Or.inl hyc)
  have hf_diff : DifferentiableOn ℂ f (R \ {0}) := by
    apply DifferentiableOn.div
    · exact (hyz.sub (differentiable_const 1)).differentiableOn
    · exact differentiableOn_id
    · intro z hz
      simp only [Set.mem_diff, Set.mem_singleton_iff] at hz
      exact hz.2
  -- the singularity is removable: `f = (y^s-1)/s = o(1/s)` at `0`
  have hf0 : f 0 = 0 := by simp [hf]
  have hlittleO : (fun z => f z - f 0) =o[𝓝[≠] (0 : ℂ)] fun z => (z - 0)⁻¹ := by
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    have htend : Tendsto (fun z : ℂ => (y : ℂ) ^ z - 1) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
      have hca : ContinuousAt (fun z : ℂ => (y : ℂ) ^ z) 0 :=
        (continuous_id.const_cpow (Or.inl hyc)).continuousAt
      have h1 : Tendsto (fun z : ℂ => (y : ℂ) ^ z) (𝓝[≠] (0 : ℂ)) (𝓝 1) := by
        have := hca.tendsto.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
        simpa [Complex.cpow_zero] using this
      simpa using h1.sub_const 1
    have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖(y : ℂ) ^ z - 1‖ < ε := by
      have := Metric.tendsto_nhds.mp htend ε hε
      simpa [dist_eq_norm] using this
    filter_upwards [hev, self_mem_nhdsWithin] with z hz hz0
    have hzne : z ≠ 0 := hz0
    show ‖f z - f 0‖ ≤ ε * ‖(z - (0 : ℂ))⁻¹‖
    rw [hf0, sub_zero, sub_zero]
    have hfz : f z = ((y : ℂ) ^ z - 1) / z := rfl
    rw [hfz, norm_div, norm_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hz.le (by positivity)
  have hG_diff : DifferentiableOn ℂ G R :=
    differentiableOn_update_limUnder_of_isLittleO hR0 hf_diff hlittleO
  -- residue theorem for `G + 1/(·)` : the inverse kernel contributes `2πi`
  have hab : (-U : ℝ) ≤ c := by linarith
  have hcd : (-T : ℝ) ≤ T := by linarith
  have hS : ∀ ρ ∈ ({0} : Finset ℂ), (-U) < ρ.re ∧ ρ.re < c ∧ (-T) < ρ.im ∧ ρ.im < T := by
    intro ρ hρ
    rw [Finset.mem_singleton] at hρ; subst hρ
    simp only [Complex.zero_re, Complex.zero_im]
    exact ⟨by linarith, hc, by linarith, hT⟩
  have hmain := rectangleBoundaryIntegral_holo_add_residues G ({0} : Finset ℂ) (fun _ => (1 : ℂ))
    hab hcd hG_diff hS
  simp only [Finset.sum_singleton, one_mul, sub_zero, mul_one] at hmain
  -- edge agreement: `y^s/s = G s + s⁻¹` for `s ≠ 0`
  have hagree : ∀ s : ℂ, s ≠ 0 → (y : ℂ) ^ s / s = G s + s⁻¹ := by
    intro s hs
    rw [hG, Function.update_of_ne hs]
    show (y : ℂ) ^ s / s = ((y : ℂ) ^ s - 1) / s + s⁻¹
    rw [inv_eq_one_div, ← add_div]
    congr 1
    ring
  have hne_im : ∀ (x t : ℝ), t ≠ 0 → ((x : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro x t ht h
    have := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.ofReal_re,
      Complex.I_re, mul_zero, mul_one, zero_add, add_zero, Complex.zero_im] at this
    exact ht this
  have hne_re : ∀ (s v : ℝ), s ≠ 0 → ((s : ℂ) + (v : ℂ) * I) ≠ 0 := by
    intro s v hs h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_mul, Complex.zero_re] at this
    exact hs this
  have hEQ : rectangleBoundaryIntegral (fun s => (y : ℂ) ^ s / s) (-U) c (-T) T
      = rectangleBoundaryIntegral (fun z => G z + z⁻¹) (-U) c (-T) T := by
    simp only [rectangleBoundaryIntegral]
    rw [intervalIntegral.integral_congr
          (fun x _ => hagree (↑x + ↑(-T : ℝ) * I) (hne_im x (-T) (neg_ne_zero.mpr hT.ne'))),
        intervalIntegral.integral_congr
          (fun x _ => hagree (↑x + ↑(T : ℝ) * I) (hne_im x T hT.ne')),
        intervalIntegral.integral_congr
          (fun v _ => hagree (↑c + ↑v * I) (hne_re c v hc.ne')),
        intervalIntegral.integral_congr
          (fun v _ => hagree (↑(-U : ℝ) + ↑v * I) (hne_re (-U) v (neg_ne_zero.mpr hU.ne')))]
  rw [hEQ, hmain]

/-- **Vertical-leg estimate.**  For `y > 0`, `s ≠ 0`, `T > 0`, the vertical segment of `y^z/z` at
abscissa `s` is bounded by `y^s·2T/|s|`: numerator norm `y^s`, denominator norm `≥ |s|`, length `2T`. -/
theorem perron_vertical_bound {y : ℝ} (hy0 : 0 < y) {s T : ℝ} (hs : s ≠ 0) (hT : 0 < T) :
    ‖∫ v in (-T)..T, (y : ℂ) ^ ((s : ℂ) + (v : ℂ) * I) / ((s : ℂ) + (v : ℂ) * I)‖
      ≤ y ^ s * (2 * T) / |s| := by
  have habs : (0 : ℝ) < |s| := abs_pos.mpr hs
  have hden : ∀ v : ℝ, |s| ≤ ‖(s : ℂ) + (v : ℂ) * I‖ := by
    intro v
    calc |s| = |((s : ℂ) + (v : ℂ) * I).re| := by simp
      _ ≤ ‖(s : ℂ) + (v : ℂ) * I‖ := Complex.abs_re_le_norm _
  have hne : ∀ v : ℝ, (s : ℂ) + (v : ℂ) * I ≠ 0 := by
    intro v h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, zero_mul, Complex.zero_re] at this
    exact hs this
  have hpt : ∀ v ∈ Set.Icc (-T) T,
      ‖(y : ℂ) ^ ((s : ℂ) + (v : ℂ) * I) / ((s : ℂ) + (v : ℂ) * I)‖ ≤ y ^ s / |s| := by
    intro v _
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy0,
      show ((s : ℂ) + (v : ℂ) * I).re = s by simp]
    have : (0 : ℝ) < ‖(s : ℂ) + (v : ℂ) * I‖ := lt_of_lt_of_le habs (hden v)
    gcongr
    exact hden v
  have hcont : Continuous fun v : ℝ =>
      (y : ℂ) ^ ((s : ℂ) + (v : ℂ) * I) / ((s : ℂ) + (v : ℂ) * I) := by
    apply Continuous.div
    · exact (by fun_prop : Continuous fun v : ℝ => (s : ℂ) + (v : ℂ) * I).const_cpow
        (Or.inl (by exact_mod_cast hy0.ne'))
    · fun_prop
    · exact hne
  have hTle : (-T : ℝ) ≤ T := by linarith
  calc ‖∫ v in (-T)..T, (y : ℂ) ^ ((s : ℂ) + (v : ℂ) * I) / ((s : ℂ) + (v : ℂ) * I)‖
      ≤ ∫ v in (-T)..T, ‖(y : ℂ) ^ ((s : ℂ) + (v : ℂ) * I) / ((s : ℂ) + (v : ℂ) * I)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hTle
    _ ≤ ∫ _v in (-T)..T, y ^ s / |s| :=
        intervalIntegral.integral_mono_on hTle (hcont.intervalIntegrable _ _).norm
          (continuous_const.intervalIntegrable _ _) hpt
    _ = y ^ s * (2 * T) / |s| := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        rw [show T - (-T) = 2 * T by ring]
        ring

/-- The effective Perron kernel `(1/2π)∫_{-T}^{T} y^{c+it}/(c+it) dt`. -/
noncomputable def perronKernel (c T y : ℝ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    ∫ v in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (v : ℂ) * I) / ((c : ℂ) + (v : ℂ) * I)

/-- **The Perron kernel bound (`y > 1`).**  `|(1/2π)∫_{-T}^{T} y^{c+it}/(c+it) dt − 1| ≤
y^c/(πT·log y)`.  From the residue `∮ y^s/s = 2πi`, the vertical leg at `c` equals `2πi` minus the
two horizontal legs and the far vertical leg at `-U`; the horizontals are `≤ y^c/(T log y)` and the
far leg `→ 0` as `U → ∞`. -/
theorem perron_kernel_bound {y : ℝ} (hy : 1 < y) {c T : ℝ} (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel c T y - 1‖ ≤ y ^ c / (Real.pi * T * Real.log y) := by
  have hy0 : (0 : ℝ) < y := lt_trans one_pos hy
  have hLpos : 0 < Real.log y := Real.log_pos hy
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hTne : T ≠ 0 := hT.ne'
  have hLne : Real.log y ≠ 0 := hLpos.ne'
  have hπne : Real.pi ≠ 0 := hπ.ne'
  set B : ℝ := y ^ c / (Real.pi * T * Real.log y) with hBdef
  set rt : ℂ := ∫ v in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (v : ℂ) * I) / ((c : ℂ) + (v : ℂ) * I) with hrt
  have hpk : perronKernel c T y = (1 / (2 * (Real.pi : ℂ))) * rt := rfl
  have hc2πI : ‖(2 * (Real.pi : ℂ) * I)‖ = 2 * Real.pi := by
    rw [show (2 : ℂ) * (Real.pi : ℂ) * I = ((2 * Real.pi : ℝ) : ℂ) * I by push_cast; ring,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  -- per-`U` inequality
  have hbound : ∀ U : ℝ, 0 < U →
      ‖perronKernel c T y - 1‖ ≤ B + y ^ (-U) * (2 * T) / U / (2 * Real.pi) := by
    intro U hU
    have hres := perron_rect_residue hy0 hU hc hT
    rw [rectangleBoundaryIntegral] at hres
    set bot : ℂ := ∫ x in (-U)..c,
      (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * I) / ((x : ℂ) + ((-T : ℝ) : ℂ) * I) with hbot
    set top : ℂ := ∫ x in (-U)..c,
      (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * I) / ((x : ℂ) + ((T : ℝ) : ℂ) * I) with htop
    set lf : ℂ := ∫ v in (-T)..T,
      (y : ℂ) ^ (((-U : ℝ) : ℂ) + (v : ℂ) * I) / (((-U : ℝ) : ℂ) + (v : ℂ) * I) with hlf
    rw [← hrt] at hres
    have halg : 2 * (Real.pi : ℂ) * I * (perronKernel c T y - 1) = top - bot + I * lf := by
      rw [hpk]
      have h2 : 2 * (Real.pi : ℂ) * I * ((1 / (2 * (Real.pi : ℂ))) * rt - 1)
          = I * rt - 2 * (Real.pi : ℂ) * I := by
        have hne2 : (2 * (Real.pi : ℂ)) ≠ 0 := by simp [hπne]
        field_simp
      rw [h2]
      linear_combination hres
    have hbotb : ‖bot‖ ≤ y ^ c / (T * Real.log y) := by
      have h := perron_horizontal_bound hy (h := -T) (by simpa using hTne) (a := -U) (c := c)
        (by linarith)
      rw [abs_neg, abs_of_pos hT] at h
      exact h
    have htopb : ‖top‖ ≤ y ^ c / (T * Real.log y) := by
      have h := perron_horizontal_bound hy (h := T) hTne (a := -U) (c := c) (by linarith)
      rw [abs_of_pos hT] at h
      exact h
    have hlfb : ‖lf‖ ≤ y ^ (-U) * (2 * T) / U := by
      have h := perron_vertical_bound hy0 (s := -U) (T := T) (by linarith) hT
      rw [abs_of_neg (by linarith : -U < 0)] at h
      rw [hlf]
      simpa [Complex.ofReal_neg] using h
    have hnorm : 2 * Real.pi * ‖perronKernel c T y - 1‖ = ‖top - bot + I * lf‖ := by
      have hn := congrArg norm halg
      rw [norm_mul, hc2πI] at hn
      exact hn
    have htri : ‖top - bot + I * lf‖ ≤ ‖top‖ + ‖bot‖ + ‖lf‖ := by
      calc ‖top - bot + I * lf‖ ≤ ‖top - bot‖ + ‖I * lf‖ := norm_add_le _ _
        _ ≤ ‖top‖ + ‖bot‖ + ‖lf‖ := by
            rw [norm_mul, Complex.norm_I, one_mul]
            linarith [norm_sub_le top bot]
    have hle : 2 * Real.pi * ‖perronKernel c T y - 1‖
        ≤ 2 * (y ^ c / (T * Real.log y)) + y ^ (-U) * (2 * T) / U := by
      rw [hnorm]; linarith [htri, hbotb, htopb, hlfb]
    have hfin : ‖perronKernel c T y - 1‖
        ≤ (2 * (y ^ c / (T * Real.log y)) + y ^ (-U) * (2 * T) / U) / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]; linarith [hle]
    refine le_trans hfin (le_of_eq ?_)
    rw [hBdef]; field_simp
  -- `U → ∞` : the far vertical leg vanishes
  have hg : Tendsto (fun U : ℝ => y ^ (-U) * (2 * T) / U / (2 * Real.pi)) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun U : ℝ => T / (Real.pi * U))
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with U hU
      have : (0 : ℝ) < y ^ (-U) := Real.rpow_pos_of_pos hy0 _
      positivity
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with U hU
      have hU0 : (0 : ℝ) < U := by linarith
      have hUne : U ≠ 0 := hU0.ne'
      have hr : y ^ (-U) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hy.le (by linarith)
      have hc2 : (2 * T) / U / (2 * Real.pi) = T / (Real.pi * U) := by
        rw [div_div]; field_simp
      rw [mul_div_assoc, mul_div_assoc, hc2]
      calc y ^ (-U) * (T / (Real.pi * U)) ≤ 1 * (T / (Real.pi * U)) :=
            mul_le_mul_of_nonneg_right hr (by positivity)
        _ = T / (Real.pi * U) := one_mul _
    · exact Tendsto.div_atTop tendsto_const_nhds (Tendsto.const_mul_atTop hπ tendsto_id)
  have hlim : Tendsto (fun U : ℝ => B + y ^ (-U) * (2 * T) / U / (2 * Real.pi)) atTop (𝓝 B) := by
    simpa using tendsto_const_nhds.add hg
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with U hU
  exact hbound U hU

/-- **The pole-free Perron rectangle vanishes.**  For `y > 0`, `0 < c ≤ U`, `T > 0`, the pole
`s = 0` of `y^s/s` lies strictly to the *left* of the rectangle `[c,U] × [-T,T]`, so `y^s/s` is
holomorphic on the closed rectangle and its boundary integral vanishes (Cauchy–Goursat). -/
theorem perron_rect_holo {y : ℝ} (hy0 : 0 < y) {c U T : ℝ}
    (hc : 0 < c) (hcU : c ≤ U) (hT : 0 < T) :
    rectangleBoundaryIntegral (fun s => (y : ℂ) ^ s / s) c U (-T) T = 0 := by
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'
  have hyz : Differentiable ℂ (fun s : ℂ => (y : ℂ) ^ s) := fun s =>
    DifferentiableAt.const_cpow differentiableAt_id (Or.inl hyc)
  refine rectangleBoundaryIntegral_eq_zero_of_differentiableOn _ c U (-T) T hcU (by linarith) ?_
  apply DifferentiableOn.div hyz.differentiableOn differentiableOn_id
  intro z hz h0
  rw [Complex.mem_reProdIm] at hz
  have hzre : c ≤ z.re := (Set.mem_Icc.mp hz.1).1
  have h0' : z = 0 := h0
  rw [h0', Complex.zero_re] at hzre
  linarith

/-- **The Perron kernel bound (`y < 1`).**  `|(1/2π)∫_{-T}^{T} y^{c+it}/(c+it) dt| ≤
y^c/(πT·(-log y))`.  The kernel approximates `[y > 1] = 0`.  Now the rectangle `[c,U]×[-T,T]`
encloses *no* pole (Cauchy–Goursat gives `0`); the vertical leg at `c` equals the two horizontal
legs plus the far vertical leg at `U`, and the far leg `→ 0` as `U → ∞` (since `y^U → 0`). -/
theorem perron_kernel_bound_lt {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) {c T : ℝ}
    (hc : 0 < c) (hT : 0 < T) :
    ‖perronKernel c T y‖ ≤ y ^ c / (Real.pi * T * (- Real.log y)) := by
  have hLneg : Real.log y < 0 := Real.log_neg hy0 hy1
  have hLpos' : (0 : ℝ) < - Real.log y := by linarith
  have hLne' : (- Real.log y) ≠ 0 := hLpos'.ne'
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπne : Real.pi ≠ 0 := hπ.ne'
  have hTne : T ≠ 0 := hT.ne'
  set B : ℝ := y ^ c / (Real.pi * T * (- Real.log y)) with hBdef
  set rt : ℂ := ∫ v in (-T)..T, (y : ℂ) ^ ((c : ℂ) + (v : ℂ) * I) / ((c : ℂ) + (v : ℂ) * I) with hrt
  have hpk : perronKernel c T y = (1 / (2 * (Real.pi : ℂ))) * rt := rfl
  have hc2πI : ‖(2 * (Real.pi : ℂ) * I)‖ = 2 * Real.pi := by
    rw [show (2 : ℂ) * (Real.pi : ℂ) * I = ((2 * Real.pi : ℝ) : ℂ) * I by push_cast; ring,
      norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  -- per-`U` inequality
  have hbound : ∀ U : ℝ, c < U →
      ‖perronKernel c T y‖ ≤ B + y ^ U * (2 * T) / U / (2 * Real.pi) := by
    intro U hcU
    have hUpos : 0 < U := lt_trans hc hcU
    have hres := perron_rect_holo hy0 hc hcU.le hT
    rw [rectangleBoundaryIntegral] at hres
    set bot : ℂ := ∫ x in c..U,
      (y : ℂ) ^ ((x : ℂ) + ((-T : ℝ) : ℂ) * I) / ((x : ℂ) + ((-T : ℝ) : ℂ) * I) with hbot
    set top : ℂ := ∫ x in c..U,
      (y : ℂ) ^ ((x : ℂ) + ((T : ℝ) : ℂ) * I) / ((x : ℂ) + ((T : ℝ) : ℂ) * I) with htop
    set rc : ℂ := ∫ v in (-T)..T,
      (y : ℂ) ^ (((U : ℝ) : ℂ) + (v : ℂ) * I) / (((U : ℝ) : ℂ) + (v : ℂ) * I) with hrc
    rw [← hrt] at hres
    have halg : 2 * (Real.pi : ℂ) * I * perronKernel c T y = bot - top + I * rc := by
      rw [hpk]
      have h2 : 2 * (Real.pi : ℂ) * I * ((1 / (2 * (Real.pi : ℂ))) * rt) = I * rt := by
        have hne2 : (2 * (Real.pi : ℂ)) ≠ 0 := by simp [hπne]
        field_simp
      rw [h2]
      linear_combination -hres
    have hbotb : ‖bot‖ ≤ y ^ c / (T * (- Real.log y)) := by
      have h := perron_horizontal_bound_lt hy0 hy1 (h := -T) (by simpa using hTne) (c := c) (b := U)
        (by linarith)
      rw [abs_neg, abs_of_pos hT] at h
      exact h
    have htopb : ‖top‖ ≤ y ^ c / (T * (- Real.log y)) := by
      have h := perron_horizontal_bound_lt hy0 hy1 (h := T) hTne (c := c) (b := U) (by linarith)
      rw [abs_of_pos hT] at h
      exact h
    have hrcb : ‖rc‖ ≤ y ^ U * (2 * T) / U := by
      have h := perron_vertical_bound hy0 (s := U) (T := T) hUpos.ne' hT
      rw [abs_of_pos hUpos] at h
      rw [hrc]
      exact h
    have hnorm : 2 * Real.pi * ‖perronKernel c T y‖ = ‖bot - top + I * rc‖ := by
      have hn := congrArg norm halg
      rw [norm_mul, hc2πI] at hn
      exact hn
    have htri : ‖bot - top + I * rc‖ ≤ ‖bot‖ + ‖top‖ + ‖rc‖ := by
      calc ‖bot - top + I * rc‖ ≤ ‖bot - top‖ + ‖I * rc‖ := norm_add_le _ _
        _ ≤ ‖bot‖ + ‖top‖ + ‖rc‖ := by
            rw [norm_mul, Complex.norm_I, one_mul]
            linarith [norm_sub_le bot top]
    have hle : 2 * Real.pi * ‖perronKernel c T y‖
        ≤ 2 * (y ^ c / (T * (- Real.log y))) + y ^ U * (2 * T) / U := by
      rw [hnorm]; linarith [htri, hbotb, htopb, hrcb]
    have hfin : ‖perronKernel c T y‖
        ≤ (2 * (y ^ c / (T * (- Real.log y))) + y ^ U * (2 * T) / U) / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)]; linarith [hle]
    refine le_trans hfin (le_of_eq ?_)
    rw [hBdef]; field_simp
  -- `U → ∞` : the far vertical leg vanishes (`y^U → 0`)
  have hg : Tendsto (fun U : ℝ => y ^ U * (2 * T) / U / (2 * Real.pi)) atTop (𝓝 0) := by
    apply squeeze_zero' (g := fun U : ℝ => T / (Real.pi * U))
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with U hU
      have : (0 : ℝ) < y ^ U := Real.rpow_pos_of_pos hy0 _
      positivity
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with U hU
      have hU0 : (0 : ℝ) < U := by linarith
      have hr : y ^ U ≤ 1 := Real.rpow_le_one hy0.le hy1.le (by linarith)
      have hc2 : (2 * T) / U / (2 * Real.pi) = T / (Real.pi * U) := by
        rw [div_div]; field_simp
      rw [mul_div_assoc, mul_div_assoc, hc2]
      calc y ^ U * (T / (Real.pi * U)) ≤ 1 * (T / (Real.pi * U)) :=
            mul_le_mul_of_nonneg_right hr (by positivity)
        _ = T / (Real.pi * U) := one_mul _
    · exact Tendsto.div_atTop tendsto_const_nhds (Tendsto.const_mul_atTop hπ tendsto_id)
  have hlim : Tendsto (fun U : ℝ => B + y ^ U * (2 * T) / U / (2 * Real.pi)) atTop (𝓝 B) := by
    simpa using tendsto_const_nhds.add hg
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_gt_atTop c] with U hU
  exact hbound U hU

end CriticalLinePhasor.Perron

#print axioms CriticalLinePhasor.Perron.perron_horizontal_bound
#print axioms CriticalLinePhasor.Perron.perron_horizontal_bound_lt
#print axioms CriticalLinePhasor.Perron.perron_rect_residue
#print axioms CriticalLinePhasor.Perron.perron_rect_holo
#print axioms CriticalLinePhasor.Perron.perron_vertical_bound
#print axioms CriticalLinePhasor.Perron.perron_kernel_bound
#print axioms CriticalLinePhasor.Perron.perron_kernel_bound_lt
