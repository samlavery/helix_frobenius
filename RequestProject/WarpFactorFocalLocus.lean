import RequestProject.WarpFactorAudit
import RequestProject.LimitFocalEvent
import RequestProject.ResidueJump

/-!
# `D_δ` on the native focal detector: the rank-drop height is rigid (ledger 1198)

`WarpFactorAudit` split `e^{−sH} = D_{Re s} · U_{Im s}` and identified `U_t` with the house height
flow. This file asks what the positive factor `D_δ : a_n ↦ n^{−δ} a_n` does to the rank drops of the
native focal detector `lawDetector` (finite head) and its normalized limit (`LimitFocalEvent`).

* `cSpin`, `cSpin_real`, `cSpin_imag`: `D_δ` is the height flow's own per-site factor `exp(−iτ log n)`
  at imaginary time `τ = −iδ`. The generator is the same `log n`; `D` is not reached at real time.
* `dilateFiber_eq`, `lawUnsigned_dilate`: `D_δ` sends the grown fiber's two channels at `s` to the
  channels at `s + δ`, at the same head and window. `dilate_detector`: the `D`-image detector is
  `lawDetector` at `s + δ`.
* `dilate_normalized`: the house normalization (`harmonicPencil_factor`) splits off the mass column
  only. The signed channel of the `D`-image is `lawFiber` at `s + δ`, untouched by normalization.
  `dilate_rankDrop_iff`: the `D`-image drops rank exactly where the fiber at `s + δ` cancels.
* `flowFiber_eq`: `U_t` sends `s` to `s + it`. `D` and `U` are the two translations of `s`.
* `LimitFocalEvent.dilate_image`, `LimitFocalEvent.ofDilate`, `ofDilate_height`: every limit focal
  event at exponent `σ` and height `Z = e^y` is the `D_{σ − σ₀}`-image of the grown fiber at
  exponent `σ₀` at the same `y`, for every reference exponent `σ₀`; and a `D`-image cancellation is a
  limit focal event at the base point's height.
* `zeta_zero_rigid`, `eta_event_rigid`: a ζ event is an isolated point of the (transverse, height)
  plane. For every small `(δ, t) ≠ 0` the grown η fiber at `ρ + δ + it` does not cancel in the limit:
  `D_δ` does not carry the event to a nearby height; it removes it there.
-/

open Complex Filter Topology Finset
open scoped Matrix

noncomputable section

namespace CriticalLinePhasor.WarpFactorLocus

open CriticalLinePhasor CriticalLinePhasor.FiberDetectorChain CriticalLinePhasor.HarmonicCell
open CriticalLinePhasor.LimitFocalEventNS CriticalLinePhasor.GrownFiberEvolution
open CriticalLinePhasor.EisensteinWheelBank

/-! ## 0. `D` is the height flow at imaginary time -/

/-- The height flow's per-site factor at complex time `τ`: `exp(−iτ log n)`. -/
def cSpin (τ : ℂ) (n : ℕ) : ℂ := Complex.exp (-(τ * (Real.log n : ℂ)) * I)

theorem cSpin_real (t : ℝ) (n : ℕ) : cSpin t n = LFunctionPhasor.mellinSpin t n := by
  unfold cSpin LFunctionPhasor.mellinSpin
  push_cast
  ring_nf

/-- **`D_δ` is the height flow at imaginary time `−iδ`.** -/
theorem cSpin_imag (δ : ℝ) {n : ℕ} (hn : 0 < n) :
    cSpin (-(δ : ℂ) * I) n = (((n : ℝ) ^ (-δ) : ℝ) : ℂ) := by
  rw [Real.rpow_def_of_pos (by exact_mod_cast hn), Complex.ofReal_exp]
  unfold cSpin
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_neg]
  linear_combination (δ * (Real.log n : ℂ)) * Complex.I_sq

theorem cSpin_add (τ τ' : ℂ) (n : ℕ) : cSpin (τ + τ') n = cSpin τ n * cSpin τ' n := by
  unfold cSpin
  rw [← Complex.exp_add]
  congr 1
  ring

/-! ## 1. `D` on the finite detector -/

theorem site_dilate (k : ℕ) (s : ℂ) (δ : ℝ) :
    ((((k : ℝ) + 1) ^ (-δ) : ℝ) : ℂ) * ((k : ℂ) + 1) ^ (-s) = ((k : ℂ) + 1) ^ (-(s + δ)) := by
  have hx : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hc : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  have hne : (((k : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [hc, Complex.ofReal_cpow hx.le, ← Complex.cpow_add _ _ hne]
  congr 1
  push_cast
  ring

theorem site_flow (k : ℕ) (s : ℂ) (t : ℝ) :
    LFunctionPhasor.mellinSpin t (k + 1) * ((k : ℂ) + 1) ^ (-s) =
      ((k : ℂ) + 1) ^ (-(s + (t : ℂ) * I)) := by
  have hx : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hc : ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  have hne : (((k : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [hc, show -(s + (t : ℂ) * I) = -s + (-(t : ℂ) * I) by ring, Complex.cpow_add _ _ hne,
    Complex.cpow_def_of_ne_zero hne (-(t : ℂ) * I), ← Complex.ofReal_log hx.le, mul_comm]
  unfold LFunctionPhasor.mellinSpin
  congr 2
  push_cast
  ring

/-- `D_δ` applied to the grown fiber's sites. -/
def dilateFiber (w : ℕ → ℂ) (Z : ℝ) (s : ℂ) (δ : ℝ) : ℂ :=
  windowed (fun k => ((((k : ℝ) + 1) ^ (-δ) : ℝ) : ℂ) * (w (k + 1) * ((k : ℂ) + 1) ^ (-s))) Z

/-- **`D_δ` sends the signed channel at `s` to the signed channel at `s + δ`**, same head, same
window. -/
theorem dilateFiber_eq (w : ℕ → ℂ) (Z : ℝ) (s : ℂ) (δ : ℝ) :
    dilateFiber w Z s δ = lawFiber w Z (s + δ) := by
  unfold dilateFiber lawFiber windowed
  refine Finset.sum_congr rfl fun k _ => ?_
  dsimp only
  rw [← site_dilate]
  ring

/-- `U_t` applied to the grown fiber's sites. -/
def flowFiber (w : ℕ → ℂ) (Z : ℝ) (s : ℂ) (t : ℝ) : ℂ :=
  windowed (fun k => LFunctionPhasor.mellinSpin t (k + 1) * (w (k + 1) * ((k : ℂ) + 1) ^ (-s))) Z

/-- `U_t` sends the signed channel at `s` to the signed channel at `s + it`. -/
theorem flowFiber_eq (w : ℕ → ℂ) (Z : ℝ) (s : ℂ) (t : ℝ) :
    flowFiber w Z s t = lawFiber w Z (s + (t : ℂ) * I) := by
  unfold flowFiber lawFiber windowed
  refine Finset.sum_congr rfl fun k _ => ?_
  dsimp only
  rw [← site_flow]
  ring

/-- `D_δ` sends the unsigned channel at exponent `σ` to the unsigned channel at `σ + δ`. -/
theorem lawUnsigned_dilate (w : ℕ → ℂ) (Z σ δ : ℝ) :
    ∑ k ∈ range ⌈Z⌉₊, headWindow Z k * ‖w (k + 1)‖ * (((k : ℝ) + 1) ^ (-σ) * ((k : ℝ) + 1) ^ (-δ)) =
      lawUnsigned w Z (σ + δ) := by
  unfold lawUnsigned
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Real.rpow_add (by positivity)]
  congr 2
  ring

/-- **The `D`-image detector is the native detector at `s + δ`.** -/
theorem dilate_detector (w : ℕ → ℂ) (Z : ℝ) (s : ℂ) (δ : ℝ) (μ lam : ℂ) :
    harmonicPencil ((lawUnsigned w Z (s.re + δ) : ℝ) : ℂ) (dilateFiber w Z s δ) μ lam =
      lawDetector w Z (s + δ) μ lam := by
  rw [dilateFiber_eq, lawDetector]
  simp

/-- **Normalization splits off the mass column only.** The `D`-image's signed channel is the fiber
at `s + δ`, and it survives normalization. -/
theorem dilate_normalized (w : ℕ → ℂ) (Z : ℝ) (s : ℂ) (δ : ℝ) (μ lam : ℂ) :
    lawDetector w Z (s + δ) μ lam =
      harmonicPencil 1 (dilateFiber w Z s δ) μ lam *
        Matrix.diagonal ![((lawUnsigned w Z (s.re + δ) : ℝ) : ℂ), 1] := by
  rw [← dilate_detector, harmonicPencil_factor]

/-- **The `D`-image drops rank exactly where the fiber at `s + δ` cancels.** -/
theorem dilate_rankDrop_iff (w : ℕ → ℂ) {Z : ℝ} (hZ : 1 < Z) (hw : ‖w 1‖ = 1) (s : ℂ) (δ : ℝ)
    (μ lam : ℂ) (hlam : lam ≠ μ) :
    dilateFiber w Z s δ = 0 ↔
      ((lawDetector w Z (s + δ) μ lam)ᴴ * lawDetector w Z (s + δ) μ lam).det = 0 := by
  rw [dilateFiber_eq]
  exact finite_cancel_iff_rankDrop w hZ hw _ μ lam hlam

/-- `D` and `U` commute on the grown fiber: both are translations of `s`. -/
theorem dilate_flow_comm (w : ℕ → ℂ) (Z : ℝ) (s : ℂ) (δ t : ℝ) :
    dilateFiber w Z (s + (t : ℂ) * I) δ = flowFiber w Z (s + δ) t := by
  rw [dilateFiber_eq, flowFiber_eq]
  congr 1
  ring

/-! ## 2. The limit: every event is a `D`-image at its own height -/

/-- **Every limit focal event is a `D`-image at its own height**: for every reference exponent
`σ₀`, the event at `(σ, y)` is the limit cancellation of the `D_{σ−σ₀}`-image of the grown fiber at
`σ₀ + iy`. -/
theorem LimitFocalEvent.dilate_image (e : LimitFocalEvent) (σ₀ : ℝ) :
    Tendsto (fun Z => dilateFiber e.w Z ((σ₀ : ℂ) + (e.y : ℂ) * I) (e.σ - σ₀)) atTop (𝓝 0) := by
  have h : ((σ₀ : ℂ) + (e.y : ℂ) * I) + ((e.σ - σ₀ : ℝ) : ℂ) = (e.σ : ℂ) + (e.y : ℂ) * I := by
    push_cast
    ring
  simp_rw [dilateFiber_eq, h]
  exact e.cancel

/-- A `D`-image cancellation is a limit focal event. -/
def LimitFocalEvent.ofDilate (w : ℕ → ℂ) (σ₀ δ y : ℝ) (hpos : 0 < σ₀ + δ)
    (h : Tendsto (fun Z => dilateFiber w Z ((σ₀ : ℂ) + (y : ℂ) * I) δ) atTop (𝓝 0)) :
    LimitFocalEvent where
  w := w
  σ := σ₀ + δ
  y := y
  σ_pos := hpos
  cancel := by
    have hs : ((σ₀ : ℂ) + (y : ℂ) * I) + (δ : ℂ) = ((σ₀ + δ : ℝ) : ℂ) + (y : ℂ) * I := by
      push_cast
      ring
    simp_rw [dilateFiber_eq, hs] at h
    exact h

/-- **`D` does not change the height**: the `D`-image event sits at the base point's height
`e^y`, whatever `δ` is. -/
theorem ofDilate_height (w : ℕ → ℂ) (σ₀ δ y : ℝ) (hpos : 0 < σ₀ + δ)
    (h : Tendsto (fun Z => dilateFiber w Z ((σ₀ : ℂ) + (y : ℂ) * I) δ) atTop (𝓝 0)) :
    (LimitFocalEvent.ofDilate w σ₀ δ y hpos h).height = Real.exp y :=
  LimitFocalEvent.height_eq _

/-! ## 3. Rigidity: `D` removes an event, it does not move it -/

/-- **A ζ zero is an isolated point of the (transverse, height) plane.** -/
theorem zeta_zero_rigid {ρ : ℂ} (hρ : ρ ≠ 1) :
    ∀ᶠ p : ℝ × ℝ in 𝓝[≠] 0, riemannZeta (ρ + p.1 + p.2 * I) ≠ 0 := by
  have hd : DifferentiableOn ℂ riemannZeta {s : ℂ | s ≠ 1} := fun s hs =>
    (differentiableAt_riemannZeta hs).differentiableWithinAt
  have hana : AnalyticAt ℂ riemannZeta ρ := hd.analyticAt (isOpen_ne.mem_nhds hρ)
  have hev : ∀ᶠ u in 𝓝[≠] ρ, riemannZeta u ≠ 0 :=
    hana.eventually_eq_zero_or_eventually_ne_zero.resolve_left
      (ResidueJump.zeta_not_eventually_zero hρ)
  set f : ℝ × ℝ → ℂ := fun p => ρ + p.1 + p.2 * I with hf
  have hcont : Continuous f := by fun_prop
  have hf0 : f 0 = ρ := by simp [hf]
  have hT : Tendsto f (𝓝[≠] 0) (𝓝[≠] ρ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · rw [← hf0]
      exact hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · refine eventually_nhdsWithin_of_forall fun p hp heq => hp ?_
      have h0 : (p.1 : ℂ) + (p.2 : ℂ) * I = 0 := by
        simp only [hf, Set.mem_singleton_iff] at heq
        linear_combination heq
      have h1 := congrArg Complex.re h0
      have h2 := congrArg Complex.im h0
      simp at h1 h2
      exact Prod.ext h1 h2
  exact hT.eventually hev

/-- **No small `D`–height combination carries a ζ event to another limit event.** For a nontrivial
zero `ρ` and every small `(δ, t) ≠ 0`, the `D_δ`-image of the grown η fiber at `ρ + it` does not
cancel in the limit. In particular `D_δ` alone (`t = 0`) removes the event, and no height near it
receives one. -/
theorem eta_event_rigid {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    ∀ᶠ p : ℝ × ℝ in 𝓝[≠] 0,
      ¬ Tendsto (fun Z => dilateFiber Routing.eta.coeff Z (ρ + (p.2 : ℂ) * I) p.1) atTop (𝓝 0) := by
  obtain ⟨h0, h1, -⟩ := hρ
  have hne : ρ ≠ 1 := by
    rintro rfl
    simp at h1
  have ht : Tendsto (fun p : ℝ × ℝ => ρ.re + p.1) (𝓝 0) (𝓝 ρ.re) :=
    Continuous.tendsto' (by fun_prop) 0 ρ.re (by simp)
  have hI := ht.eventually (Ioo_mem_nhds h0 h1)
  filter_upwards [zeta_zero_rigid hne, nhdsWithin_le_nhds hI] with p hz hmem hT
  have hs : ρ + (p.2 : ℂ) * I + (p.1 : ℂ) = ρ + p.1 + p.2 * I := by ring
  simp_rw [dilateFiber_eq, hs] at hT
  have hre : (ρ + (p.1 : ℂ) + (p.2 : ℂ) * I).re = ρ.re + p.1 := by simp
  exact hz ((limit_chain_eta (hre ▸ hmem.1) (hre ▸ hmem.2) 0 1 one_ne_zero).1.mp hT)

end CriticalLinePhasor.WarpFactorLocus

end

#print axioms CriticalLinePhasor.WarpFactorLocus.cSpin_imag
#print axioms CriticalLinePhasor.WarpFactorLocus.dilateFiber_eq
#print axioms CriticalLinePhasor.WarpFactorLocus.flowFiber_eq
#print axioms CriticalLinePhasor.WarpFactorLocus.lawUnsigned_dilate
#print axioms CriticalLinePhasor.WarpFactorLocus.dilate_normalized
#print axioms CriticalLinePhasor.WarpFactorLocus.dilate_rankDrop_iff
#print axioms CriticalLinePhasor.WarpFactorLocus.dilate_flow_comm
#print axioms CriticalLinePhasor.WarpFactorLocus.LimitFocalEvent.dilate_image
#print axioms CriticalLinePhasor.WarpFactorLocus.ofDilate_height
#print axioms CriticalLinePhasor.WarpFactorLocus.zeta_zero_rigid
#print axioms CriticalLinePhasor.WarpFactorLocus.eta_event_rigid
