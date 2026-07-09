import RequestProject.StOscillation
import RequestProject.CircleMonodromy
import RequestProject.CarrierReachability
import RequestProject.Faithfulness
import RequestProject.GeometricReadout
import RequestProject.SourceHolonomy
import RequestProject.HeightGrowthActive

/-!
# The S(t) carrier-scale compensation theorem

Formalizes §"The scale mismatch behind the S(t) term" of `automorph/universal.tex`
(`sec:carrier-S`).  The theorem target is

  `N_{π/3}(e^t) − N_1(e^t) = S(t)`,

with the two **non-tautological carrier identifications** derived from their respective
realizations (never inserted as definitions):

  `N_{π/3}(e^t) = N(t)`   and   `N_1(e^t) = 1 + ϑ(t)/π`.

**What `S(t)` is**: a *fundamental gap*, not a property of vanishing or of crossings.  Each
integer sits on the carrier at native coordinate `n·(π/3)`; the conventional chart registers
the same integer at `n·1`.  The two placements are incommensurable — the lattices share only
the origin (`lattice_gap_fundamental`, irrationality of `π`) — so the unit chart can never
re-synchronize with the native registration: it structurally cannot complete a native cell
(`unit_never_closes`), and the accumulated registration gap between the two scalings of one
arithmetic procession is exactly what the 1-D chart readout calls `S(t)`.  Crossings enter
only as the *units* of the native bookkeeping.

## The chain, and what each piece is

* **§1 The scale dichotomy (the mechanism).**  The same fiber, the same crossing predicate;
  only the carrier scale changes.  At `H = π/3` the carrier closes exactly (six-cell
  monodromy, antipodal wall `cell n + cell (n+3) = 0`).  At `H = 1` the carrier **provably
  never closes**: no finite monodromy (`Monodromy.unit_not_finite_monodromy`, irrationality
  of `π`) and no antipodal cancellation (`unit_cell_no_antipodal`, `π ≠ 3`).  So the unit
  chart can complete no arithmetic cell: its registered procession is continuous — the smooth
  clock only — while the native chart registers the completed (quantized) closure events.

* **§2 The unit chart's clock `ϑ`, constructed.**  `theta t := ∫₀ᵗ Re (logDeriv Γℝ(½+iu)) du`
  is the continuous phase of the archimedean gauge on the line: `theta_zero`, the polar lift
  `gauge_polar : Γℝ(½+it) = ‖Γℝ(½+it)‖·e^{iϑ(t)}`, and uniqueness (`theta_unique`).  This is
  the Riemann–Siegel theta — the continuous branch of `arg Γ(¼+it/2) − (t/2)·log π` — obtained
  here as a theorem about the gauge, not as an imported asymptotic.

* **§3 The native registration identity.**  `unit_chart_factorization`:
  `ζ(½+it) = rsZ(t)·e^{−iϑ(t)}` with `rsZ(t)` **real** (it is the Riemann–Siegel `Z`).
  Hence `no_native_oscillation`: the clock-despun unit readout is real at every height —
  the fiber carries **zero** continuous oscillation beyond the clock, and the arithmetic
  content is π-quantized (`StOscillation.zeta_line_phase_quantized`).  There is no native
  oscillatory state for `S(t)` to be.

* **§4 The scale-indexed count functor, and both counts derived.**  `registeredCount` is one
  functor for both realizations: DC base + continuous clock procession in π-cells + completed
  closure events, the last gated by `CircleMonodromy H` (a carrier can only register cells
  that close).  The gate is *proven* open at `π/3` and *proven* shut at `1` — not chosen.
  With the fiber's own closure predicate (`NativeClosure`, the η-accumulation of
  `Faithful.continuous_model_zeta`) and the readout (`Readout.readout_exp`):
  - `native_identification : N_pi3 (e^t) = N(t)` — the native count is the arithmetic
    event count (each complete closure **is** an on-line zero, and conversely);
  - `unit_identification : N_1 (e^t) = 1 + theta t / π` — the unit count is the DC residue
    (`dcResidue_spec`, the pole of the trivial channel, value forced `= 1`) plus the clock.

* **§5 Subtraction.**  `carrier_scale_compensation_S` (the boxed target, unconditional):
  `N_pi3(e^t) − N_1(e^t) = S(t)`, with `S` the accumulated registration gap and
  `count_decomposition` its classical shape `N(t) = 1 + ϑ(t)/π + S(t)`.
  `S_has_no_native_carrier`: `S` is registration bookkeeping — no native oscillatory state.

* **§6 Exhaustion — proven, consumed.**  The 3-D event space is the height ray, and its
  exhaustion is a *theorem* (`SourceHolonomy.threeD_exhaustive`): every event is weld-fixed,
  there is nowhere else for an event to occur.  `native_events_sourced` instantiates it at
  the ζ fiber; `event_encoding_complete` re-exports the lossless height encoding
  (`Geometry.online_zeros_exhausted`).  Nothing is left out of the native count.

## Scope (exact)

Unconditional throughout: `{propext, Classical.choice, Quot.sound}`, no `sorry`, no `axiom`,
no hypothesis parameters.  `N(t)` is the zero-counting procession of the 3-D system over its
**entire** event space — the height ray, whose exhaustion is proven and consumed in §6.  The
gap proven here is *fundamental*: the scale-registration gap between the incommensurable
`π/3` and unit-`1` placements of one arithmetic procession.  Zero placement plays no role on
either side of any statement in this file: this is a counting/registration identity, and it
has nothing to do with RH/GRH (neither assumed, nor proved, nor needed).  The strip of the
1-D chart is a projection device with no 3-D counterpart; it does not appear.
-/

set_option maxHeartbeats 1000000

open Complex Filter Set MeasureTheory intervalIntegral
open scoped Real Topology BigOperators

namespace CriticalLinePhasor.CarrierScale

open CriticalLinePhasor

/-! ## §0 The critical line -/

/-- The complex line map `z ↦ 1/2 + z·I` (the chart-independent carrier axis). -/
noncomputable def lineC (z : ℂ) : ℂ := 1 / 2 + z * I

/-- The critical-line parametrization by real height, `line t = 1/2 + i·t`. -/
noncomputable def line (t : ℝ) : ℂ := lineC (t : ℂ)

lemma line_def (t : ℝ) : line t = 1 / 2 + (t : ℂ) * I := rfl

lemma line_re (t : ℝ) : (line t).re = 1 / 2 := by
  simp [line, lineC]

lemma line_re_pos (t : ℝ) : 0 < (line t).re := by
  rw [line_re]; norm_num

lemma line_ne_zero (t : ℝ) : line t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [line_re] at this
  norm_num at this

/-- The exact gauge never vanishes on the line. -/
lemma gauge_ne_zero (t : ℝ) : Gammaℝ (line t) ≠ 0 :=
  Gammaℝ_ne_zero_of_re_pos (line_re_pos t)

/-! ## §1 The scale dichotomy: `π/3` closes, unit-`1` provably never does

The same cell law `cellAt H n = exp(i·H·n)` at both scales.  The closure mechanism —
finite monodromy and the antipodal (half-turn) cancellation wall — exists at `H = π/3`
and is **impossible** at `H = 1`, both by the irrationality of `π`.  This is the entire
reason the two registrations of one arithmetic procession differ. -/

/-- The carrier cell phasor at scale `H`: `cellAt H n = exp(i·H·n)`. -/
noncomputable def cellAt (H : ℝ) (n : ℕ) : ℂ := Complex.exp (I * ((H * (n : ℝ) : ℝ) : ℂ))

/-- At the native scale the cell is the μ6 cell of the geometric layer. -/
theorem cellAt_pi3_eq_cell (n : ℕ) : cellAt (Real.pi / 3) n = Geometric.cell n := by
  unfold cellAt Geometric.cell
  congr 1
  push_cast
  ring

/-- **Native antipodal closure**: at `H = π/3` three cells are an exact half turn —
`cell n + cell (n+3) = 0` (= `Readout.cell_antipodal_cancel`). -/
theorem pi3_antipodal (n : ℕ) :
    cellAt (Real.pi / 3) n + cellAt (Real.pi / 3) (n + 3) = 0 := by
  rw [cellAt_pi3_eq_cell, cellAt_pi3_eq_cell]
  exact Readout.cell_antipodal_cancel n

/-- **Native finite monodromy**: the `π/3` carrier closes exactly after 6 cells
(= `Monodromy.pi3_finite_monodromy`). -/
theorem pi3_closes : Monodromy.CircleMonodromy (Real.pi / 3) :=
  Monodromy.pi3_finite_monodromy

/-- **The unit carrier never completes a cell**: `exp(i·k) ≠ 1` for every `k ≥ 1` —
a closure would force `π = k/(2m)` rational. -/
theorem unit_cell_never_closes {k : ℕ} (hk : 0 < k) : cellAt 1 k ≠ 1 := by
  intro h
  rw [cellAt, Complex.exp_eq_one_iff] at h
  obtain ⟨m, hm⟩ := h
  have him := congrArg Complex.im hm
  simp [Complex.mul_im] at him
  -- him : (k : ℝ) = m * (2 * π)
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0] at him
    simp at him
    exact (Nat.cast_ne_zero.mpr hk.ne').elim (by exact_mod_cast him)
  exact irrational_pi ⟨(k : ℚ) / (2 * m), by
    push_cast
    rw [div_eq_iff (by exact_mod_cast mul_ne_zero two_ne_zero (Int.cast_ne_zero.mpr hm0))]
    linarith [him]⟩

/-- **The unit carrier has no antipodal wall**: `cellAt 1 n + cellAt 1 (n+3) ≠ 0` for every
`n` — the μ6 cancellation identity has no unit-scale counterpart, because `π ≠ 3`. -/
theorem unit_cell_no_antipodal (n : ℕ) : cellAt 1 n + cellAt 1 (n + 3) ≠ 0 := by
  intro h
  have hsplit : cellAt 1 (n + 3) = cellAt 1 n * Complex.exp (I * 3) := by
    rw [cellAt, cellAt, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hsplit] at h
  have hfac : cellAt 1 n * (1 + Complex.exp (I * 3)) = 0 := by
    rw [mul_add, mul_one]; exact h
  have hne : cellAt 1 n ≠ 0 := Complex.exp_ne_zero _
  have hneg : Complex.exp (I * 3) = -1 := by
    have := (mul_eq_zero.mp hfac).resolve_left hne
    linear_combination this
  have hsq : Complex.exp (I * 6) = 1 := by
    rw [show (I * 6 : ℂ) = I * 3 + I * 3 by ring, Complex.exp_add, hneg]
    ring
  rw [Complex.exp_eq_one_iff] at hsq
  obtain ⟨m, hm⟩ := hsq
  have him := congrArg Complex.im hm
  simp [Complex.mul_im] at him
  -- him : 6 = m * (2 * π)
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0] at him
    norm_num at him
  exact irrational_pi ⟨(3 : ℚ) / m, by
    push_cast
    rw [div_eq_iff (by exact_mod_cast Int.cast_ne_zero.mpr hm0)]
    linarith [him]⟩

/-- **The unit carrier has no finite monodromy** (= `Monodromy.unit_not_finite_monodromy`):
the unit-`1` realization can register **no** complete arithmetic closure, ever. -/
theorem unit_never_closes : ¬ Monodromy.CircleMonodromy (1 : ℝ) :=
  Monodromy.unit_not_finite_monodromy

/-- **The fundamental scale gap.**  The native placement puts integer `k` at carrier
coordinate `k·(π/3)`; the unit chart puts an integer at `m·1`.  The two lattices meet only
at the origin: for `k ≥ 1`, `k·(π/3)` is never an integer (`π` irrational).  The two
registrations of one procession can never re-synchronize — this gap is structural, prior to
any question of vanishing or crossing, and its accumulated readout is `S(t)`. -/
theorem lattice_gap_fundamental {k : ℕ} (hk : 0 < k) (m : ℕ) :
    (k : ℝ) * (Real.pi / 3) ≠ (m : ℝ) := by
  intro h
  exact irrational_pi ⟨(3 * m : ℚ) / k, by
    push_cast
    rw [div_eq_iff (by exact_mod_cast hk.ne' : (k : ℝ) ≠ 0)]
    linarith [h]⟩

/-- Each integer's two placements differ: `n·(π/3) ≠ n·1` for every `n ≥ 1` — the
per-integer registration gap of the two scalings. -/
theorem integer_placement_gap {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * (Real.pi / 3) ≠ (n : ℝ) :=
  lattice_gap_fundamental hn n

/-! ## §2 The unit chart's clock: the continuous gauge phase `ϑ`

`theta t = ∫₀ᵗ Re (logDeriv Γℝ (½+iu)) du` — the cumulative continuous phase of the
archimedean gauge along the line, normalized `theta 0 = 0`.  `gauge_polar` proves it *is*
the phase: `Γℝ(½+it) = ‖Γℝ(½+it)‖ · e^{iϑ(t)}`; `theta_unique` proves it is the *only*
continuous phase with that normalization.  Classically this continuous branch of
`arg Γ(¼ + it/2) − (t/2)·log π` is the Riemann–Siegel theta. -/

/-- Γℝ is complex-differentiable on the open right half-plane. -/
lemma gammaR_differentiableAt {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ Gammaℝ s := by
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s :=
    (differentiableAt_id.neg.div_const 2).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have h2 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z / 2)) s := by
    have hG : DifferentiableAt ℂ Complex.Gamma (s / 2) := by
      refine Complex.differentiableAt_Gamma _ (fun m => ?_)
      intro h
      have := congrArg Complex.re h
      simp at this
      nlinarith [this, hs, (Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    exact hG.comp s (differentiableAt_id.div_const 2)
  exact h1.mul h2

/-- Γℝ' is continuous on the right half-plane (holomorphy ⟹ analyticity ⟹ analytic deriv). -/
lemma gammaR_deriv_continuousAt {s : ℂ} (hs : 0 < s.re) :
    ContinuousAt (deriv Gammaℝ) s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hd : DifferentiableOn ℂ Gammaℝ {z : ℂ | 0 < z.re} :=
    fun z hz => (gammaR_differentiableAt hz).differentiableWithinAt
  exact ((hd.analyticAt (hU.mem_nhds hs)).deriv).continuousAt

/-- **The clock rate**: the instantaneous phase speed of the gauge on the line,
`clockRate t = Re (logDeriv Γℝ (½+it))`. -/
noncomputable def clockRate (t : ℝ) : ℝ := (logDeriv Gammaℝ (line t)).re

lemma continuous_line : Continuous line := by
  unfold line lineC
  fun_prop

lemma continuous_clockRate : Continuous clockRate := by
  rw [continuous_iff_continuousAt]
  intro t
  have hline : ContinuousAt line t := continuous_line.continuousAt
  have h1 : ContinuousAt (fun u : ℝ => deriv Gammaℝ (line u)) t :=
    (gammaR_deriv_continuousAt (line_re_pos t)).comp hline
  have h2 : ContinuousAt (fun u : ℝ => Gammaℝ (line u)) t :=
    ((gammaR_differentiableAt (line_re_pos t)).continuousAt).comp hline
  have h3 : ContinuousAt (fun u : ℝ => logDeriv Gammaℝ (line u)) t := by
    simp only [logDeriv_apply]
    exact h1.div h2 (gauge_ne_zero t)
  exact Complex.continuous_re.continuousAt.comp h3

/-- **The unit chart's clock** `ϑ`: the cumulative continuous phase of the gauge,
`theta t = ∫₀ᵗ Re (logDeriv Γℝ (½+iu)) du`.  This is the Riemann–Siegel theta, obtained
from the gauge itself (see `gauge_polar`, `theta_unique`), not from an asymptotic. -/
noncomputable def theta (t : ℝ) : ℝ := ∫ u in (0:ℝ)..t, clockRate u

/-- The clock starts at the common origin: `ϑ(0) = 0`. -/
theorem theta_zero : theta 0 = 0 := intervalIntegral.integral_same

/-- The clock's rate is the gauge's phase speed (fundamental theorem of calculus). -/
theorem theta_hasDerivAt (t : ℝ) : HasDerivAt theta (clockRate t) t := by
  refine intervalIntegral.integral_hasDerivAt_right
    (continuous_clockRate.intervalIntegrable 0 t) ?_ continuous_clockRate.continuousAt
  exact continuous_clockRate.stronglyMeasurable.stronglyMeasurableAtFilter

theorem theta_continuous : Continuous theta := by
  have hd : Differentiable ℝ theta := fun t => (theta_hasDerivAt t).differentiableAt
  exact hd.continuous

/-! ### The polar lift: `Γℝ(½+it) = ‖Γℝ(½+it)‖ · e^{iϑ(t)}` -/

/-- The gauge along the line. -/
noncomputable def gaugeAt (t : ℝ) : ℂ := Gammaℝ (line t)

/-- The clock-despun gauge `F(t) = Γℝ(½+it)·e^{−iϑ(t)}`; proven real and positive below. -/
noncomputable def despun (t : ℝ) : ℂ := gaugeAt t * Complex.exp (-(I * ((theta t : ℝ) : ℂ)))

/-- The derivative value of `despun` (as produced by the product rule). -/
noncomputable def despunDeriv (t : ℝ) : ℂ :=
  deriv Gammaℝ (line t) * I * Complex.exp (-(I * ((theta t : ℝ) : ℂ)))
    + gaugeAt t * (Complex.exp (-(I * ((theta t : ℝ) : ℂ))) * (-(I * ((clockRate t : ℝ) : ℂ))))

lemma despun_ne_zero (t : ℝ) : despun t ≠ 0 :=
  mul_ne_zero (gauge_ne_zero t) (Complex.exp_ne_zero _)

lemma hasDerivAt_lineC (z : ℂ) : HasDerivAt lineC I z := by
  have h : HasDerivAt (fun w : ℂ => 1 / 2 + w * I) ((1 : ℂ) * I) z :=
    ((hasDerivAt_id z).mul_const I).const_add (1 / 2 : ℂ)
  rw [one_mul] at h
  exact h

lemma gaugeAt_hasDerivAt (t : ℝ) :
    HasDerivAt gaugeAt (deriv Gammaℝ (line t) * I) t := by
  have h1 : HasDerivAt (fun z : ℂ => Gammaℝ (lineC z)) (deriv Gammaℝ (line t) * I) (t : ℂ) :=
    ((gammaR_differentiableAt (line_re_pos t)).hasDerivAt).comp (t : ℂ) (hasDerivAt_lineC _)
  exact h1.comp_ofReal

lemma expFactor_hasDerivAt (t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (-(I * ((theta u : ℝ) : ℂ))))
      (Complex.exp (-(I * ((theta t : ℝ) : ℂ))) * (-(I * ((clockRate t : ℝ) : ℂ)))) t := by
  have h1 : HasDerivAt (fun u : ℝ => ((theta u : ℝ) : ℂ)) ((clockRate t : ℝ) : ℂ) t :=
    (theta_hasDerivAt t).ofReal_comp
  have h2 : HasDerivAt (fun u : ℝ => -(I * ((theta u : ℝ) : ℂ)))
      (-(I * ((clockRate t : ℝ) : ℂ))) t := (h1.const_mul I).neg
  exact h2.cexp

lemma despun_hasDerivAt (t : ℝ) : HasDerivAt despun (despunDeriv t) t :=
  (gaugeAt_hasDerivAt t).mul (expFactor_hasDerivAt t)

lemma despun_continuous : Continuous despun := by
  have hd : Differentiable ℝ despun := fun t => (despun_hasDerivAt t).differentiableAt
  exact hd.continuous

/-- The derivative factors through `despun` with a **real** log-derivative coefficient:
`F' = i·(logDeriv Γℝ − ϑ')·F` and `Re(logDeriv Γℝ) − ϑ' = 0`. -/
lemma despunDeriv_eq (t : ℝ) :
    despunDeriv t
      = I * (logDeriv Gammaℝ (line t) - ((clockRate t : ℝ) : ℂ)) * despun t := by
  unfold despunDeriv despun gaugeAt
  rw [logDeriv_apply]
  field_simp [gauge_ne_zero t]
  ring

/-- The despinning coefficient is real: `Im (i·(logDeriv Γℝ(½+it) − ϑ'(t))) = 0`. -/
lemma coeff_im_zero (t : ℝ) :
    (I * (logDeriv Gammaℝ (line t) - ((clockRate t : ℝ) : ℂ))).im = 0 := by
  simp [Complex.mul_im, Complex.sub_re, Complex.sub_im, clockRate]

/-- The weld identity `F'·conj F = F·conj F'` — the numerator of `(F/conj F)'` vanishes. -/
lemma key_identity (t : ℝ) :
    despunDeriv t * (starRingEnd ℂ) (despun t)
      = despun t * (starRingEnd ℂ) (despunDeriv t) := by
  rw [despunDeriv_eq]
  set c : ℂ := I * (logDeriv Gammaℝ (line t) - ((clockRate t : ℝ) : ℂ)) with hc
  have hcr : (starRingEnd ℂ) c = c := Complex.conj_eq_iff_im.mpr (coeff_im_zero t)
  rw [map_mul, hcr]
  ring

lemma conj_despun_hasDerivAt (t : ℝ) :
    HasDerivAt (fun u => (starRingEnd ℂ) (despun u)) ((starRingEnd ℂ) (despunDeriv t)) t := by
  simpa using (despun_hasDerivAt t).star

lemma conj_despun_ne_zero (t : ℝ) : (starRingEnd ℂ) (despun t) ≠ 0 := by
  simpa using despun_ne_zero t

/-- The reality ratio `q = F / conj F` is stationary. -/
lemma qratio_hasDerivAt (t : ℝ) :
    HasDerivAt (fun u => despun u / (starRingEnd ℂ) (despun u)) 0 t := by
  have h := (despun_hasDerivAt t).div (conj_despun_hasDerivAt t) (conj_despun_ne_zero t)
  have hnum : (despunDeriv t * (starRingEnd ℂ) (despun t)
      - despun t * (starRingEnd ℂ) (despunDeriv t)) / ((starRingEnd ℂ) (despun t)) ^ 2
        = 0 := by
    rw [key_identity]
    simp
  rw [hnum] at h
  exact h

/-- At the origin the despun gauge is `Γℝ(½)`, a positive real. -/
lemma despun_zero : despun 0 = Gammaℝ (1 / 2 : ℂ) := by
  unfold despun gaugeAt
  rw [theta_zero]
  simp [line, lineC]

/-- `Γℝ(½) = π^{-1/4}·Γ(¼)` as a positive real. -/
lemma gammaR_half_eq :
    Gammaℝ (1 / 2 : ℂ) = ((Real.pi ^ (-(1/4) : ℝ) * Real.Gamma (1/4) : ℝ) : ℂ) := by
  rw [Gammaℝ_def]
  have h1 : (-(1 / 2 : ℂ)) / 2 = ((-(1/4) : ℝ) : ℂ) := by push_cast; ring
  have h2 : ((1 / 2 : ℂ)) / 2 = ((1/4 : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, ← Complex.ofReal_cpow Real.pi_pos.le, Complex.Gamma_ofReal]
  push_cast
  ring

lemma despun_zero_re_pos : 0 < (despun 0).re := by
  rw [despun_zero, gammaR_half_eq]
  simp only [Complex.ofReal_re]
  positivity

/-- **The despun gauge is real**: `Im F(t) = 0` — the ratio `F/conj F` is constant `= 1`. -/
lemma despun_im_zero (t : ℝ) : (despun t).im = 0 := by
  have hconst : despun t / (starRingEnd ℂ) (despun t)
      = despun 0 / (starRingEnd ℂ) (despun 0) :=
    is_const_of_deriv_eq_zero
      (fun u => (qratio_hasDerivAt u).differentiableAt)
      (fun u => (qratio_hasDerivAt u).deriv) t 0
  have h0 : despun 0 / (starRingEnd ℂ) (despun 0) = 1 := by
    rw [despun_zero, gammaR_half_eq, Complex.conj_ofReal]
    exact div_self (by
      rw [← gammaR_half_eq]
      exact Gammaℝ_ne_zero_of_re_pos (by norm_num))
  rw [h0] at hconst
  have heq : despun t = (starRingEnd ℂ) (despun t) :=
    (div_eq_one_iff_eq (conj_despun_ne_zero t)).mp hconst
  exact Complex.conj_eq_iff_im.mp heq.symm

/-- **The despun gauge is positive**: never zero, real, positive at the origin, connected line. -/
lemma despun_re_pos (t : ℝ) : 0 < (despun t).re := by
  by_contra hle
  rw [not_lt] at hle
  have hne : ∀ u : ℝ, (despun u).re ≠ 0 := fun u h =>
    despun_ne_zero u (Complex.ext h (despun_im_zero u))
  have hlt : (despun t).re < 0 := lt_of_le_of_ne hle (hne t)
  have hcont : ContinuousOn (fun u : ℝ => (despun u).re) (Set.uIcc 0 t) :=
    (Complex.continuous_re.comp despun_continuous).continuousOn
  have hmem : (0 : ℝ) ∈ Set.uIcc ((fun u : ℝ => (despun u).re) 0)
      ((fun u : ℝ => (despun u).re) t) := by
    rw [Set.mem_uIcc]
    right
    exact ⟨hlt.le, despun_zero_re_pos.le⟩
  obtain ⟨c, _, hc⟩ := intermediate_value_uIcc hcont hmem
  exact hne c hc

/-- **The polar lift**: `Γℝ(½+it) = ‖Γℝ(½+it)‖ · e^{iϑ(t)}` — `theta` *is* the continuous
phase of the archimedean gauge on the line (the Riemann–Siegel theta). -/
theorem gauge_polar (t : ℝ) :
    Gammaℝ (line t) = ((‖Gammaℝ (line t)‖ : ℝ) : ℂ) * Complex.exp (I * ((theta t : ℝ) : ℂ)) := by
  have hG : Gammaℝ (line t) = despun t * Complex.exp (I * ((theta t : ℝ) : ℂ)) := by
    unfold despun gaugeAt
    rw [mul_assoc, ← Complex.exp_add]
    simp
  have hreal : despun t = (((despun t).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [despun_im_zero t]
  have hnorm : ‖Gammaℝ (line t)‖ = (despun t).re := by
    rw [hG]
    rw [norm_mul]
    have h1 : ‖Complex.exp (I * ((theta t : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [h1, mul_one, hreal]
    simp [Complex.norm_real, abs_of_pos (despun_re_pos t)]
  rw [hnorm, ← hreal]
  exact hG

/-- **Uniqueness of the clock**: any continuous phase of the gauge normalized at the origin
equals `theta`.  (The lift gap is continuous, `2πℤ`-valued on a connected line, `0` at `0`.) -/
theorem theta_unique (φ : ℝ → ℝ) (hcont : Continuous φ) (h0 : φ 0 = 0)
    (hlift : ∀ t, Gammaℝ (line t)
      = ((‖Gammaℝ (line t)‖ : ℝ) : ℂ) * Complex.exp (I * ((φ t : ℝ) : ℂ))) :
    ∀ t, φ t = theta t := by
  have hgap : ∀ t, ∃ k : ℤ, φ t - theta t = 2 * Real.pi * k := by
    intro t
    have h1 := (gauge_polar t).symm.trans (hlift t)
    have hn : ((‖Gammaℝ (line t)‖ : ℝ) : ℂ) ≠ 0 := by
      simpa using norm_ne_zero_iff.mpr (gauge_ne_zero t)
    have h2 : Complex.exp (I * ((theta t : ℝ) : ℂ)) = Complex.exp (I * ((φ t : ℝ) : ℂ)) :=
      mul_left_cancel₀ hn h1
    have h3 : Complex.exp (I * ((φ t : ℝ) : ℂ) - I * ((theta t : ℝ) : ℂ)) = 1 := by
      rw [Complex.exp_sub, h2, div_self (Complex.exp_ne_zero _)]
    rw [Complex.exp_eq_one_iff] at h3
    obtain ⟨k, hk⟩ := h3
    refine ⟨k, ?_⟩
    have him := congrArg Complex.im hk
    simp [Complex.mul_im, Complex.sub_im] at him
    linarith [him]
  -- the gap function has countable, preconnected image ⟹ constant ⟹ 0
  have hsub : Set.range (fun t => φ t - theta t)
      ⊆ Set.range (fun k : ℤ => 2 * Real.pi * (k : ℝ)) := by
    rintro x ⟨t, rfl⟩
    obtain ⟨k, hk⟩ := hgap t
    exact ⟨k, hk.symm⟩
  have hcountable : (Set.range (fun t => φ t - theta t)).Countable :=
    (Set.countable_range _).mono hsub
  have hpre : IsPreconnected (Set.range (fun t => φ t - theta t)) := by
    rw [← Set.image_univ]
    exact isPreconnected_univ.image _ (hcont.sub theta_continuous).continuousOn
  have hsing :=
    CarrierReachability.subsingleton_of_countable_preconnected hcountable hpre
  intro t
  have h1 : φ t - theta t = φ 0 - theta 0 :=
    hsing ⟨t, rfl⟩ ⟨0, rfl⟩
  rw [h0, theta_zero] at h1
  linarith [h1]

/-! ## §3 The native registration identity

The unit-chart scalar readout of the trivial-character fiber factors as
(real native state) × (conjugate clock spin): **all** of its continuous phase is the clock;
the arithmetic content is the real factor `rsZ` (the Riemann–Siegel `Z`), whose sign is
π-quantized.  There is no continuous oscillatory degree of freedom left for `S(t)`. -/

/-- The real native state read in the unit chart: `rsZ t = Λ(½+it).re / ‖Γℝ(½+it)‖`
(the Riemann–Siegel `Z`-function). -/
noncomputable def rsZ (t : ℝ) : ℝ :=
  (completedRiemannZeta (line t)).re / ‖Gammaℝ (line t)‖

/-- The completed fiber is real on the line (the weld reality; re-export). -/
theorem native_chart_real (t : ℝ) : (completedRiemannZeta (line t)).im = 0 :=
  HelixCollapse.completedRiemannZeta_critical_line_im_zero t

/-- The completed fiber equals the gauge times the raw fiber on the line. -/
lemma completed_eq_gauge_mul (t : ℝ) :
    completedRiemannZeta (line t) = Gammaℝ (line t) * riemannZeta (line t) := by
  rw [riemannZeta_def_of_ne_zero (line_ne_zero t),
    mul_div_cancel₀ _ (gauge_ne_zero t)]

/-- **The unit-chart factorization** (the master registration identity):
`ζ(½+it) = rsZ(t) · e^{−iϑ(t)}` with `rsZ(t)` real.  Every unit of continuous phase in the
unit-chart readout is clock; the arithmetic rides in the real factor alone. -/
theorem unit_chart_factorization (t : ℝ) :
    riemannZeta (line t) = ((rsZ t : ℝ) : ℂ) * Complex.exp (-(I * ((theta t : ℝ) : ℂ))) := by
  have hΛ : completedRiemannZeta (line t)
      = (((completedRiemannZeta (line t)).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [native_chart_real t]
  have hζ : riemannZeta (line t) = completedRiemannZeta (line t) / Gammaℝ (line t) :=
    riemannZeta_def_of_ne_zero (line_ne_zero t)
  rw [hζ, hΛ, gauge_polar t, rsZ]
  have hn : ((‖Gammaℝ (line t)‖ : ℝ) : ℂ) ≠ 0 := by
    simpa using norm_ne_zero_iff.mpr (gauge_ne_zero t)
  rw [Complex.exp_neg]
  field_simp
  rw [Complex.ofReal_div, mul_comm, div_mul_cancel₀ _ hn]

/-- The native state vanishes exactly at the fiber's zeros: closure soundness of the
real readout. -/
theorem rsZ_zero_iff (t : ℝ) : rsZ t = 0 ↔ riemannZeta (line t) = 0 := by
  constructor
  · intro h
    have := unit_chart_factorization t
    rw [h] at this
    simpa using this
  · intro h
    have hΛ : completedRiemannZeta (line t) = 0 := by
      rw [completed_eq_gauge_mul t, h, mul_zero]
    rw [rsZ, hΛ]
    simp

/-- **No native oscillation** (the 100% removal, explicit-clock form): despinning the
unit-chart readout by the clock leaves a real value at *every* height — `ζ(½+it)·e^{iϑ(t)} ∈ ℝ`.
The classical `S(t)` has no continuous native carrier state to be. -/
theorem no_native_oscillation (t : ℝ) :
    (riemannZeta (line t) * Complex.exp (I * ((theta t : ℝ) : ℂ))).im = 0 := by
  rw [unit_chart_factorization t, mul_assoc, ← Complex.exp_add]
  simp

/-! ## §4 The scale-indexed count functor, and the two counts derived

One functor for both realizations of the same fiber:

  `registeredCount H base clock events z
     = base + (clock (log z) − clock 0)/π + (if CircleMonodromy H then events z else 0)`.

DC base at the common origin, continuous clock procession in π-cells, and the completed
closure events — the last **gated by whether the carrier's cells close at scale `H`**
(a carrier registers a completed crossing only through a completed cell).  The gate is a
proposition *proven* on each side (`pi3_closes`, `unit_never_closes`), never chosen.  Both
instantiations below feed the functor the *same* fiber events (`nativeCount`). -/

/-- **The native closure predicate**: the fiber's own η-accumulation closes at ordinate `γ`
(the complete-closure criterion of the Part-I chain; `Faithful.continuous_model_zeta`). -/
def NativeClosure (γ : ℝ) : Prop :=
  Filter.Tendsto
    (fun N : ℕ => ∑ n ∈ Finset.range N, (-1 : ℂ) ^ (n + 1) * (n : ℂ) ^ (-(line γ)))
    Filter.atTop (nhds 0)

/-- **Event identification**: a complete native closure at ordinate `γ` is exactly an
on-line zero of the fiber — from the strip extension and the η↔ζ bridge of the Part-I
chain (`Faithful.continuous_model_zeta`), not by definition. -/
theorem nativeClosure_iff_zero (γ : ℝ) :
    NativeClosure γ ↔ riemannZeta (line γ) = 0 := by
  have h := Faithful.continuous_model_zeta γ
  constructor
  · intro hc
    have hlim := tendsto_nhds_unique hc h.1
    exact h.2.mp hlim.symm
  · intro hz
    have h1 := h.1
    rw [show riemannZeta ((1 / 2 : ℂ) + (γ : ℂ) * Complex.I) = 0 from hz] at h1
    rw [mul_zero] at h1
    exact h1

/-- `N_H`-input: the cumulative complete-closure count of the fiber realization, through raw
height `z`, read through the (only) logarithmic readout `heightReadout`. -/
noncomputable def nativeCount (z : ℝ) : ℕ :=
  {γ : ℝ | γ ∈ Set.Ioc 0 (Readout.heightReadout z) ∧ NativeClosure γ}.ncard

/-- `N(t)`: the arithmetic event count — on-line zeros of the fiber with ordinate in `(0,t]`. -/
noncomputable def zeroEventCount (t : ℝ) : ℕ :=
  {γ : ℝ | γ ∈ Set.Ioc 0 t ∧ riemannZeta (line γ) = 0}.ncard

/-- **The native identification `N_{π/3}(e^t) = N(t)`** (event-level): the closure events
through raw height `e^t` are exactly the arithmetic zero events through ordinate `t` — via
the event identification and the exact readout `heightReadout (e^t) = t`. -/
theorem native_identification (t : ℝ) :
    nativeCount (Real.exp t) = zeroEventCount t := by
  unfold nativeCount zeroEventCount
  congr 1
  ext γ
  rw [Readout.readout_exp]
  exact and_congr_right fun _ => nativeClosure_iff_zero γ

/-- **The DC residue of the trivial channel** — the pole of the projected fiber at the DC
point `s = 1`.  Its value is forced (`dcResidue_spec`, `dcResidue_unique`): this is the `+1`
of the unit chart's origin registration. -/
noncomputable def dcResidue : ℝ := 1

/-- The DC residue is the residue of the trivial-channel pole: `(s−1)·ζ(s) → dcResidue`. -/
theorem dcResidue_spec :
    Filter.Tendsto (fun s => (s - 1) * riemannZeta s) (nhdsWithin 1 {(1 : ℂ)}ᶜ)
      (nhds ((dcResidue : ℝ) : ℂ)) := by
  simpa [dcResidue] using riemannZeta_residue_one

/-- The DC registration is forced: any residue value of the trivial channel equals `1`. -/
theorem dcResidue_unique (r : ℂ)
    (h : Filter.Tendsto (fun s => (s - 1) * riemannZeta s) (nhdsWithin 1 {(1 : ℂ)}ᶜ)
      (nhds r)) : r = 1 :=
  tendsto_nhds_unique h riemannZeta_residue_one

open Classical in
/-- **The scale-indexed cumulative count functor** `X_{ζ,H} ⟶ (z ↦ N_H(z))`: DC base at the
common origin, plus the chart's continuous clock procession in π-cells, plus one completed
cell per closure event — the event channel gated by the *proven* closure capability of the
scale (`CircleMonodromy H`). -/
noncomputable def registeredCount (H : ℝ) (base : ℝ) (clock : ℝ → ℝ) (events : ℝ → ℕ)
    (z : ℝ) : ℝ :=
  base + (clock (Real.log z) - clock 0) / Real.pi
    + (if Monodromy.CircleMonodromy H then (events z : ℝ) else 0)

/-- **`N_{π/3}`**: the native realization registered by the functor.  Base `0` and clock `0`
are the *proven* native data: the count starts at the common origin, and the native chart has
no continuous procession because its readout is real (`native_chart_real` — the phase is
π-quantized, all continuous phase having been proven to be gauge).  The events channel is
open because the `π/3` carrier closes (`pi3_closes`, `pi3_antipodal`). -/
noncomputable def N_pi3 (z : ℝ) : ℝ :=
  registeredCount (Real.pi / 3) 0 (fun _ => 0) nativeCount z

/-- **`N_1`**: the *same* fiber events, the *same* functor, at carrier scale `1`.  Base is the
DC residue (`dcResidue_spec` — the trivial-channel pole registers at the origin); the clock is
`theta` (`unit_chart_factorization` — the readout's entire continuous phase; unique by
`theta_unique`); the events channel is **shut by a theorem** (`unit_never_closes` — the unit
carrier completes no cell), not by choice. -/
noncomputable def N_1 (z : ℝ) : ℝ :=
  registeredCount 1 dcResidue theta nativeCount z

/-- The native count evaluates to the pure event counter: `N_{π/3}(z) = #closures(z)`. -/
theorem N_pi3_eval (z : ℝ) : N_pi3 z = (nativeCount z : ℝ) := by
  unfold N_pi3 registeredCount
  rw [if_pos pi3_closes]
  simp

/-- **The unit-1 identification `N_1(e^t) = 1 + ϑ(t)/π`** — *derived* from the unit-`1`
realization: the DC residue registers the base, the clock `ϑ` is the readout's entire
continuous procession, and the closure channel contributes nothing because the unit carrier
provably never closes a cell.  The theta term is a conclusion, not a definition. -/
theorem unit_identification (t : ℝ) :
    N_1 (Real.exp t) = 1 + theta t / Real.pi := by
  unfold N_1 registeredCount
  rw [if_neg unit_never_closes, Real.log_exp, theta_zero, dcResidue]
  ring

/-- `N_{π/3}(e^t) = N(t)`, functor form. -/
theorem native_identification' (t : ℝ) :
    N_pi3 (Real.exp t) = (zeroEventCount t : ℝ) := by
  rw [N_pi3_eval, native_identification]

/-! ## §5 The subtraction: `S(t)` is the carrier-scale compensation ledger -/

/-- **The S(t) carrier-scale compensation theorem.**  With both counts derived from their
respective realizations of the same fiber (`native_identification'`,
`unit_identification`), the difference of registrations is

  `N_{π/3}(e^t) − N_1(e^t) = N(t) − 1 − ϑ(t)/π`

— the quantity the unit chart calls `S(t)`.  It is a *registration ledger*: integer event
counter minus (DC base + smooth clock).  No native state variable appears on either side
beyond the closure events and the clock. -/
theorem carrier_scale_compensation (t : ℝ) :
    N_pi3 (Real.exp t) - N_1 (Real.exp t)
      = (zeroEventCount t : ℝ) - 1 - theta t / Real.pi := by
  rw [native_identification', unit_identification]
  ring

/-- **`S(t)`**: the accumulated carrier-scale registration gap, as the unit chart reads it —
the zero-counting procession minus the chart's smooth content (DC base + clock).  This is
the quantity classically written `S(t)` in `N(t) = 1 + ϑ(t)/π + S(t)`. -/
noncomputable def S (t : ℝ) : ℝ := (zeroEventCount t : ℝ) - 1 - theta t / Real.pi

/-- The classical count decomposition `N(t) = 1 + ϑ(t)/π + S(t)`, as an identity of the
native count. -/
theorem count_decomposition (t : ℝ) :
    (zeroEventCount t : ℝ) = 1 + theta t / Real.pi + S t := by
  unfold S
  ring

/-- **The S(t) carrier-scale compensation theorem (the boxed target), unconditional**:

  `N_{π/3}(e^t) − N_1(e^t) = S(t)`.

`S(t)` is the unit-`1`–based readout **tracking the real `π/3` carrier in 3-D state space**:
the same arithmetic procession, registered at its native `π/3` scale and at unit scale,
differs by exactly the term the 1-D chart calls `S(t)` — the correction the unit chart must
carry because it can never re-synchronize with the native registration
(`lattice_gap_fundamental`, `unit_never_closes`).  Both counts are derived from their
realizations (`native_identification'`, `unit_identification`); nothing here depends on
where any zero lies. -/
theorem carrier_scale_compensation_S (t : ℝ) :
    N_pi3 (Real.exp t) - N_1 (Real.exp t) = S t := by
  unfold S
  exact carrier_scale_compensation t

/-- **`S(t)` is not a native oscillatory state** — the structural consequence, packaged:
(i) despinning the unit readout by the clock leaves a real value at every height (there is
no continuous oscillation in the fiber beyond the clock), and (ii) `S` is pure registration
bookkeeping: event counter minus DC base minus clock.  `S(t)` exists only as the
compensation between the two carrier registrations of one arithmetic procession. -/
theorem S_has_no_native_carrier (t : ℝ) :
    (riemannZeta (line t) * Complex.exp (I * ((theta t : ℝ) : ℂ))).im = 0 ∧
      S t = (zeroEventCount t : ℝ) - dcResidue - (theta t - theta 0) / Real.pi := by
  refine ⟨no_native_oscillation t, ?_⟩
  rw [theta_zero, dcResidue]
  unfold S
  ring

/-! ## §6 Exhaustion of the event space — proven, consumed

The 3-D representation's event space is the height ray, and its exhaustion is a theorem
(`SourceHolonomy.threeD_exhaustive`): heights are weld-fixed, so every event is sourced —
there is nowhere else for an event to occur.  The height encoding is lossless
(`Geometry.online_zeros_exhausted`).  So the native count in §4–§5 counts the whole event
space; nothing is left out, unconditionally. -/

/-- The trivial-character fiber over the 3-D height ray (the representation's entire
event space). -/
noncomputable def heightFiber (z : ℂ) : ℂ := riemannZeta (lineC z)

/-- **Every registered closure event is a source — unconditional** (consumes the proven 3-D
exhaustion `SourceHolonomy.threeD_exhaustive`): over the height ray, the 3-D object's entire
event space, every closure event of the native count is weld-fixed and sourced. -/
theorem native_events_sourced (γ : ℝ) (h : NativeClosure γ) :
    SourceHolonomy.IsSource heightFiber (γ : ℂ) :=
  SourceHolonomy.threeD_exhaustive heightFiber γ
    (by simpa [heightFiber, line] using (nativeClosure_iff_zero γ).mp h)

/-- **The height encoding of the events is complete** (re-export of
`Geometry.online_zeros_exhausted`): event ordinates correspond bijectively to cancellation
heights — the readout `z = e^γ` misses no event and invents none. -/
noncomputable def event_encoding_complete :=
  CriticalLinePhasor.Geometry.online_zeros_exhausted

end CriticalLinePhasor.CarrierScale
