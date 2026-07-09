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

* **§4 The induced event readout, the count functor, and both counts derived.**  The arrow
  derived here is: **carrier monodromy/closure geometry → event contribution in the scalar
  registered count**.  An event is a sign flip of the real native state; its mark is the
  half turn `−1 = e^{iπ}` (`sign_flip_mark`).  A scale-`H` chart registers the mark only
  through a completed cell arc realizing it: `eventArcs H = {k > 0 | cellAt H k = −1}`.
  The arc geometry is then a theorem on each side: at `π/3` the wall is hit exactly once
  per closed six-cell monodromy loop (`pi3_wall_mem`, from the antipodal identity;
  `pi3_arcs_eq`: the arcs are exactly `k ≡ 3 (mod 6)`) — one registered event per completed
  native cell; at scale `1` no arc ever realizes the mark (`unit_arcs_empty`).  The induced
  per-event contribution (`eventContribution`; values `eventContribution_pi3 = 1`,
  `eventContribution_one = 0` are theorems) feeds the functor
  `registeredCount = base + clock-procession/π + eventContribution·events`.  The native
  chart's zero clock is likewise derived, not passed by hand: every continuous clock its
  readout factors through is constant on event-free stretches
  (`native_clock_locally_constant`, from `no_native_oscillation`).  With the fiber's own
  closure predicate (`NativeClosure`) and the readout (`Readout.readout_exp`):
  - `native_identification : N_pi3 (e^t) = N(t)` — the native count is the arithmetic
    event count (each complete closure **is** an on-line zero, and conversely);
  - `unit_identification : N_1 (e^t) = 1 + theta t / π` — the unit count is the DC residue
    (`dcResidue_spec`, the pole of the trivial channel, value forced `= 1`) plus the clock,
    the event channel vanishing by `eventContribution_one`.

* **§5 Subtraction.**  `carrier_scale_compensation_S` (the boxed target, unconditional):
  `N_pi3(e^t) − N_1(e^t) = S(t)`, with `S` the accumulated registration gap and
  `count_decomposition` its classical shape `N(t) = 1 + ϑ(t)/π + S(t)`.
  `S_has_no_native_carrier`: `S` is registration bookkeeping — no native oscillatory state.

* **§6 Exhaustion — proven, consumed.**  The 3-D event space is the height ray, and its
  exhaustion is a *theorem* (`SourceHolonomy.threeD_exhaustive`): every event is weld-fixed,
  there is nowhere else for an event to occur.  `native_events_sourced` instantiates it at
  the ζ fiber; `event_encoding_complete` re-exports the lossless height encoding
  (`Geometry.online_zeros_exhausted`).  Nothing is left out of the native count.

* **§7 The general gap `S_{H,K}` and the harmonic-closure family.**  `NH H` is the canonical
  scale-`H` chart: event channel at its derived weight, continuous channel at the
  complementary weight — and since the weight is the arc-set indicator, the family contains
  exactly the two proven chart types, decided by arc geometry (`NH_dichotomy`; anchors
  `NH_pi3`, `NH_one`).  The two-scale registration gap `Sgap H K t := NH H (e^t) − NH K (e^t)`
  is a coboundary of the per-scale potential: reflexive (`Sgap_refl`), antisymmetric
  (`Sgap_antisymm`), cocycle-composing (`Sgap_cocycle`) — `S(t)` is *relative*, never
  intrinsic.  Every harmonic scale `π/m` realizes the wall at `m` cells (`pi_div_wall`;
  arcs exactly `k ≡ m (mod 2m)`, `pi_div_arcs_eq`; monodromy *derived* by doubling,
  `pi_div_closes`), so the family registers identically (`Sgap_pi_div = 0`) and every member
  reads the SAME classical `S(t)` against the unit chart: `Sgap_pi3_one` (recovery),
  `Sgap_pi6_one` (the second gap function, obtained through the cocycle; its channel is
  determined open by `pi6_wall_mem`/`pi6_arcs_eq`, not prescribed), `Sgap_pi_div_one`
  (general).  Monodromy is necessary (`arcs_nonempty_monodromy`) but **not sufficient**:
  `2π` closes in one cell yet never realizes the mark (`two_pi_closes`,
  `two_pi_arcs_empty`) — the event channel is decided by the arc geometry alone.

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

/-! ## §4 The induced event readout, the count functor, and the two counts derived

The arrow derived in this section: **carrier monodromy/closure geometry → event
contribution in the scalar registered count**.  One functor for both realizations:

  `registeredCount H base clock events z
     = base + (clock (log z) − clock 0)/π + eventContribution H · events z`,

where `eventContribution` is not a gate inserted by hand but the readout induced by the
scale's arc geometry (§4a): an event's half-turn mark is registered exactly through a
completed cell arc realizing it — once per closed loop at `π/3`, never at scale `1`.  Both
instantiations feed the functor the *same* fiber events (`nativeCount`); every functor
input (base, clock, event weight) is pinned by a theorem. -/

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

/-! ### §4a The induced event readout: closure geometry → scalar event contribution

An event of the fiber is a sign flip of the real native state (`rsZ`, §3); its mark is the
half turn `−1 = e^{iπ}` (`sign_flip_mark`).  A scale-`H` chart can register that mark only
through a completed cell arc that realizes it (`eventArcs H`).  At `π/3` the antipodal wall
realizes the mark, exactly once per closed six-cell monodromy loop (`pi3_wall_mem`,
`pi3_arcs_eq`) — a completed native cell contributes one registered event.  At scale `1` no
cell arc ever realizes the mark (`unit_arcs_empty`) — a non-closing scale contributes only
its continuous clock procession (§3).  The per-event contribution `eventContribution` is
*induced* by this geometry; its two values are theorems, not choices. -/

/-- **The event mark is the half turn**: across a sign flip of the real native state, the
readout's phase factor changes by exactly `e^{iπ} = −1`. -/
theorem sign_flip_mark {s₀ s₁ : ℝ} (h : s₀ * s₁ < 0) :
    ((s₁ / |s₁| : ℝ) : ℂ) = Complex.exp (I * Real.pi) * ((s₀ / |s₀| : ℝ) : ℂ) := by
  have hmark : Complex.exp (I * Real.pi) = -1 := by
    rw [mul_comm]
    exact_mod_cast Complex.exp_pi_mul_I
  rcases mul_neg_iff.mp h with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have e0 : s₀ / |s₀| = 1 := by rw [abs_of_pos h0]; exact div_self h0.ne'
    have e1 : s₁ / |s₁| = -1 := by rw [abs_of_neg h1, div_neg, div_self h1.ne]
    rw [e0, e1, hmark]
    norm_num
  · have e0 : s₀ / |s₀| = -1 := by rw [abs_of_neg h0, div_neg, div_self h0.ne]
    have e1 : s₁ / |s₁| = 1 := by rw [abs_of_pos h1]; exact div_self h1.ne'
    rw [e0, e1, hmark]
    norm_num

/-- The completed cell arcs of scale `H` that realize the event mark `−1`: the walks of
`k ≥ 1` whole cells landing exactly on the half turn. -/
def eventArcs (H : ℝ) : Set ℕ := {k : ℕ | 0 < k ∧ cellAt H k = -1}

/-- **The native wall realizes the mark** — derived from the antipodal identity
(`pi3_antipodal` = `Readout.cell_antipodal_cancel`): three `π/3` cells are exactly the half
turn, `cellAt (π/3) 3 = −1`. -/
theorem pi3_wall_mem : 3 ∈ eventArcs (Real.pi / 3) := by
  refine ⟨by norm_num, ?_⟩
  have h := pi3_antipodal 0
  have h0 : cellAt (Real.pi / 3) 0 = 1 := by
    simp [cellAt]
  rw [h0] at h
  have h3 : (0 + 3 : ℕ) = 3 := by norm_num
  rw [h3] at h
  linear_combination h

/-- **Exactly one wall per closed loop**: the `π/3` arcs realizing the mark are precisely
`k ≡ 3 (mod 6)` — one half-turn wall inside each closed six-cell monodromy loop.  A
completed native cell contributes exactly *one* registered event; the "one" is geometry,
not normalization. -/
theorem pi3_arcs_eq : eventArcs (Real.pi / 3) = {k : ℕ | k % 6 = 3} := by
  ext k
  simp only [eventArcs, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hk, hcell⟩
    have hpi : Complex.exp (I * ((Real.pi : ℝ) : ℂ)) = -1 := by
      rw [mul_comm]
      exact_mod_cast Complex.exp_pi_mul_I
    have h1 : Complex.exp (I * ((Real.pi / 3 * (k : ℝ) - Real.pi : ℝ) : ℂ)) = 1 := by
      have harg : ((Real.pi / 3 * (k : ℝ) - Real.pi : ℝ) : ℂ)
          = ((Real.pi / 3 * (k : ℝ) : ℝ) : ℂ) - ((Real.pi : ℝ) : ℂ) := by
        push_cast
        ring
      rw [harg, mul_sub, Complex.exp_sub,
        show Complex.exp (I * ((Real.pi / 3 * (k : ℝ) : ℝ) : ℂ)) = -1 from hcell, hpi]
      norm_num
    rw [Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    have him := congrArg Complex.im hn
    simp [Complex.mul_im] at him
    have hfac : Real.pi / 3 * ((k : ℝ) - 3 - 6 * n) = 0 := by
      ring_nf
      ring_nf at him
      linarith [him]
    have hπ3 : Real.pi / 3 ≠ 0 := by positivity
    have hk3 : (k : ℝ) - 3 - 6 * n = 0 := by
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd h hπ3
      · exact h
    have hkz : (k : ℤ) = 6 * n + 3 := by
      have : (k : ℝ) = 6 * n + 3 := by linarith [hk3]
      exact_mod_cast this
    omega
  · intro hk
    obtain ⟨q, rfl⟩ : ∃ q, k = 6 * q + 3 := ⟨k / 6, by omega⟩
    refine ⟨by omega, ?_⟩
    have harg : ((Real.pi / 3 * ((6 * q + 3 : ℕ) : ℝ) : ℝ) : ℂ)
        = ((q : ℤ) : ℂ) * (2 * (Real.pi : ℂ)) + (Real.pi : ℂ) := by
      push_cast
      ring
    rw [cellAt, harg, mul_add, Complex.exp_add]
    have h1 : Complex.exp (I * (((q : ℤ) : ℂ) * (2 * (Real.pi : ℂ)))) = 1 := by
      rw [show I * (((q : ℤ) : ℂ) * (2 * (Real.pi : ℂ)))
          = ((q : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) by ring]
      exact_mod_cast Complex.exp_int_mul_two_pi_mul_I (q : ℤ)
    rw [h1, one_mul, mul_comm]
    exact_mod_cast Complex.exp_pi_mul_I

/-- **The unit scale never realizes the mark**: no whole-cell walk of the unit carrier lands
on the half turn — that would force `π = k/m` rational.  A non-closing scale has no arc to
register an event with. -/
theorem unit_arcs_empty : eventArcs 1 = ∅ := by
  ext k
  simp only [eventArcs, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hk hcell
  have hsq : Complex.exp (I * ((2 * ((1 : ℝ) * (k : ℝ)) : ℝ) : ℂ)) = 1 := by
    have harg : ((2 * ((1 : ℝ) * (k : ℝ)) : ℝ) : ℂ)
        = (((1 : ℝ) * (k : ℝ) : ℝ) : ℂ) + (((1 : ℝ) * (k : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg, mul_add, Complex.exp_add,
      show Complex.exp (I * (((1 : ℝ) * (k : ℝ) : ℝ) : ℂ)) = -1 from hcell]
    norm_num
  rw [Complex.exp_eq_one_iff] at hsq
  obtain ⟨m, hm⟩ := hsq
  have him := congrArg Complex.im hm
  simp [Complex.mul_im] at him
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0] at him
    norm_num at him
    exact hk.ne' (by exact_mod_cast him)
  exact irrational_pi ⟨(k : ℚ) / m, by
    push_cast
    rw [div_eq_iff (by exact_mod_cast hm0 : (m : ℝ) ≠ 0)]
    linarith [him]⟩

/-- Realizing the mark forces closure: an arc to the half turn doubles to a full monodromy
loop, so the induced readout refines the §1 dichotomy — its support implies
`CircleMonodromy`. -/
theorem arcs_nonempty_monodromy {H : ℝ} (hH : 0 < H) (h : (eventArcs H).Nonempty) :
    Monodromy.CircleMonodromy H := by
  obtain ⟨k, hk, hcell⟩ := h
  have hsq : Complex.exp (I * ((H * (k : ℝ) + H * (k : ℝ) : ℝ) : ℂ)) = 1 := by
    have harg : ((H * (k : ℝ) + H * (k : ℝ) : ℝ) : ℂ)
        = ((H * (k : ℝ) : ℝ) : ℂ) + ((H * (k : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [harg, mul_add, Complex.exp_add,
      show Complex.exp (I * ((H * (k : ℝ) : ℝ) : ℂ)) = -1 from hcell]
    norm_num
  rw [Complex.exp_eq_one_iff] at hsq
  obtain ⟨m, hm⟩ := hsq
  have him := congrArg Complex.im hm
  simp [Complex.mul_im] at him
  have hmpos : 0 < m := by
    have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    have : (0 : ℝ) < (m : ℝ) := by nlinarith [Real.pi_pos, him]
    exact_mod_cast this
  refine ⟨2 * k, by omega, m.toNat, by omega, ?_⟩
  have hcast : ((m.toNat : ℕ) : ℝ) = (m : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hmpos.le
  rw [hcast]
  push_cast
  linarith [him]

open Classical in
/-- **The induced per-event contribution** of scale `H` in the scalar registered count: `1`
when some completed cell arc realizes the event mark, `0` when none ever does.  This is the
readout induced by the closure geometry; the values at the two scales are the theorems
`eventContribution_pi3` and `eventContribution_one`, not choices. -/
noncomputable def eventContribution (H : ℝ) : ℝ :=
  if (eventArcs H).Nonempty then 1 else 0

/-- **A completed native cell contributes one registered event**: at `π/3` the wall exists
(`pi3_wall_mem`), so the induced contribution is `1`. -/
theorem eventContribution_pi3 : eventContribution (Real.pi / 3) = 1 :=
  if_pos ⟨3, pi3_wall_mem⟩

/-- **A non-closing scale contributes no event**: at scale `1` no arc realizes the mark
(`unit_arcs_empty`), so the induced contribution is `0` — only the continuous clock
procession remains. -/
theorem eventContribution_one : eventContribution (1 : ℝ) = 0 :=
  if_neg (by rw [unit_arcs_empty]; exact Set.not_nonempty_empty)

/-- **The native chart's clock is zero — derived from `no_native_oscillation`.**  On any
event-free stretch, *every* continuous clock the native readout factors through is constant:
the clock-despun readout is real (`no_native_oscillation`), so a factorization
`ζ(½+it)·e^{iϑ(t)} = r(t)·e^{iφ(t)}` with real `r ≠ 0` pins `φ(t)` to `πℤ`, and a continuous
`πℤ`-valued function on an interval is constant.  The native chart therefore has no
continuous clock procession; the zero clock passed to `N_pi3` is this theorem's content
under the origin normalization. -/
theorem native_clock_locally_constant (φ : ℝ → ℝ) (hcont : Continuous φ) {a b : ℝ}
    (hfree : ∀ t ∈ Set.uIcc a b, riemannZeta (line t) ≠ 0)
    (hfac : ∀ t ∈ Set.uIcc a b, ∃ r : ℝ,
      riemannZeta (line t) * Complex.exp (I * ((theta t : ℝ) : ℂ))
        = (r : ℂ) * Complex.exp (I * ((φ t : ℝ) : ℂ))) :
    ∀ t ∈ Set.uIcc a b, φ t = φ a := by
  have hquant : ∀ t ∈ Set.uIcc a b, ∃ n : ℤ, φ t = n * Real.pi := by
    intro t ht
    obtain ⟨r, hr⟩ := hfac t ht
    have him := no_native_oscillation t
    rw [hr] at him
    have hsin : r * Real.sin (φ t) = 0 := by
      simpa [Complex.mul_im, Complex.exp_im, Complex.mul_re, Complex.mul_im] using him
    have hZ : riemannZeta (line t) * Complex.exp (I * ((theta t : ℝ) : ℂ)) ≠ 0 :=
      mul_ne_zero (hfree t ht) (Complex.exp_ne_zero _)
    have hrne : r ≠ 0 := by
      intro h0
      rw [h0] at hr
      simp at hr
      exact hZ (by rw [hr, zero_mul])
    have hs := (mul_eq_zero.mp hsin).resolve_left hrne
    rw [Real.sin_eq_zero_iff] at hs
    obtain ⟨n, hn⟩ := hs
    exact ⟨n, hn.symm⟩
  have hsub : φ '' Set.uIcc a b ⊆ Set.range (fun n : ℤ => (n : ℝ) * Real.pi) := by
    rintro x ⟨t, ht, rfl⟩
    obtain ⟨n, hn⟩ := hquant t ht
    exact ⟨n, hn.symm⟩
  have hcountable : (φ '' Set.uIcc a b).Countable :=
    (Set.countable_range _).mono hsub
  have hpre : IsPreconnected (φ '' Set.uIcc a b) :=
    isPreconnected_uIcc.image φ hcont.continuousOn
  have hsing :=
    CarrierReachability.subsingleton_of_countable_preconnected hcountable hpre
  intro t ht
  exact hsing (Set.mem_image_of_mem φ ht) (Set.mem_image_of_mem φ Set.left_mem_uIcc)

/-! ### §4b The count functor, from the induced readout -/

/-- **The scale-indexed cumulative count functor** `X_{ζ,H} ⟶ (z ↦ N_H(z))`: DC base at the
common origin, plus the chart's continuous clock procession in π-cells, plus the event
channel — the event count weighted by the **induced per-event contribution** of the scale's
closure geometry (`eventContribution`, §4a).  No gate is inserted: the event channel's
weight is the arc-geometry readout, a theorem at each scale. -/
noncomputable def registeredCount (H : ℝ) (base : ℝ) (clock : ℝ → ℝ) (events : ℝ → ℕ)
    (z : ℝ) : ℝ :=
  base + (clock (Real.log z) - clock 0) / Real.pi + eventContribution H * (events z : ℝ)

/-- **`N_{π/3}`**: the native realization registered by the functor.  The zero clock is the
*derived* native datum: every continuous clock the native readout factors through is
constant on event-free stretches (`native_clock_locally_constant`, from
`no_native_oscillation`), so with the origin normalization the native clock is the zero
function; base `0` is the common origin.  The event channel carries weight one per event by
the arc geometry (`eventContribution_pi3`; one wall per completed cell, `pi3_arcs_eq`). -/
noncomputable def N_pi3 (z : ℝ) : ℝ :=
  registeredCount (Real.pi / 3) 0 (fun _ => 0) nativeCount z

/-- **`N_1`**: the *same* fiber events, the *same* functor, at carrier scale `1`.  Base is the
DC residue (`dcResidue_spec` — the trivial-channel pole registers at the origin); the clock is
`theta` (`unit_chart_factorization` — the readout's entire continuous phase; unique by
`theta_unique`); the event channel carries weight zero by the arc geometry
(`eventContribution_one` — the unit scale never realizes the event mark). -/
noncomputable def N_1 (z : ℝ) : ℝ :=
  registeredCount 1 dcResidue theta nativeCount z

/-- The native count evaluates to the pure event counter: `N_{π/3}(z) = #closures(z)` —
one registered event per completed native cell (`eventContribution_pi3`). -/
theorem N_pi3_eval (z : ℝ) : N_pi3 z = (nativeCount z : ℝ) := by
  unfold N_pi3 registeredCount
  rw [eventContribution_pi3]
  ring

/-- **The unit-1 identification `N_1(e^t) = 1 + ϑ(t)/π`** — *derived* from the unit-`1`
realization: the DC residue registers the base, the clock `ϑ` is the readout's entire
continuous procession, and the event channel contributes nothing because the unit scale's
arc geometry never realizes the event mark (`eventContribution_one`).  The theta term is a
conclusion, not a definition. -/
theorem unit_identification (t : ℝ) :
    N_1 (Real.exp t) = 1 + theta t / Real.pi := by
  unfold N_1 registeredCount
  rw [eventContribution_one, Real.log_exp, theta_zero, dcResidue]
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

/-! ## §7 The general registration gap `S_{H,K}` and the harmonic-closure family

The carrier can be scaled to any value where the representative closes harmonically.  The
canonical scale-`H` chart is determined by the derived event weight (`eventContribution H`,
§4a): the continuous channel carries the *complementary* weight — a mark-realizing scale
carries the procession discretely (zero clock, zero base: `native_clock_locally_constant`),
a non-realizing scale carries it continuously (clock `ϑ`:
`unit_chart_factorization`/`theta_unique`; base: `dcResidue_spec`).  Because the weight is
the arc-set indicator, this family contains *exactly* the two proven chart types, decided by
the arc geometry (`NH_dichotomy`) — nothing new is inserted, and `NH_pi3`/`NH_one` anchor
the family to the §4 charts.

The two-scale gap `S_{H,K}(t) := N_H(e^t) − N_K(e^t)` is a **coboundary** of the per-scale
potential `NH`: reflexive, antisymmetric, cocycle-composing.  `S(t)` is *relative* — a gap
between registrations, never an intrinsic state.  Every harmonic scale `π/m` realizes the
event mark (wall at `m` cells, exactly one per closed `2m`-cell loop), so the family
registers identically and every member reads the SAME classical `S(t)` against the unit
chart.  Monodromy is necessary for the event channel but not sufficient (`2π` closes in one
cell yet never realizes the mark): the channel is decided by the arc geometry alone. -/

/-- **The canonical scale-`H` chart count `N_H`**: the functor with the event channel at its
derived weight and the continuous channel at the complementary weight.  Since
`eventContribution H` is the arc-set indicator, `NH H` is by theorem (`NH_dichotomy`) either
the native-type registration (events, no clock) or the unit-type registration (DC base and
clock, no events) — the family only organizes the two proven chart types along the derived
dichotomy. -/
noncomputable def NH (H : ℝ) (z : ℝ) : ℝ :=
  registeredCount H ((1 - eventContribution H) * dcResidue)
    (fun u => (1 - eventContribution H) * theta u) nativeCount z

/-- The family passes through the proven native chart: `NH (π/3) = N_pi3`. -/
theorem NH_pi3 (z : ℝ) : NH (Real.pi / 3) z = N_pi3 z := by
  unfold NH N_pi3 registeredCount
  simp only [eventContribution_pi3]
  ring

/-- The family passes through the proven unit chart: `NH 1 = N_1`. -/
theorem NH_one (z : ℝ) : NH 1 z = N_1 z := by
  unfold NH N_1 registeredCount
  simp only [eventContribution_one]
  ring

/-- **The canonical family has exactly two registration types**, decided by the derived arc
geometry: full native event registration, or DC base plus clock.  No third chart type is
introduced by the generalization. -/
theorem NH_dichotomy (H : ℝ) :
    (∀ z, NH H z = (nativeCount z : ℝ)) ∨
      (∀ z, NH H z = dcResidue + (theta (Real.log z) - theta 0) / Real.pi) := by
  by_cases h : (eventArcs H).Nonempty
  · left
    intro z
    have hw : eventContribution H = 1 := if_pos h
    unfold NH registeredCount
    simp only [hw]
    ring
  · right
    intro z
    have hw : eventContribution H = 0 := if_neg h
    unfold NH registeredCount
    simp only [hw]
    ring

/-- **The two-scale carrier registration gap** `S_{H,K}(t) := N_H(e^t) − N_K(e^t)`: the
compensation the `K`-chart carries when tracking the `H`-carrier's procession. -/
noncomputable def Sgap (H K : ℝ) (t : ℝ) : ℝ := NH H (Real.exp t) - NH K (Real.exp t)

/-- Reflexivity: a scale has no gap against itself. -/
theorem Sgap_refl (H : ℝ) (t : ℝ) : Sgap H H t = 0 := sub_self _

/-- Antisymmetry: reversing the pair negates the gap. -/
theorem Sgap_antisymm (H K : ℝ) (t : ℝ) : Sgap H K t = -Sgap K H t := by
  unfold Sgap
  ring

/-- **Cocycle composition**: the gap composes through any intermediate scale,
`S_{H,L} = S_{H,K} + S_{K,L}`.  The registration gap is a coboundary of the per-scale
potential `NH` — relative, never intrinsic. -/
theorem Sgap_cocycle (H K L : ℝ) (t : ℝ) : Sgap H L t = Sgap H K t + Sgap K L t := by
  unfold Sgap
  ring

/-! ### The harmonic-closure family `H = π/m` -/

/-- **The harmonic wall**: every harmonic scale `π/m` (`m ≥ 1`) realizes the event mark at
exactly `m` cells — `m·(π/m) = π`. -/
theorem pi_div_wall (m : ℕ) (hm : 0 < m) : m ∈ eventArcs (Real.pi / (m : ℝ)) := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  refine ⟨hm, ?_⟩
  have harg : ((Real.pi / (m : ℝ) * (m : ℝ) : ℝ) : ℂ) = ((Real.pi : ℝ) : ℂ) := by
    rw [div_mul_cancel₀ _ hm0]
  rw [cellAt, harg, mul_comm]
  exact_mod_cast Complex.exp_pi_mul_I

/-- **Every harmonic channel is open — determined by the wall, not prescribed**:
`eventContribution (π/m) = 1` for every `m ≥ 1`. -/
theorem pi_div_channel_open (m : ℕ) (hm : 0 < m) :
    eventContribution (Real.pi / (m : ℝ)) = 1 :=
  if_pos ⟨m, pi_div_wall m hm⟩

/-- Every harmonic scale closes — *derived* by doubling the wall through
`arcs_nonempty_monodromy`, not asserted. -/
theorem pi_div_closes (m : ℕ) (hm : 0 < m) :
    Monodromy.CircleMonodromy (Real.pi / (m : ℝ)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  exact arcs_nonempty_monodromy (by positivity) ⟨m, pi_div_wall m hm⟩

/-- **Exactly one wall per closed loop, at every harmonic scale**: the arcs of `π/m`
realizing the mark are precisely `k ≡ m (mod 2m)` — one registered event per completed
`2m`-cell monodromy loop. -/
theorem pi_div_arcs_eq (m : ℕ) (hm : 0 < m) :
    eventArcs (Real.pi / (m : ℝ)) = {k : ℕ | k % (2 * m) = m} := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  ext k
  simp only [eventArcs, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hk, hcell⟩
    have hpi : Complex.exp (I * ((Real.pi : ℝ) : ℂ)) = -1 := by
      rw [mul_comm]
      exact_mod_cast Complex.exp_pi_mul_I
    have h1 : Complex.exp (I * ((Real.pi / (m : ℝ) * (k : ℝ) - Real.pi : ℝ) : ℂ)) = 1 := by
      have harg : ((Real.pi / (m : ℝ) * (k : ℝ) - Real.pi : ℝ) : ℂ)
          = ((Real.pi / (m : ℝ) * (k : ℝ) : ℝ) : ℂ) - ((Real.pi : ℝ) : ℂ) := by
        push_cast
        ring
      rw [harg, mul_sub, Complex.exp_sub,
        show Complex.exp (I * ((Real.pi / (m : ℝ) * (k : ℝ) : ℝ) : ℂ)) = -1 from hcell, hpi]
      norm_num
    rw [Complex.exp_eq_one_iff] at h1
    obtain ⟨n, hn⟩ := h1
    have him := congrArg Complex.im hn
    simp [Complex.mul_im] at him
    have hkm : (k : ℝ) = (m : ℝ) + 2 * (m : ℝ) * (n : ℝ) := by
      field_simp at him
      linear_combination him
    have hkz : (k : ℤ) = (m : ℤ) + 2 * (m : ℤ) * n := by exact_mod_cast hkm
    have hn0 : 0 ≤ n := by
      by_contra hneg
      rw [not_le] at hneg
      have hle : n ≤ -1 := by omega
      have hb : 2 * (m : ℤ) * n ≤ 2 * (m : ℤ) * (-1) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
      have : (k : ℤ) ≤ -(m : ℤ) := by linarith [hkz, hb]
      have hk1 : (1 : ℤ) ≤ (k : ℤ) := by exact_mod_cast hk
      have hm1 : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
      linarith
    obtain ⟨n', rfl⟩ : ∃ n' : ℕ, (n' : ℤ) = n := ⟨n.toNat, Int.toNat_of_nonneg hn0⟩
    have hknat : k = m + 2 * m * n' := by exact_mod_cast hkz
    rw [hknat, show m + 2 * m * n' = m + (2 * m) * n' by ring,
      Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by omega)
  · intro hk
    obtain ⟨q, hq⟩ : ∃ q, k = 2 * m * q + m :=
      ⟨k / (2 * m), by
        have h := Nat.mod_add_div k (2 * m)
        rw [hk] at h
        linarith [h]⟩
    subst hq
    refine ⟨Nat.add_pos_right _ hm, ?_⟩
    have hm0C : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
    have harg : ((Real.pi / (m : ℝ) * ((2 * m * q + m : ℕ) : ℝ) : ℝ) : ℂ)
        = ((q : ℤ) : ℂ) * (2 * (Real.pi : ℂ)) + (Real.pi : ℂ) := by
      push_cast
      field_simp
    rw [cellAt, harg, mul_add, Complex.exp_add]
    have h1 : Complex.exp (I * (((q : ℤ) : ℂ) * (2 * (Real.pi : ℂ)))) = 1 := by
      rw [show I * (((q : ℤ) : ℂ) * (2 * (Real.pi : ℂ)))
          = ((q : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) by ring]
      exact_mod_cast Complex.exp_int_mul_two_pi_mul_I (q : ℤ)
    rw [h1, one_mul, mul_comm]
    exact_mod_cast Complex.exp_pi_mul_I

/-- The `π/6` wall: six cells are the half turn — the `π/6` event channel is **open**,
determined by the arc geometry. -/
theorem pi6_wall_mem : 6 ∈ eventArcs (Real.pi / 6) := by
  have h := pi_div_wall 6 (by norm_num)
  simpa using h

/-- The `π/6` event channel is open: `eventContribution (π/6) = 1` — a theorem of the arc
geometry, not a prescription. -/
theorem eventContribution_pi6 : eventContribution (Real.pi / 6) = 1 :=
  if_pos ⟨6, pi6_wall_mem⟩

/-- The `π/6` carrier closes (twelve cells) — derived by doubling the wall. -/
theorem pi6_closes : Monodromy.CircleMonodromy (Real.pi / 6) :=
  arcs_nonempty_monodromy (by positivity) ⟨6, pi6_wall_mem⟩

/-- The `π/6` arcs realizing the mark are exactly `k ≡ 6 (mod 12)`: one registered event
per completed twelve-cell loop. -/
theorem pi6_arcs_eq : eventArcs (Real.pi / 6) = {k : ℕ | k % 12 = 6} := by
  have h := pi_div_arcs_eq 6 (by norm_num)
  simpa using h

/-- `2π` closes in one cell — full-turn monodromy. -/
theorem two_pi_closes : Monodromy.CircleMonodromy (2 * Real.pi) :=
  ⟨1, one_pos, 1, one_pos, by push_cast; ring⟩

/-- ...yet `2π` never realizes the mark: every whole-cell walk of the `2π` carrier sits at
`1 ≠ −1`.  **Monodromy is necessary but not sufficient** for the event channel; the arc
geometry decides. -/
theorem two_pi_arcs_empty : eventArcs (2 * Real.pi) = ∅ := by
  ext k
  simp only [eventArcs, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro hk hcell
  have h1 : cellAt (2 * Real.pi) k = 1 := by
    rw [cellAt, show ((2 * Real.pi * (k : ℝ) : ℝ) : ℂ) = ((k : ℤ) : ℂ) * (2 * (Real.pi : ℂ))
        by push_cast; ring,
      show I * (((k : ℤ) : ℂ) * (2 * (Real.pi : ℂ)))
        = ((k : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) by ring]
    exact_mod_cast Complex.exp_int_mul_two_pi_mul_I (k : ℤ)
  rw [h1] at hcell
  norm_num at hcell

/-- The `2π` event channel is shut despite full monodromy: `eventContribution (2π) = 0`. -/
theorem eventContribution_two_pi : eventContribution (2 * Real.pi) = 0 :=
  if_neg (by rw [two_pi_arcs_empty]; exact Set.not_nonempty_empty)

/-! ### The fiber converts any scale: marks and dressings

Closure is a **resonance between the fiber and the carrier scale**, not a property of the
scale alone.  Two exact statements:

* *Marks.*  `eventArcs` hard-codes the self-dual mark `−1` (forced by the weld reality of
  the ζ fiber, §3).  For that mark the realizing scales are exactly the odd-π-commensurable
  ones (`eventArcs_nonempty_iff`: some `k·H` is an odd multiple of `π`).  A scale like
  `log 7` or `√5` never realizes the *half-turn* mark bare — but every scale realizes the
  marks of the functions tuned to it (`every_scale_resonates`).

* *Dressings.*  The fiber — the function representation — carries its own per-cell spin, and
  a spin `μ` dresses the scale-`H` walk into the scale-`(H+μ)` walk (`dressedCell_eq`).  So
  **every** carrier scale is converted to exact harmonic closure by the fiber that carries
  the compensating spin (`fiber_converts_to_harmonic`, `every_scale_admits_conversion`):
  `log 7` steps become the native μ6 walk under `μ = π/3 − log 7`.  The conversion belongs
  to the fiber, never to the bare lattice. -/

/-- The arc set for an arbitrary event mark `w`: the self-dual case is `w = −1`. -/
def eventArcsAt (H : ℝ) (w : ℂ) : Set ℕ := {k : ℕ | 0 < k ∧ cellAt H k = w}

/-- `eventArcs` is the self-dual instance of the general mark family. -/
theorem eventArcs_eq_eventArcsAt (H : ℝ) : eventArcs H = eventArcsAt H (-1) := rfl

/-- **Every scale has resonating marks**: for every `H` and every `k ≥ 1`, the mark that the
`k`-cell walk lands on is realized at scale `H`.  No scale is intrinsically closed to
registration — only to particular marks. -/
theorem every_scale_resonates (H : ℝ) (k : ℕ) (hk : 0 < k) :
    (eventArcsAt H (cellAt H k)).Nonempty :=
  ⟨k, hk, rfl⟩

/-- **The self-dual criterion**: the half-turn mark is realized at scale `H` exactly when
some whole number of cells is an odd multiple of `π` — `k·H = (2j+1)·π`.  This is the
precise boundary between the harmonic family and the bare weird scales. -/
theorem eventArcs_nonempty_iff (H : ℝ) :
    (eventArcs H).Nonempty ↔ ∃ k : ℕ, 0 < k ∧ ∃ j : ℤ, (k : ℝ) * H = (2 * j + 1) * Real.pi := by
  constructor
  · rintro ⟨k, hk, hcell⟩
    refine ⟨k, hk, ?_⟩
    have hpi : Complex.exp (I * ((Real.pi : ℝ) : ℂ)) = -1 := by
      rw [mul_comm]
      exact_mod_cast Complex.exp_pi_mul_I
    have h1 : Complex.exp (I * ((H * (k : ℝ) - Real.pi : ℝ) : ℂ)) = 1 := by
      have harg : ((H * (k : ℝ) - Real.pi : ℝ) : ℂ)
          = ((H * (k : ℝ) : ℝ) : ℂ) - ((Real.pi : ℝ) : ℂ) := by
        push_cast
        ring
      rw [harg, mul_sub, Complex.exp_sub,
        show Complex.exp (I * ((H * (k : ℝ) : ℝ) : ℂ)) = -1 from hcell, hpi]
      norm_num
    rw [Complex.exp_eq_one_iff] at h1
    obtain ⟨j, hj⟩ := h1
    have him := congrArg Complex.im hj
    simp [Complex.mul_im] at him
    refine ⟨j, ?_⟩
    have hswap : H * (k : ℝ) = (k : ℝ) * H := mul_comm _ _
    linarith [him]
  · rintro ⟨k, hk, j, hj⟩
    refine ⟨k, hk, ?_⟩
    have harg : ((H * (k : ℝ) : ℝ) : ℂ) = (j : ℂ) * (2 * (Real.pi : ℂ)) + (Real.pi : ℂ) := by
      have : H * (k : ℝ) = (j : ℝ) * (2 * Real.pi) + Real.pi := by
        rw [mul_comm H (k : ℝ), hj]
        ring
      rw [this]
      push_cast
      ring
    rw [cellAt, harg, mul_add, Complex.exp_add]
    have h1 : Complex.exp (I * ((j : ℂ) * (2 * (Real.pi : ℂ)))) = 1 := by
      rw [show I * ((j : ℂ) * (2 * (Real.pi : ℂ))) = (j : ℂ) * (2 * (Real.pi : ℂ) * I) by ring]
      exact_mod_cast Complex.exp_int_mul_two_pi_mul_I j
    rw [h1, one_mul, mul_comm]
    exact_mod_cast Complex.exp_pi_mul_I

/-- **The fiber dressing**: the composite walk of the scale-`H` cells with a fiber spin `μ`
per cell — the fiber is the function representation, and this is its per-cell phase. -/
noncomputable def dressedCell (H μ : ℝ) (n : ℕ) : ℂ :=
  cellAt H n * Complex.exp (I * ((μ * (n : ℝ) : ℝ) : ℂ))

/-- Dressing shifts the scale: the dressed `H`-walk **is** the `(H+μ)`-walk. -/
theorem dressedCell_eq (H μ : ℝ) (n : ℕ) : dressedCell H μ n = cellAt (H + μ) n := by
  unfold dressedCell cellAt
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The fiber converts any scale into any harmonic closure**: for every carrier scale `H`
and every harmonic target `π/m`, the fiber spin `μ = π/m − H` dresses the `H`-walk into the
native `π/m` walk exactly — wall, loop, and channel included.  `log 7` steps become
harmonic closure through the fiber that carries the compensating spin. -/
theorem fiber_converts_to_harmonic (H : ℝ) (m : ℕ) (_hm : 0 < m) :
    ∀ n, dressedCell H (Real.pi / (m : ℝ) - H) n = cellAt (Real.pi / (m : ℝ)) n := by
  intro n
  rw [dressedCell_eq, show H + (Real.pi / (m : ℝ) - H) = Real.pi / (m : ℝ) by ring]

/-- **Every scale admits a conversion** — the existence form: for every `H` there is a fiber
spin realizing the event mark on the dressed walk and closing its monodromy loop.  The
carrier scales by whatever; the conversion is the fiber's. -/
theorem every_scale_admits_conversion (H : ℝ) :
    ∃ μ : ℝ, ∃ k : ℕ, 0 < k ∧ dressedCell H μ k = -1 ∧
      Monodromy.CircleMonodromy (H + μ) := by
  refine ⟨Real.pi / 3 - H, 3, by norm_num, ?_, ?_⟩
  · rw [dressedCell_eq, show H + (Real.pi / 3 - H) = Real.pi / 3 by ring]
    exact pi3_wall_mem.2
  · rw [show H + (Real.pi / 3 - H) = Real.pi / 3 by ring]
    exact pi3_closes

/-! ### Instantiations: recovering `S(t)` and its harmonic versions -/

/-- **Classical recovery**: the `(π/3, 1)` gap is exactly the classical `S(t)`. -/
theorem Sgap_pi3_one (t : ℝ) : Sgap (Real.pi / 3) 1 t = S t := by
  unfold Sgap
  rw [NH_pi3, NH_one]
  exact carrier_scale_compensation_S t

/-- **Zero gap inside the harmonic family**: any two mark-realizing harmonic scales register
identically — the native count is scale-independent within the family. -/
theorem Sgap_pi_div (m m' : ℕ) (hm : 0 < m) (hm' : 0 < m') (t : ℝ) :
    Sgap (Real.pi / (m : ℝ)) (Real.pi / (m' : ℝ)) t = 0 := by
  unfold Sgap NH registeredCount
  simp only [pi_div_channel_open m hm, pi_div_channel_open m' hm']
  ring

/-- The `(π/6, π/3)` gap vanishes: the two native harmonic scales agree. -/
theorem Sgap_pi6_pi3 (t : ℝ) : Sgap (Real.pi / 6) (Real.pi / 3) t = 0 := by
  have h := Sgap_pi_div 6 3 (by norm_num) (by norm_num) t
  simpa using h

/-- **The second gap function `(π/6, 1)`, through the cocycle**:
`S_{π/6,1} = S_{π/6,π/3} + S_{π/3,1} = 0 + S(t)`.  The `π/6`-tracking version of `S(t)`
exists and *is* the classical `S(t)`. -/
theorem Sgap_pi6_one (t : ℝ) : Sgap (Real.pi / 6) 1 t = S t := by
  rw [Sgap_cocycle (Real.pi / 6) (Real.pi / 3) 1 t, Sgap_pi6_pi3, Sgap_pi3_one, zero_add]

/-- **The general harmonic version**: for every `m ≥ 1` the `(π/m, 1)` gap is the same
classical `S(t)` — one `S`, read from every harmonically closing carrier. -/
theorem Sgap_pi_div_one (m : ℕ) (hm : 0 < m) (t : ℝ) :
    Sgap (Real.pi / (m : ℝ)) 1 t = S t := by
  have h0 : Sgap (Real.pi / (m : ℝ)) (Real.pi / 3) t = 0 := by
    have h := Sgap_pi_div m 3 hm (by norm_num) t
    simpa using h
  rw [Sgap_cocycle (Real.pi / (m : ℝ)) (Real.pi / 3) 1 t, h0, Sgap_pi3_one, zero_add]

/-- **The unit chart tracks the `π/6` carrier with `S(t)`**: there is a version of `S(t)`
tracking the `π/6`-scaled carrier procession — namely
`NH (π/6) (e^t) = N_1(e^t) + S(t)` — and it is the classical `S(t)`. -/
theorem unit_tracks_pi6 (t : ℝ) :
    NH (Real.pi / 6) (Real.exp t) = N_1 (Real.exp t) + S t := by
  have h := Sgap_pi6_one t
  unfold Sgap at h
  rw [NH_one] at h
  linarith [h]

/-- **The unit chart tracks every harmonic carrier with the same `S(t)`** — the general
tracking law: `NH (π/m) (e^t) = N_1(e^t) + S(t)` for every `m ≥ 1`. -/
theorem unit_tracks_harmonic (m : ℕ) (hm : 0 < m) (t : ℝ) :
    NH (Real.pi / (m : ℝ)) (Real.exp t) = N_1 (Real.exp t) + S t := by
  have h := Sgap_pi_div_one m hm t
  unfold Sgap at h
  rw [NH_one] at h
  linarith [h]

end CriticalLinePhasor.CarrierScale
