import RequestProject.MeromorphicTraceIdentity
import RequestProject.HilbertPolya
import RequestProject.ThreeDFocalEvent

/-!
# The twin resolvent-trace capture formulas: one per reading of "the zero"

There are two legitimate addresses for a carrier event.  In three dimensions the event is
the point `line γ = 1/2 + iγ` where the fibre closes residue-free; in the one-dimensional
readout the event is the real ordinate `γ`.  This file formalises **two capture formulas,
both unconditional**, one per reading, and proves they are the same capture object seen in
two charts:

* **The 3D-canonical trace** `trace3D E m w`.  For a finite set of carrier event heights
  `E : Finset ℝ` with multiplicities `m : ℝ → ℕ`, the multiplicity-weighted sum of the
  genuine fibre resolvent-determinant traces of the self-adjoint von Neumann operators
  `vonNeumannOp γ`.  Each summand is `vonNeumann_resolvent_trace`
  (`MeromorphicTraceIdentity`), whose closed form is `I / specBchan γ w = (w − line γ)⁻¹`.
  Its poles sit **exactly at the carrier points** `line γ` (the `1/2 + iγ`), with residues
  the multiplicities `m γ` (`trace3D_capture`); it is analytic off those points
  (`trace3D_analyticAt_off`).  The trace is defined on abstract finite event data, so it
  consumes the carrier's marked heights under the 3D reading.

* **The 1D-selected trace** is the graded resolvent trace `gradedResolventTrace w T`
  (`GradedModeDictionary`), whose poles sit at the real ordinates `γ` with residues the
  log-derivative residues (`trace1D_capture`, a thin re-export of
  `gradedResolventTrace_eq_residue_sum`).

* **The correlation** `twinTraces_agree_on_window`.  On every analytic window `(0,T]`, the
  3D trace read at the carrier point `lineC w` equals `I · gradedResolventTrace w T`: the
  same capture object, two indexings, proven equal.  The substitution `w ↦ lineC w` and the
  factor `I` are exactly the height↔line chart change (`d(lineC)/dw = i`) — the price of
  the 3D reading placing its pole on the critical line rather than at the real ordinate.

Scope: finite window, unconditional; no RH/GRH is assumed or proved.  The `T → ∞` limit of
the windowed resolvent is `windowedDiffResolvent_tendsto` (`DifferencedResolvent.lean`), not
re-proved here.  Every declaration below has the standard kernel footprint.

## Conformance note (statements differ from the informal directive, by design)

`vonNeumann_resolvent_trace` gives the von Neumann operator's resolvent-determinant trace as
`I / specBchan γ w = (w − line γ)⁻¹` — pole at the **line point** `line γ`, not at the real
ordinate `γ`.  Reusing it faithfully therefore forces two departures from a verbatim
`trace3D … w = gradedResolventTrace w T`:

  * the 3D capture is stated at `line γ₀` (residue `m γ₀`), i.e. poles at `{line γ : γ ∈ E}`;
  * the correlation carries the chart Jacobian `I` and evaluates `trace3D` at `lineC w`.

Both are the honest content of the operator's own resolvent trace.

## Construction search audit

The completed-event assembly was preceded by:

* `rg -n -i "CompletedThreeDEigenEvent|completedThreeDOperator|threeD.*eigenvector|
  trace3D.*eigen|oneD.*threeD.*trace|fixed.*3D.*operator" RequestProject --glob '*.lean'`;
* `rg -n -i "diagOp|Finsupp.single.*eigen|resolvent.*trace|Matrix.trace|
  LinearMap.trace" RequestProject --glob '*.lean'`;
* the same diagonal/eigenvector/trace search in `.lake/packages/mathlib/Mathlib`.

The matching repo conclusions used below are `diagOp_symmetric`, `diagOp_eigenvector`,
`vonNeumannResolventTrace_eq_line`, and the retained `trace3D_capture`.
-/

open Complex Filter Topology
open CriticalLinePhasor.SelfAdjointGenerator CriticalLinePhasor.CarrierScale
open CriticalLinePhasor.ResidueJump CriticalLinePhasor.GradedModes
open CriticalLinePhasor.ThreeDFocal

namespace CriticalLinePhasor.TwinResolventTrace

/-! ## §0 The fibre resolvent-determinant trace of the von Neumann operator

The genuine resolvent-determinant trace of the self-adjoint operator `vonNeumannOp γ`,
reused verbatim from `MeromorphicTraceIdentity.vonNeumann_resolvent_trace`, together with
its closed form `(w − line γ)⁻¹` (pole at the carrier point `line γ = 1/2 + iγ`). -/

/-- The fibre resolvent-determinant trace of the self-adjoint von Neumann operator
`vonNeumannOp γ = γ • id` at spectral parameter `w`:
`logDeriv (w ↦ det (specOp (vonNeumannOp γ) w))`. -/
noncomputable def vonNeumannResolventTrace (γ : ℝ) (w : ℂ) : ℂ :=
  logDeriv (fun z => LinearMap.det
    (specOp (CriticalLinePhasor.UnconditionalFrobenius.vonNeumannOp γ) z)) w

/-- The resolvent trace in signed-mode form, reused from
`MeromorphicTraceIdentity.vonNeumann_resolvent_trace`. -/
theorem vonNeumannResolventTrace_eq_specBchan (γ : ℝ) (w : ℂ) :
    vonNeumannResolventTrace γ w = Complex.I / specBchan γ w :=
  CriticalLinePhasor.Tate.vonNeumann_resolvent_trace γ w

/-- `specBchan γ w = I · (w − line γ)`: the signed mode is `I` times the displacement from
the carrier point. -/
theorem specBchan_eq_I_mul (γ : ℝ) (w : ℂ) :
    specBchan γ w = Complex.I * (w - line γ) := by
  simp only [specBchan, specHeight, line, lineC]
  linear_combination (γ : ℂ) * Complex.I_sq

/-- **Closed form of the fibre resolvent trace**, unconditional: `(w − line γ)⁻¹` — a simple
pole at the carrier point `line γ = 1/2 + iγ`, residue `1`. -/
theorem vonNeumannResolventTrace_eq_line (γ : ℝ) (w : ℂ) :
    vonNeumannResolventTrace γ w = (w - line γ)⁻¹ := by
  rw [vonNeumannResolventTrace_eq_specBchan, specBchan_eq_I_mul, div_eq_mul_inv, mul_inv,
    ← mul_assoc, mul_inv_cancel₀ Complex.I_ne_zero, one_mul]

/-- The critical-line parametrization is injective. -/
theorem line_injective : Function.Injective line := by
  intro a b h
  simp only [line, lineC, add_right_inj] at h
  exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h

/-! ## §1 The 3D-canonical windowed trace -/

/-- **The 3D-canonical windowed trace.**  For a finite set of carrier event heights `E`
with multiplicities `m`, the multiplicity-weighted sum of the fibre resolvent-determinant
traces of the von Neumann operators `vonNeumannOp γ`. -/
noncomputable def trace3D (E : Finset ℝ) (m : ℝ → ℕ) (w : ℂ) : ℂ :=
  ∑ γ ∈ E, (m γ : ℂ) * vonNeumannResolventTrace γ w

/-- **The capture formula, closed form**: `trace3D E m w = Σ_{γ ∈ E} m γ · (w − line γ)⁻¹`.
Each summand is the operator's genuine resolvent trace; the pole of the `γ` term is the
carrier point `line γ`. -/
theorem trace3D_eq_sum (E : Finset ℝ) (m : ℝ → ℕ) (w : ℂ) :
    trace3D E m w = ∑ γ ∈ E, (m γ : ℂ) * (w - line γ)⁻¹ := by
  unfold trace3D
  exact Finset.sum_congr rfl fun γ _ => by rw [vonNeumannResolventTrace_eq_line]

theorem trace3D_eq_sum' (E : Finset ℝ) (m : ℝ → ℕ) :
    trace3D E m = fun w => ∑ γ ∈ E, (m γ : ℂ) * (w - line γ)⁻¹ :=
  funext fun w => trace3D_eq_sum E m w

/-- **The residue capture, unconditional.**  For any event height `γ₀ ∈ E`, `trace3D` has a
simple pole exactly at the carrier point `line γ₀`, with residue the multiplicity `m γ₀`:
`(w − line γ₀) · trace3D E m w → m γ₀` as `w → line γ₀` off the point.  (When `m γ₀ = 0` the
"pole" is absent and the residue is `0`; the statement holds uniformly.)  Every other event
term is continuous at `line γ₀` and killed by the `(w − line γ₀)` factor — the distinctness
of the carrier points is `line_injective`. -/
theorem trace3D_capture (E : Finset ℝ) (m : ℝ → ℕ) {γ₀ : ℝ} (hγ₀ : γ₀ ∈ E) :
    Tendsto (fun w => (w - line γ₀) * trace3D E m w)
      (𝓝[≠] (line γ₀)) (𝓝 (m γ₀ : ℂ)) := by
  -- pointwise split off the `γ₀` term
  have key : ∀ w, w ≠ line γ₀ →
      (w - line γ₀) * trace3D E m w
        = (m γ₀ : ℂ) + (w - line γ₀) *
            ∑ γ ∈ E.erase γ₀, (m γ : ℂ) * (w - line γ)⁻¹ := by
    intro w hw
    rw [trace3D_eq_sum, ← Finset.add_sum_erase E (fun γ => (m γ : ℂ) * (w - line γ)⁻¹) hγ₀,
      mul_add]
    congr 1
    rw [mul_comm ((m γ₀ : ℂ)) ((w - line γ₀)⁻¹), ← mul_assoc,
      mul_inv_cancel₀ (sub_ne_zero.mpr hw), one_mul]
  have hev : (fun w => (w - line γ₀) * trace3D E m w)
      =ᶠ[𝓝[≠] (line γ₀)]
      (fun w => (m γ₀ : ℂ) + (w - line γ₀) *
        ∑ γ ∈ E.erase γ₀, (m γ : ℂ) * (w - line γ)⁻¹) := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    exact key w hw
  rw [tendsto_congr' hev]
  apply Tendsto.mono_left _ nhdsWithin_le_nhds
  -- continuity of the split function at `line γ₀`
  have h1 : Tendsto (fun w : ℂ => w - line γ₀) (𝓝 (line γ₀)) (𝓝 0) := by
    have h : Tendsto (fun w : ℂ => w - line γ₀) (𝓝 (line γ₀)) (𝓝 (line γ₀ - line γ₀)) :=
      (continuous_id.sub continuous_const).tendsto (line γ₀)
    rwa [sub_self] at h
  have h2 : Tendsto (fun w : ℂ => ∑ γ ∈ E.erase γ₀, (m γ : ℂ) * (w - line γ)⁻¹)
      (𝓝 (line γ₀))
      (𝓝 (∑ γ ∈ E.erase γ₀, (m γ : ℂ) * (line γ₀ - line γ)⁻¹)) := by
    apply tendsto_finsetSum
    intro γ hγ
    have hne : line γ₀ - line γ ≠ 0 :=
      sub_ne_zero.mpr (line_injective.ne (Finset.ne_of_mem_erase hγ)).symm
    have hsub : Tendsto (fun w : ℂ => w - line γ) (𝓝 (line γ₀)) (𝓝 (line γ₀ - line γ)) :=
      (continuous_id.sub continuous_const).tendsto (line γ₀)
    exact tendsto_const_nhds.mul (hsub.inv₀ hne)
  have h3 := (tendsto_const_nhds (x := (m γ₀ : ℂ))).add (h1.mul h2)
  simpa using h3

/-- **Analyticity off the carrier points.**  At any `w₀` not equal to `line γ` for every
`γ ∈ E`, `trace3D E m` is analytic — a finite sum of functions each analytic off its single
pole at the carrier point. -/
theorem trace3D_analyticAt_off (E : Finset ℝ) (m : ℝ → ℕ) {w₀ : ℂ}
    (hw₀ : ∀ γ ∈ E, w₀ ≠ line γ) :
    AnalyticAt ℂ (trace3D E m) w₀ := by
  rw [trace3D_eq_sum']
  apply Finset.analyticAt_fun_sum
  intro γ hγ
  have hden : AnalyticAt ℂ (fun w : ℂ => w - line γ) w₀ :=
    analyticAt_id.sub analyticAt_const
  exact analyticAt_const.mul (hden.fun_inv (sub_ne_zero.mpr (hw₀ γ hγ)))

/-! ## §1A Two traces assembled on completed 3D events

The preceding trace accepts an abstract finite set of ordinates.  The next two definitions use
the stronger index `CompletedThreeDEigenEvent χ`: membership in the index type already carries the
completed 3D focal-crossing certificate.  Both traces use the same finite event set.  The first
bundles below retain the event-restricted presentation; the ambient bundles place those same
events into `carrierThreeDOperator p r`, whose full carrier domain is independent of certificates.

* `completedTrace3D` places the poles at the 3D carrier points;
* `completedTrace1D` places the same poles in the logarithmic ordinate chart.

Thus the first bundle records 3D zeros and 3D eigenvectors.  The second additionally exposes the
1D analytic equation supplied by the completed fibre. -/

variable {q : ℕ} [NeZero q]

/-- The area-law carrier point at physical height `Z` is the critical-line chart of the derived
ordinate `log Z`. -/
theorem carrierPointAtHeight_eq_line (Z : ℝ) :
    carrierPointAtHeight Z = line (Real.log Z) := by
  simp [carrierPointAtHeight, carrierPoint, line, lineC]
  ring

/-- Version I: the completed-event 3D resolvent trace.  Each summand is the genuine local
resolvent-determinant trace of the diagonal mode selected by a completed 3D event. -/
noncomputable def completedTrace3D
    (χ : DirichletCharacter ℂ q)
    (E : Finset (CompletedThreeDEigenEvent χ))
    (m : CompletedThreeDEigenEvent χ → ℕ) (w : ℂ) : ℂ :=
  ∑ e ∈ E, (m e : ℂ) * vonNeumannResolventTrace (Real.log e.1) w

/-- Closed form of Version I: its poles are the physical 3D carrier points of the completed
events. -/
theorem completedTrace3D_eq_sum
    (χ : DirichletCharacter ℂ q)
    (E : Finset (CompletedThreeDEigenEvent χ))
    (m : CompletedThreeDEigenEvent χ → ℕ) (w : ℂ) :
    completedTrace3D χ E m w =
      ∑ e ∈ E, (m e : ℂ) * (w - carrierPointAtHeight e.1)⁻¹ := by
  unfold completedTrace3D
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [vonNeumannResolventTrace_eq_line, carrierPointAtHeight_eq_line]

/-- Version II: the same completed 3D events read in the 1D logarithmic-ordinate chart. -/
noncomputable def completedTrace1D
    (χ : DirichletCharacter ℂ q)
    (E : Finset (CompletedThreeDEigenEvent χ))
    (m : CompletedThreeDEigenEvent χ → ℕ) (w : ℂ) : ℂ :=
  ∑ e ∈ E, (m e : ℂ) * ((Real.log e.1 : ℂ) - w)⁻¹

/-- Closed form of Version II. -/
theorem completedTrace1D_eq_sum
    (χ : DirichletCharacter ℂ q)
    (E : Finset (CompletedThreeDEigenEvent χ))
    (m : CompletedThreeDEigenEvent χ → ℕ) (w : ℂ) :
    completedTrace1D χ E m w =
      ∑ e ∈ E, (m e : ℂ) * ((Real.log e.1 : ℂ) - w)⁻¹ := rfl

/-- The two completed-event traces are the same resolvent object in the carrier and ordinate
charts.  The factor `I` is exactly the chart Jacobian. -/
theorem completedTraces_agree
    (χ : DirichletCharacter ℂ q)
    (E : Finset (CompletedThreeDEigenEvent χ))
    (m : CompletedThreeDEigenEvent χ → ℕ) (w : ℂ) :
    completedTrace3D χ E m (lineC w) = Complex.I * completedTrace1D χ E m w := by
  rw [completedTrace3D_eq_sum, completedTrace1D_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [carrierPointAtHeight_eq_line]
  have h : lineC w - line (Real.log e.1) =
      -Complex.I * ((Real.log e.1 : ℂ) - w) := by
    simp only [lineC, line]
    ring
  rw [h, mul_inv, inv_neg, Complex.inv_I, neg_neg]
  ring

/-- Version I bundled: every index is a completed 3D zero and its basis state is a nonzero
eigenvector of the single completed 3D operator; the associated trace has its pole at that 3D
carrier point. -/
theorem threeDZero_eigenvector_resolventTrace
    (χ : DirichletCharacter ℂ q)
    (E : Finset (CompletedThreeDEigenEvent χ))
    (m : CompletedThreeDEigenEvent χ → ℕ) (w : ℂ) :
    (∀ e ∈ E,
      CompletedThreeDZeroAtHeight χ e.1 ∧
        Finsupp.single e (1 : ℂ) ≠ 0 ∧
        completedThreeDOperator χ (Finsupp.single e (1 : ℂ)) =
          (Real.log e.1 : ℂ) • Finsupp.single e (1 : ℂ)) ∧
      completedTrace3D χ E m w =
        ∑ e ∈ E, (m e : ℂ) * (w - carrierPointAtHeight e.1)⁻¹ := by
  constructor
  · intro e _he
    exact ⟨e.2, (completedThreeDOperator_eigenvector χ e).1,
      (completedThreeDOperator_eigenvector χ e).2⟩
  · exact completedTrace3D_eq_sum χ E m w

/-- Version II bundled: in addition to the same 3D crossing and eigenvector data, every event
has its 1D analytic L-function readout equation.  The 1D and 3D traces agree by the explicit chart
map. -/
theorem oneDZero_threeDZero_eigenvector_resolventTrace
    (χ : DirichletCharacter ℂ q)
    (E : Finset (CompletedThreeDEigenEvent χ))
    (m : CompletedThreeDEigenEvent χ → ℕ) (w : ℂ) :
    (∀ e ∈ E,
      DirichletCharacter.LFunction χ (carrierPointAtHeight e.1) = 0 ∧
        CompletedThreeDZeroAtHeight χ e.1 ∧
        Finsupp.single e (1 : ℂ) ≠ 0 ∧
        completedThreeDOperator χ (Finsupp.single e (1 : ℂ)) =
          (Real.log e.1 : ℂ) • Finsupp.single e (1 : ℂ)) ∧
      completedTrace1D χ E m w =
        ∑ e ∈ E, (m e : ℂ) * ((Real.log e.1 : ℂ) - w)⁻¹ ∧
      completedTrace3D χ E m (lineC w) =
        Complex.I * completedTrace1D χ E m w := by
  refine ⟨?_, completedTrace1D_eq_sum χ E m w, completedTraces_agree χ E m w⟩
  intro e _he
  exact ⟨completedThreeDEigenEvent_L_zero χ e, e.2,
    (completedThreeDOperator_eigenvector χ e).1,
    (completedThreeDOperator_eigenvector χ e).2⟩

/-- Ambient Version I: the same completed 3D trace, now bundled with eigenvectors of the carrier
operator whose state space was defined independently of completed-event certificates. -/
theorem threeDZero_ambientEigenvector_resolventTrace
    (p r : ℝ) (χ : DirichletCharacter ℂ q)
    (E : Finset (CompletedThreeDEigenEvent χ))
    (m : CompletedThreeDEigenEvent χ → ℕ) (w : ℂ) :
    (∀ e ∈ E,
      CompletedThreeDZeroAtHeight χ e.1 ∧
        Finsupp.single (e.toCarrierState p r) (1 : ℂ) ≠ 0 ∧
        carrierThreeDOperator p r (Finsupp.single (e.toCarrierState p r) (1 : ℂ)) =
          (Real.log e.1 : ℂ) • Finsupp.single (e.toCarrierState p r) (1 : ℂ)) ∧
      completedTrace3D χ E m w =
        ∑ e ∈ E, (m e : ℂ) * (w - carrierPointAtHeight e.1)⁻¹ := by
  constructor
  · intro e _he
    exact ⟨e.2, (carrierThreeDOperator_completedEvent_eigenvector p r e).1,
      (carrierThreeDOperator_completedEvent_eigenvector p r e).2⟩
  · exact completedTrace3D_eq_sum χ E m w

/-- Ambient Version II: the analytic 1D readout, the same completed 3D event, and its eigenvector
of the independently defined carrier operator are bundled with the exact trace chart relation. -/
theorem oneDZero_threeDZero_ambientEigenvector_resolventTrace
    (p r : ℝ) (χ : DirichletCharacter ℂ q)
    (E : Finset (CompletedThreeDEigenEvent χ))
    (m : CompletedThreeDEigenEvent χ → ℕ) (w : ℂ) :
    (∀ e ∈ E,
      DirichletCharacter.LFunction χ (carrierPointAtHeight e.1) = 0 ∧
        CompletedThreeDZeroAtHeight χ e.1 ∧
        Finsupp.single (e.toCarrierState p r) (1 : ℂ) ≠ 0 ∧
        carrierThreeDOperator p r (Finsupp.single (e.toCarrierState p r) (1 : ℂ)) =
          (Real.log e.1 : ℂ) • Finsupp.single (e.toCarrierState p r) (1 : ℂ)) ∧
      completedTrace1D χ E m w =
        ∑ e ∈ E, (m e : ℂ) * ((Real.log e.1 : ℂ) - w)⁻¹ ∧
      completedTrace3D χ E m (lineC w) =
        Complex.I * completedTrace1D χ E m w := by
  refine ⟨?_, completedTrace1D_eq_sum χ E m w, completedTraces_agree χ E m w⟩
  intro e _he
  exact ⟨completedThreeDEigenEvent_L_zero χ e, e.2,
    (carrierThreeDOperator_completedEvent_eigenvector p r e).1,
    (carrierThreeDOperator_completedEvent_eigenvector p r e).2⟩

/-! ## §2 The 1D-selected trace (bridge to the graded machinery)

The 1D reading is the graded resolvent trace of `GradedModeDictionary`, indexed by the real
ordinates.  Its capture formula is `gradedResolventTrace_eq_residue_sum`; we do not duplicate
it, only re-export it as the 1D companion of `trace3D_capture`. -/

/-- **The 1D-ordinate capture formula** (re-export of `gradedResolventTrace_eq_residue_sum`):
for `w` off the window's ordinates, the 1D graded resolvent trace is the residue sum
`Σ_γ r γ · (γ − w)⁻¹`, with `r γ` the log-derivative residue at the ordinate `γ`. -/
theorem trace1D_capture (w : ℂ) (T : ℝ)
    (hw : ∀ γ ∈ eventWindow T, w ≠ (γ : ℂ)) (r : ℝ → ℂ)
    (hr : ∀ γ ∈ eventWindow T,
      Tendsto (fun s => (s - line γ) * logDeriv riemannZeta s) (𝓝[≠] line γ) (𝓝 (r γ))) :
    gradedResolventTrace w T = ∑ γ ∈ eventWindow T, r γ * ((γ : ℂ) - w)⁻¹ :=
  gradedResolventTrace_eq_residue_sum w T hw r hr

/-! ## §3 The correlation: the two readings agree on every window -/

/-- The chart identity `(lineC w − line γ)⁻¹ = I · (γ − w)⁻¹`, holding for all `w` (both
sides vanish at the coincidence `w = γ`).  It is the height↔line change of variable applied
to a single resolvent term. -/
theorem lineC_sub_line_inv (w : ℂ) (γ : ℝ) :
    (lineC w - line γ)⁻¹ = Complex.I * ((γ : ℂ) - w)⁻¹ := by
  have h : lineC w - line γ = -Complex.I * ((γ : ℂ) - w) := by
    simp only [lineC, line]; ring
  rw [h, mul_inv, inv_neg, Complex.inv_I, neg_neg]

/-- **The correlation theorem.**  On every analytic window `(0,T]`, the 3D-canonical trace
instantiated on the window's event set (`eventWindow T`) with the analytic multiplicities
(`eventOrder`), read at the carrier point `lineC w`, equals `I · gradedResolventTrace w T`
(for `w` off the window's ordinates):

    `trace3D (eventWindow T) eventOrder (lineC w) = I · gradedResolventTrace w T`.

Same capture object, two indexings — the 3D reading at the line point and the 1D graded
reading at the ordinate — proven equal, the factor `I` the height↔line chart Jacobian. -/
theorem twinTraces_agree_on_window (T : ℝ) (w : ℂ)
    (hw : ∀ γ ∈ eventWindow T, w ≠ (γ : ℂ)) :
    trace3D (eventWindow T) eventOrder (lineC w)
      = Complex.I * gradedResolventTrace w T := by
  rw [trace3D_eq_sum, gradedResolventTrace_eq_windowedResolventTrace w T hw]
  simp only [windowedResolventTrace, windowedTrace]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [lineC_sub_line_inv]
  ring

/-! ## §4 The bundle -/

/-- **Twin capture, bundled.**  On every window `(0,T]`, packaged in one statement:

  (i)   the 3D-canonical capture — for every event `γ₀`, `trace3D` has a pole at the carrier
        point `line γ₀` with residue the multiplicity `eventOrder γ₀` (unconditional);
  (ii)  the 1D-selected capture — the graded resolvent trace is the residue sum over the
        ordinates (unconditional);
  (iii) the window agreement — the two readings coincide at `lineC w`, up to the chart
        factor `I`.

One capture formula per reading of "the zero", both unconditional, correlated. -/
theorem twin_capture (T : ℝ) (w : ℂ)
    (hw : ∀ γ ∈ eventWindow T, w ≠ (γ : ℂ)) (r : ℝ → ℂ)
    (hr : ∀ γ ∈ eventWindow T,
      Tendsto (fun s => (s - line γ) * logDeriv riemannZeta s) (𝓝[≠] line γ) (𝓝 (r γ))) :
    (∀ γ₀ ∈ eventWindow T,
        Tendsto (fun v => (v - line γ₀) * trace3D (eventWindow T) eventOrder v)
          (𝓝[≠] (line γ₀)) (𝓝 (eventOrder γ₀ : ℂ)))
      ∧ gradedResolventTrace w T = ∑ γ ∈ eventWindow T, r γ * ((γ : ℂ) - w)⁻¹
      ∧ trace3D (eventWindow T) eventOrder (lineC w)
          = Complex.I * gradedResolventTrace w T :=
  ⟨fun _γ₀ hγ₀ => trace3D_capture (eventWindow T) eventOrder hγ₀,
   trace1D_capture w T hw r hr,
   twinTraces_agree_on_window T w hw⟩

end CriticalLinePhasor.TwinResolventTrace

#print axioms CriticalLinePhasor.TwinResolventTrace.trace3D_capture
#print axioms CriticalLinePhasor.TwinResolventTrace.completedTrace3D_eq_sum
#print axioms CriticalLinePhasor.TwinResolventTrace.completedTrace1D_eq_sum
#print axioms CriticalLinePhasor.TwinResolventTrace.completedTraces_agree
#print axioms CriticalLinePhasor.TwinResolventTrace.threeDZero_eigenvector_resolventTrace
#print axioms CriticalLinePhasor.TwinResolventTrace.oneDZero_threeDZero_eigenvector_resolventTrace
#print axioms CriticalLinePhasor.TwinResolventTrace.threeDZero_ambientEigenvector_resolventTrace
#print axioms CriticalLinePhasor.TwinResolventTrace.oneDZero_threeDZero_ambientEigenvector_resolventTrace
#print axioms CriticalLinePhasor.TwinResolventTrace.twinTraces_agree_on_window
#print axioms CriticalLinePhasor.TwinResolventTrace.twin_capture
