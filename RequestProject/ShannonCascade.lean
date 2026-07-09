import RequestProject.LimitDominance
import RequestProject.XiChannelReceiver

/-!
# Shannon's Cascade, specialized to midpoint projection geometry

**Shannon's Cascade**: a chain of channels in series — stages flowing to a readout — with
a dominance certificate on every link (Shannon's Law of Projection Dominance: the source
dominates every projection of itself; features kept or ledger-lost, never created).
Cascaded channels are the native habitat of Shannon's Data Processing Inequality, the
cited anchor.

**The midpoint specialization** packages this program's instance: the stages are entire
(finite bank readouts), they converge locally uniformly to the section (the readout in
the spectral chart, real on the fold by `xiSection_real`), and the cascade carries its
open clause as a *field* rather than an external hypothesis —

* `complete` : **stage features accumulate only at the fold** — wherever the stage zeros
  cluster, the imaginary part is zero.  This is the accumulation clause, hfaithful's
  final coat, RH's entire remaining content: *nothing enters the cascade midstream.*

The wiring theorem `riemannHypothesis_of_complete_cascade` consumes the compiled engine
`limit_dominance` (zeros of the limit are limits of stage zeros) to convert completeness
into Mathlib's literal `RiemannHypothesis`: a chart zero is an accumulation point of
stage features, completeness places it on the fold, and the fold is the line.

The Davenport–Heilbronn control bites at the named field: DH assembles every dominance
link — same charts, same collapse, same limit machinery — but its stage features
genuinely accumulate off-fold (it has off-line zeros), because no FTA source balances
them.  `complete` is exactly the field DH cannot inhabit, and exactly the field the free
alphabet is expected to pay for.

Unconditional throughout: the structure asserts nothing; instances of `complete` are the
open target.  No `sorry`, no `axiom` beyond the standard three.
-/

open Filter Topology Complex CriticalLinePhasor.XiChannel CriticalLinePhasor.LimitDominance

namespace CriticalLinePhasor.Cascade

/-- **Shannon's Cascade, midpoint-specialized**: entire stages converging locally
uniformly to the ξ-section in the spectral chart.  The dominance links are carried by
the fields; the fold reality is already a theorem (`xiSection_real`). -/
structure MidpointCascade where
  /-- the finite stages of the cascade (finite bank readouts in the spectral chart). -/
  stage : ℕ → ℂ → ℂ
  /-- every stage is entire — each finite bank readout is an honest holomorphic object. -/
  stage_entire : ∀ n, Differentiable ℂ (stage n)
  /-- the cascade converges: stages flow locally uniformly to the ξ-section. -/
  converges : TendstoLocallyUniformly stage xiSection atTop

/-- **Completeness of the cascade** — the accumulation clause, as a field: wherever the
stage features accumulate, the fold.  *Nothing enters the cascade midstream.* -/
def Complete (C : MidpointCascade) : Prop :=
  ∀ z : ℂ, (∀ ε > 0, ∀ᶠ n in atTop, ∃ w ∈ Metric.ball z ε, C.stage n w = 0) → z.im = 0

/-- The ξ-section is not locally identically zero (transported from
`riemannXi_analyticOrderAt_ne_top_everywhere` through the affine chart). -/
theorem xiSection_not_eventually_zero (z₀ : ℂ) :
    ¬ (∀ᶠ z in nhds z₀, xiSection z = 0) := by
  intro hev
  apply ZD.riemannXi_analyticOrderAt_ne_top_everywhere (1 / 2 + Complex.I * z₀)
  rw [analyticOrderAt_eq_top]
  have hcont : Continuous (fun s : ℂ => -Complex.I * (s - 1 / 2)) := by fun_prop
  have hkey : ∀ s : ℂ, (1 : ℂ) / 2 + Complex.I * (-Complex.I * (s - 1 / 2)) = s := fun s => by
    linear_combination (-(s - 1 / 2)) * Complex.I_sq
  have hmap : Tendsto (fun s : ℂ => -Complex.I * (s - 1 / 2))
      (nhds (1 / 2 + Complex.I * z₀)) (nhds z₀) := by
    have h0 : -Complex.I * ((1 / 2 + Complex.I * z₀) - 1 / 2) = z₀ := by
      linear_combination (-z₀) * Complex.I_sq
    have := hcont.tendsto (1 / 2 + Complex.I * z₀)
    rwa [h0] at this
  filter_upwards [hmap.eventually hev] with s hs
  have : xiSection (-Complex.I * (s - 1 / 2)) = 0 := hs
  rwa [xiSection, hkey] at this

/-- **The wiring theorem: a complete cascade forces the Riemann Hypothesis.**  Every
chart zero is an accumulation point of stage features (`limit_dominance`, the compiled
engine); completeness places it on the fold; the fold is the line; the bridge converts
line placement into Mathlib's literal `RiemannHypothesis`. -/
theorem riemannHypothesis_of_complete_cascade
    (C : MidpointCascade) (hC : Complete C) : RiemannHypothesis := by
  refine RHBridge.no_offline_zeros_implies_rh ?_
  intro ρ hρ
  -- the zero's spectral parameter
  set z₀ : ℂ := -Complex.I * (ρ - 1 / 2) with hz₀def
  have hkey : (1 : ℂ) / 2 + Complex.I * z₀ = ρ := by
    rw [hz₀def]
    linear_combination (-(ρ - 1 / 2)) * Complex.I_sq
  -- the section vanishes at the spectral parameter
  have hzero : xiSection z₀ = 0 := by
    rw [xiSection, hkey]
    exact (ZD.riemannXi_eq_zero_iff ρ).mpr hρ
  -- stage features accumulate there (limit dominance)
  have haccum : ∀ ε > 0, ∀ᶠ n in atTop, ∃ w ∈ Metric.ball z₀ ε, C.stage n w = 0 := by
    intro ε hε
    have hconv : TendstoLocallyUniformlyOn C.stage xiSection atTop Set.univ :=
      tendstoLocallyUniformlyOn_univ.mpr C.converges
    exact limit_dominance isOpen_univ hconv
      (fun n => (C.stage_entire n).differentiableOn)
      (Set.mem_univ z₀) hzero (xiSection_not_eventually_zero z₀) hε
  -- completeness places the parameter on the fold, hence the zero on the line
  have him : z₀.im = 0 := hC z₀ haccum
  have : ρ.re = 1 / 2 := by
    have h1 : z₀.im = 1 / 2 - ρ.re := by
      rw [hz₀def]
      simp [Complex.mul_im, Complex.sub_im, Complex.sub_re]
    rw [h1] at him
    linarith
  exact this

end CriticalLinePhasor.Cascade
