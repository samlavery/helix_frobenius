import RequestProject.HilbertPolyaResolventTrace
import RequestProject.XiHadamardFactorization

/-!
# The spectral determinant of the flow generator

Deninger's programme needs a Lefschetz trace formula, whose role is to identify
a trace over a leafwise cohomology with the L-function.  This file takes the
alternative Deninger himself uses elsewhere: **regularized determinants**.  The
determinant candidate is `ξ` read in the spectral chart,

`spectralDet w = ξ(1/2 + i w)`.

Calling that function a *determinant* of the flow generator is a claim, and the
claim is what this file proves — the determinant property is a theorem package,
not a definition:

* **zero set = spectrum** (`spectralDet_eq_zero_iff_spectralCoord`):
  `spectralDet w = 0 ↔ ∃ ρ ∈ NontrivialZeros, w = t ρ`, where
  `t ρ = -i(ρ - 1/2)` is the spectral coordinate;
* **multiplicities match** (`spectralDet_analyticOrderNatAt`,
  `spectralDet_orderNat_spectralCoord`): the analytic vanishing order of
  `spectralDet` at `t ρ` is exactly `xiOrderNat ρ`, by transporting the local
  factorization `ξ(s) = (s-s₀)ⁿ·g(s)` through the affine chart;
* **canonical product over the spectrum** (`spectralDet_hadamard_factorization`):
  `spectralDet w = exp(A·w + B) · xiProductMult(1/2 + i·w)` — a nonvanishing
  entire exponential times the multiplicity-indexed Weierstrass product over
  the zero multiset, from the compiled Hadamard factorization;
* **trace identity** (`resolvent_trace_eq_neg_logDeriv_diff`): the compiled
  two-point resolvent trace of `HilbertPolyaResolventTrace` equals the
  difference of logarithmic derivatives of `spectralDet` — the identity
  `d/dw log det(Θ - w) = -Tr (Θ - w)⁻¹` in the only form that needs no
  trace-class hypothesis.

Together: an entire function whose zero multiset (with multiplicity) is the
spectrum of the flow generator, which factors as the canonical product over
that multiset, and whose log-derivative difference is the resolvent trace.
That is the regularized-determinant reading of the trace step, with the
cohomology's finiteness job done by the Hadamard product.  What remains of the
foliated route is definiteness of the polarization built in
`FoliatedPolarization`; nothing here bears on it, and this file proves nothing
about the location of any zero.
-/

open Complex Filter Topology

noncomputable section

namespace CriticalLinePhasor.FoliatedDeterminant

open CriticalLinePhasor.HilbertPolya

/-- The spectral determinant of the flow generator: `ξ` read in the spectral
coordinate, so that its zeros are exactly the `t ρ = -i(ρ - 1/2)`. -/
def spectralDet (w : ℂ) : ℂ := ZD.riemannXi (1 / 2 + Complex.I * w)

/-- The chart derivative of the spectral determinant. -/
theorem deriv_spectralDet (w : ℂ) :
    deriv spectralDet w
      = Complex.I * deriv ZD.riemannXi (1 / 2 + Complex.I * w) := by
  have hlin : HasDerivAt (fun v : ℂ => 1 / 2 + Complex.I * v) Complex.I w := by
    simpa using (((hasDerivAt_id w).const_mul Complex.I).const_add (1 / 2 : ℂ))
  have hxi : HasDerivAt ZD.riemannXi
      (deriv ZD.riemannXi (1 / 2 + Complex.I * w)) (1 / 2 + Complex.I * w) :=
    (ZD.riemannXi_differentiable _).hasDerivAt
  have h2 : HasDerivAt spectralDet
      (deriv ZD.riemannXi (1 / 2 + Complex.I * w) * Complex.I) w := hxi.comp w hlin
  rw [h2.deriv]
  ring

/-- The logarithmic derivative of the spectral determinant is `i · ξ'/ξ` in the
chart — the resolvent trace density of the flow generator.  Hypothesis-free:
with Lean's total division both sides vanish together at a zero of `ξ`. -/
theorem logDeriv_spectralDet (w : ℂ) :
    deriv spectralDet w / spectralDet w
      = Complex.I * (deriv ZD.riemannXi (1 / 2 + Complex.I * w)
          / ZD.riemannXi (1 / 2 + Complex.I * w)) := by
  rw [deriv_spectralDet, spectralDet, mul_div_assoc]

/-- **The trace identity.**  The compiled two-point resolvent trace over the
zero multiset equals the difference of logarithmic derivatives of the spectral
determinant — the identity `d/dw log det(Θ - w) = -Tr (Θ - w)⁻¹`.  The only
hypotheses are that the two resolvent points avoid the spectrum.

Unconditional.  Nothing here constrains where the zeros are. -/
theorem resolvent_trace_eq_neg_logDeriv_diff {w w₀ : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw₀ : (1 / 2 + Complex.I * w₀) ∉ ZD.NontrivialZeros) :
    ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ - (spectralCoord ρ.val - w₀)⁻¹)
      = -((deriv spectralDet w / spectralDet w)
            - (deriv spectralDet w₀ / spectralDet w₀)) := by
  rw [hilbertPolya_resolvent_trace hw hw₀, logDeriv_spectralDet w,
    logDeriv_spectralDet w₀]
  ring

/-! ## The determinant property

Everything below turns the docstring claim "zeros of `spectralDet` are exactly
the spectral coordinates" into theorems: chart bijection, analyticity, finite
order, zero-set identification, multiplicity transport, and the Hadamard
product in the spectral chart. -/

/-- The spectral chart inverts the spectral coordinate: `1/2 + i·t(ρ) = ρ`. -/
theorem chart_spectralCoord (ρ : ℂ) : 1 / 2 + Complex.I * spectralCoord ρ = ρ := by
  unfold spectralCoord
  linear_combination (-(ρ - 1 / 2)) * Complex.I_mul_I

/-- The spectral coordinate inverts the chart: `t(1/2 + i·w) = w`. -/
theorem spectralCoord_chart (w : ℂ) : spectralCoord (1 / 2 + Complex.I * w) = w := by
  unfold spectralCoord
  linear_combination (-w) * Complex.I_mul_I

/-- The spectral chart `w ↦ 1/2 + i·w` is analytic. -/
theorem chartMap_analyticAt (w : ℂ) :
    AnalyticAt ℂ (fun v : ℂ => 1 / 2 + Complex.I * v) w :=
  analyticAt_const.add (analyticAt_const.mul analyticAt_id)

/-- `spectralDet` is analytic at every point (entire). -/
theorem spectralDet_analyticAt (w : ℂ) : AnalyticAt ℂ spectralDet w := by
  have h : AnalyticAt ℂ (ZD.riemannXi ∘ fun v : ℂ => 1 / 2 + Complex.I * v) w :=
    (ZD.riemannXi_differentiable.analyticAt _).comp (chartMap_analyticAt w)
  exact h

/-- The spectral chart tends to its image point. -/
theorem chart_tendsto (w₀ : ℂ) :
    Tendsto (fun w : ℂ => 1 / 2 + Complex.I * w) (𝓝 w₀)
      (𝓝 (1 / 2 + Complex.I * w₀)) :=
  (continuous_const.add (continuous_const.mul continuous_id)).tendsto w₀

/-- `spectralDet` has finite analytic order everywhere: it never vanishes on a
neighbourhood, because `ξ` does not and the chart is a homeomorphism. -/
theorem spectralDet_analyticOrderAt_ne_top (w₀ : ℂ) :
    analyticOrderAt spectralDet w₀ ≠ ⊤ := by
  intro htop
  have hev : ∀ᶠ w in 𝓝 w₀, spectralDet w = 0 := analyticOrderAt_eq_top.mp htop
  have hcont : Tendsto spectralCoord (𝓝 (1 / 2 + Complex.I * w₀)) (𝓝 w₀) := by
    have h : Continuous spectralCoord := by
      unfold spectralCoord
      fun_prop
    have h2 := h.tendsto (1 / 2 + Complex.I * w₀)
    rwa [spectralCoord_chart] at h2
  have hev' : ∀ᶠ s in 𝓝 (1 / 2 + Complex.I * w₀), ZD.riemannXi s = 0 := by
    filter_upwards [hcont.eventually hev] with s hs
    simp only [spectralDet] at hs
    rwa [chart_spectralCoord] at hs
  exact ZD.riemannXi_analyticOrderAt_ne_top_everywhere _ (analyticOrderAt_eq_top.mpr hev')

/-- **Multiplicity correspondence.**  The analytic vanishing order of
`spectralDet` at any point equals the ξ-order at its chart image: the local
factorization `ξ(s) = (s - s₀)ⁿ·g(s)` transports through the affine chart
`w ↦ 1/2 + i·w`, the unit picking up the factor `iⁿ`. -/
theorem spectralDet_analyticOrderNatAt (w₀ : ℂ) :
    analyticOrderNatAt spectralDet w₀ = ZD.xiOrderNat (1 / 2 + Complex.I * w₀) := by
  have hxi_ana : AnalyticAt ℂ ZD.riemannXi (1 / 2 + Complex.I * w₀) :=
    ZD.riemannXi_differentiable.analyticAt _
  have hxi_ne := ZD.riemannXi_analyticOrderAt_ne_top_everywhere (1 / 2 + Complex.I * w₀)
  obtain ⟨g, hg, hg0, hev⟩ := (hxi_ana.analyticOrderNatAt_eq_iff hxi_ne).mp rfl
  refine ((spectralDet_analyticAt w₀).analyticOrderNatAt_eq_iff
      (spectralDet_analyticOrderAt_ne_top w₀)).mpr
    ⟨fun w => Complex.I ^ ZD.xiOrderNat (1 / 2 + Complex.I * w₀) *
        g (1 / 2 + Complex.I * w), ?_, ?_, ?_⟩
  · have hgc : AnalyticAt ℂ (fun w : ℂ => g (1 / 2 + Complex.I * w)) w₀ :=
      hg.comp_of_eq (chartMap_analyticAt w₀) rfl
    exact analyticAt_const.mul hgc
  · exact mul_ne_zero (pow_ne_zero _ Complex.I_ne_zero) hg0
  · filter_upwards [(chart_tendsto w₀).eventually hev] with w hw
    calc spectralDet w
        = ((1 / 2 + Complex.I * w) - (1 / 2 + Complex.I * w₀)) ^
            ZD.xiOrderNat (1 / 2 + Complex.I * w₀) • g (1 / 2 + Complex.I * w) := hw
      _ = (w - w₀) ^ ZD.xiOrderNat (1 / 2 + Complex.I * w₀) •
            (Complex.I ^ ZD.xiOrderNat (1 / 2 + Complex.I * w₀) *
              g (1 / 2 + Complex.I * w)) := by
          simp only [smul_eq_mul]
          rw [show (1 / 2 + Complex.I * w) - (1 / 2 + Complex.I * w₀)
              = Complex.I * (w - w₀) by ring, mul_pow]
          ring

/-- Zeros of the determinant are the nontrivial zeros, read in the chart. -/
theorem spectralDet_eq_zero_iff (w : ℂ) :
    spectralDet w = 0 ↔ (1 / 2 + Complex.I * w) ∈ ZD.NontrivialZeros :=
  ZD.riemannXi_eq_zero_iff _

/-- **Zero set = spectrum.**  `spectralDet` vanishes at `w` iff `w` is the
spectral coordinate of a nontrivial zero. -/
theorem spectralDet_eq_zero_iff_spectralCoord (w : ℂ) :
    spectralDet w = 0 ↔ ∃ ρ ∈ ZD.NontrivialZeros, w = spectralCoord ρ := by
  rw [spectralDet_eq_zero_iff]
  constructor
  · intro h
    exact ⟨1 / 2 + Complex.I * w, h, (spectralCoord_chart w).symm⟩
  · rintro ⟨ρ, hρ, rfl⟩
    rwa [chart_spectralCoord]

/-- The determinant vanishes at the spectral coordinate of every zero. -/
theorem spectralDet_spectralCoord_eq_zero {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    spectralDet (spectralCoord ρ) = 0 := by
  rw [spectralDet_eq_zero_iff, chart_spectralCoord]
  exact hρ

/-- **Multiplicity at the spectrum**: the determinant's vanishing order at the
spectral coordinate of any point is exactly its ξ-multiplicity. -/
theorem spectralDet_orderNat_spectralCoord (ρ : ℂ) :
    analyticOrderNatAt spectralDet (spectralCoord ρ) = ZD.xiOrderNat ρ := by
  rw [spectralDet_analyticOrderNatAt, chart_spectralCoord]

/-- At a nontrivial zero the determinant's vanishing order is positive. -/
theorem spectralDet_orderNat_pos {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    0 < analyticOrderNatAt spectralDet (spectralCoord ρ) := by
  rw [spectralDet_orderNat_spectralCoord]
  exact ZD.xiOrderNat_pos_of_mem_NontrivialZeros hρ

/-- **The determinant is the canonical product over the spectrum** — Hadamard
factorization in the spectral chart: a nonvanishing entire exponential times
the multiplicity-indexed Weierstrass product over the zero multiset. -/
theorem spectralDet_hadamard_factorization :
    ∃ A B : ℂ, ∀ w : ℂ,
      spectralDet w
        = Complex.exp (A * w + B) * ZD.xiProductMult (1 / 2 + Complex.I * w) := by
  obtain ⟨A, B, h⟩ := ZD.riemannXi_hadamard_factorization
  refine ⟨A * Complex.I, A / 2 + B, fun w => ?_⟩
  calc spectralDet w
      = Complex.exp (A * (1 / 2 + Complex.I * w) + B)
          * ZD.xiProductMult (1 / 2 + Complex.I * w) := h _
    _ = Complex.exp (A * Complex.I * w + (A / 2 + B))
          * ZD.xiProductMult (1 / 2 + Complex.I * w) := by
        rw [show A * (1 / 2 + Complex.I * w) + B
            = A * Complex.I * w + (A / 2 + B) by ring]

end CriticalLinePhasor.FoliatedDeterminant

section AxiomAudit
#print axioms CriticalLinePhasor.FoliatedDeterminant.deriv_spectralDet
#print axioms CriticalLinePhasor.FoliatedDeterminant.resolvent_trace_eq_neg_logDeriv_diff
#print axioms CriticalLinePhasor.FoliatedDeterminant.spectralDet_eq_zero_iff_spectralCoord
#print axioms CriticalLinePhasor.FoliatedDeterminant.spectralDet_analyticOrderNatAt
#print axioms CriticalLinePhasor.FoliatedDeterminant.spectralDet_orderNat_spectralCoord
#print axioms CriticalLinePhasor.FoliatedDeterminant.spectralDet_hadamard_factorization
end AxiomAudit
