import RequestProject.WeilTestClass
import RequestProject.RiemannHypothesisBridge
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# The carrier-only door: positivity of the prime–Γ functional on autocorrelations ⟹ every zero on the axis
(ledger 1335)

Sam (2026-10-14): "you are mixing the chart and carrier arbitrarily" — the doors 1326–1331 were chart statements.
Here the leaf is stated with no chart in it. The compiled explicit formula (Track W, no window) equates, for every
smooth compactly supported profile `g`,

  zero side  `Σ_ρ m_ρ F(ρ)`  =  carrier side  `(1/2π)[∫F·E on two lines] − Σ_n Λ(n) n^{−½}(g(log n) + g(−log n))`,

`F = laplaceTest g`, `E = weilArch` the Γ-clock. The carrier side is primes at their heights `±log n` consumed with
the fixed amplitude `n^{−½}`, plus the Γ-clock: carrier data only. For an autocorrelation `g = h ⋆ h̃`:

* `laplaceTest_autocorr`: `F(s) = H(s)·conj H(1 − s̄)` (Laplace transform of a convolution is the product;
  `integral_convolution`), and on the axis `F(ρ) = |H(ρ)|²` (`laplaceTest_autocorr_axis`): axis zeros contribute
  nonnegatively; an off-axis pair contributes `2 Re[H(ρ)·conj H(ρ*)]`, indefinite.
* `carrierSide_eq_zeroSide`: the explicit formula for `g = h ⋆ h̃` (`autocorr_contDiff`, `autocorr_hasCompactSupport`).
* `CarrierPositive a b`: the carrier functional is nonnegative on every autocorrelation.
* `WeilWitness`: for every off-axis zero there is a test `h` whose zero side is negative — the ONE object to exhibit
  (Weil's criterion, hard direction). Probed in 1334: `H_λ(z) = (z − c)e^{λ(z−ρ₀)²}` detects every synthetic pair
  tried; its compiled form needs the explicit formula for Gaussian-decay tests and the dominance over all zeros.
* `axis_of_carrierPositive`, `riemannHypothesis_of_carrierPositive`: positivity + witness ⟹ RH.

No `sorry`, no `axiom`, no window.
-/

open Complex MeasureTheory Filter Topology
open scoped ContDiff Real Convolution ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.HelixCarrierWeil

open CriticalLinePhasor.ContourArgument

/-- Pointwise multiplication on `ℂ` as a real-bilinear map (the convolution's pairing). -/
abbrev L : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.mul ℝ ℂ

/-- The reflected conjugate profile `h̃(x) = conj h(−x)`. -/
def reflect (h : ℝ → ℂ) (x : ℝ) : ℂ := conj (h (-x))

/-- The autocorrelation `h ⋆ h̃`. -/
def autocorr (h : ℝ → ℂ) : ℝ → ℂ := h ⋆[L] reflect h

theorem reflect_eq (h : ℝ → ℂ) : reflect h = ⇑Complex.conjCLE ∘ (h ∘ fun x : ℝ => -x) := by
  funext x; simp [reflect]

theorem reflect_hasCompactSupport {h : ℝ → ℂ} (hc : HasCompactSupport h) : HasCompactSupport (reflect h) := by
  rw [reflect_eq]
  exact (hc.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (map_zero _)

theorem reflect_continuous {h : ℝ → ℂ} (hd : Continuous h) : Continuous (reflect h) := by
  rw [reflect_eq]
  exact Complex.conjCLE.continuous.comp (hd.comp continuous_neg)

theorem reflect_contDiff {h : ℝ → ℂ} (hd : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (reflect h) := by
  rw [reflect_eq]
  exact Complex.conjCLE.contDiff.comp (hd.comp contDiff_neg)

theorem autocorr_hasCompactSupport {h : ℝ → ℂ} (hc : HasCompactSupport h) : HasCompactSupport (autocorr h) :=
  HasCompactSupport.convolution L hc (reflect_hasCompactSupport hc)

theorem autocorr_contDiff {h : ℝ → ℂ} (hd : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) :
    ContDiff ℝ ∞ (autocorr h) :=
  HasCompactSupport.contDiff_convolution_right L (reflect_hasCompactSupport hc)
    hd.continuous.locallyIntegrable (reflect_contDiff hd)

/-! ## The Laplace transform of a convolution is the product -/

theorem laplaceTest_convolution {f g : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) (s : ℂ) :
    laplaceTest (f ⋆[L] g) s = laplaceTest f s * laplaceTest g s := by
  set e : ℝ → ℂ := fun x => Complex.exp ((s - 1 / 2) * x) with he
  have hecont : Continuous e := by
    simp only [he]; fun_prop
  have hfe : Integrable (f * e) := (hf.mul hecont).integrable_of_hasCompactSupport hfc.mul_right
  have hge : Integrable (g * e) := (hg.mul hecont).integrable_of_hasCompactSupport hgc.mul_right
  have hsplit : ∀ x t : ℝ, e x = e t * e (x - t) := by
    intro x t
    simp only [he]
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hconv : ∀ x : ℝ, (f ⋆[L] g) x * e x = ((f * e) ⋆[L] (g * e)) x := by
    intro x
    simp only [convolution_def, ContinuousLinearMap.mul_apply', Pi.mul_apply]
    rw [← integral_mul_const]
    congr 1
    funext t
    rw [hsplit x t]
    ring
  have h1 : laplaceTest (f ⋆[L] g) s = ∫ x : ℝ, ((f * e) ⋆[L] (g * e)) x := by
    unfold laplaceTest
    congr 1
    funext x
    exact hconv x
  rw [h1, integral_convolution L hfe hge, ContinuousLinearMap.mul_apply']
  rfl

/-- The reflected conjugate profile transforms to the conjugate at the mirror point `1 − s̄`. -/
theorem laplaceTest_reflect (h : ℝ → ℂ) (s : ℂ) :
    laplaceTest (reflect h) s = conj (laplaceTest h (1 - conj s)) := by
  unfold laplaceTest reflect
  rw [← integral_conj]
  have hpt : ∀ x : ℝ, conj (h (-x)) * Complex.exp ((s - 1 / 2) * x)
      = conj (h (-x) * Complex.exp (((1 - conj s) - 1 / 2) * ((-x : ℝ) : ℂ))) := by
    intro x
    rw [map_mul, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, map_sub, map_one, Complex.conj_conj, Complex.conj_ofReal, map_div₀, map_ofNat]
    push_cast
    ring
  simp_rw [hpt]
  exact integral_neg_eq_self (fun x : ℝ => conj (h x * Complex.exp (((1 - conj s) - 1 / 2) * (x : ℂ)))) volume

/-- **The autocorrelation's transform is `H(s)·conj H(1 − s̄)`.** -/
theorem laplaceTest_autocorr {h : ℝ → ℂ} (hd : Continuous h) (hc : HasCompactSupport h) (s : ℂ) :
    laplaceTest (autocorr h) s = laplaceTest h s * conj (laplaceTest h (1 - conj s)) := by
  unfold autocorr
  rw [laplaceTest_convolution hd hc (reflect_continuous hd) (reflect_hasCompactSupport hc), laplaceTest_reflect]

/-- **On the axis the autocorrelation's transform is `|H|²`**: axis zeros contribute nonnegatively. -/
theorem laplaceTest_autocorr_axis {h : ℝ → ℂ} (hd : Continuous h) (hc : HasCompactSupport h) {s : ℂ}
    (hs : s.re = 1 / 2) :
    laplaceTest (autocorr h) s = (Complex.normSq (laplaceTest h s) : ℂ) := by
  rw [laplaceTest_autocorr hd hc]
  have hmir : (1 : ℂ) - conj s = s := by
    apply Complex.ext
    · simp [Complex.conj_re]; linarith
    · simp [Complex.conj_im]
  rw [hmir, Complex.mul_conj]

/-! ## The two sides of the explicit formula as carrier and zero functionals -/

/-- The zero side: the chart's zero comb paired with the transform. -/
def zeroSide (g : ℝ → ℂ) : ℂ := ∑' ρ : Zero, (ZD.xiOrderNat ρ.val : ℂ) * laplaceTest g ρ.val

/-- The carrier side: the Γ-clock on two lines and the primes at their heights with amplitude `n^{−½}`. -/
def carrierSide (g : ℝ → ℂ) (a b : ℝ) : ℂ :=
  (1 / (2 * π)) * ((∫ t : ℝ, laplaceTest g (b + t * I) * weilArch (b + t * I))
      + (∫ t : ℝ, laplaceTest g (a + t * I) * weilArch (1 - ((a : ℂ) + t * I))))
    - ∑' n : ℕ, primeWeight n * (g (Real.log n) + g (-Real.log n))

/-- **The explicit formula**: carrier side = zero side, for smooth compactly supported profiles. -/
theorem carrierSide_eq_zeroSide {g : ℝ → ℂ} (hg : ContDiff ℝ ∞ g) (hs : HasCompactSupport g) {a b : ℝ}
    (ha : a < 0) (hb : 1 < b) : carrierSide g a b = zeroSide g :=
  (weil_explicit_formula_smooth hg hs ha hb).symm

/-- **Carrier positivity**: the prime–Γ functional is nonnegative on every autocorrelation. -/
def CarrierPositive (a b : ℝ) : Prop :=
  ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → HasCompactSupport h → 0 ≤ (carrierSide (autocorr h) a b).re

/-- **The Weil witness** (the one object to exhibit): every off-axis zero is detected by some test — a profile whose
autocorrelation has negative zero side. -/
def WeilWitness : Prop :=
  ∀ ρ ∈ ZD.NontrivialZeros, ρ.re ≠ 1 / 2 →
    ∃ h : ℝ → ℂ, ContDiff ℝ ∞ h ∧ HasCompactSupport h ∧ (zeroSide (autocorr h)).re < 0

/-- **The carrier-only door**: carrier positivity and the witness put every zero on the axis. -/
theorem axis_of_carrierPositive {a b : ℝ} (ha : a < 0) (hb : 1 < b) (hpos : CarrierPositive a b)
    (hwit : WeilWitness) : ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2 := by
  intro ρ hρ
  by_contra hne
  obtain ⟨h, hd, hc, hneg⟩ := hwit ρ hρ hne
  have hge := hpos h hd hc
  rw [carrierSide_eq_zeroSide (autocorr_contDiff hd hc) (autocorr_hasCompactSupport hc) ha hb] at hge
  linarith

theorem riemannHypothesis_of_carrierPositive {a b : ℝ} (ha : a < 0) (hb : 1 < b) (hpos : CarrierPositive a b)
    (hwit : WeilWitness) : RiemannHypothesis :=
  RHBridge.no_offline_zeros_implies_rh (axis_of_carrierPositive ha hb hpos hwit)

end CriticalLinePhasor.HelixCarrierWeil

end

#print axioms CriticalLinePhasor.HelixCarrierWeil.laplaceTest_autocorr
#print axioms CriticalLinePhasor.HelixCarrierWeil.laplaceTest_autocorr_axis
#print axioms CriticalLinePhasor.HelixCarrierWeil.carrierSide_eq_zeroSide
#print axioms CriticalLinePhasor.HelixCarrierWeil.riemannHypothesis_of_carrierPositive
