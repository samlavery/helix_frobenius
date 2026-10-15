import RequestProject.HelixFiberIsTwoEnded
import RequestProject.HelixFootMass
import RequestProject.ZetaZeroDefs

/-!
# Every zero of ζ has a source: two nonzero feet of the native bank that cancel (ledger 1270)

Sam (2026-10-12): "write it to reach riemannZeta then. EveryZeroHasSource is a false obstruction."

A **source** (Sam's definition, ledger 693) is an exact cancellation of two nonzero banks. Here: two nonzero feet of
the native Gaussian bank's two-ended fiber, at one height, cancelling exactly. The two feet at offset `v` from the
origin are the helix end at `v` and the J-image of the helix end at the mirrored offset `−v̄`
(`HelixOriginCentered.origin_two_ended`). This file reaches `riemannZeta` by design.

* `foot_bound_gen`: the zero-mode dominance of 1263, extended to every exponent `0 < Re s ≤ 1`:
  `‖s·E(c,s)‖ ≥ c^{Re s} − 4·Re s·e^{−c}` for cuts at or above the origin.
* `sourceConfig_mass_pos`: for every offset with `|Re v| < ¼`, both feet are nonzero at one cut or the other.
  The mass is positive at every cut.
* `sourceConfig_cancels_iff`: the feet cancel exactly when `ζ(½ + 2v) = 0`.
* **`every_zero_has_source`**: for every nontrivial zero `ρ` and every cut, the two feet at offset
  `v = ρ/2 − ¼` cancel, with positive mass, at height `e^{Im ρ}`. Every zero has a source.
* `sourceConfig_axis`: the source at an on-axis offset IS the native construction `twoEndedConfig`.
* `source_offset_re`: the source's transverse offset is `Re v = (Re ρ − ½)/2`, so the source is on the axis
  exactly when `Re ρ = ½` (`source_on_axis_iff`).

So "every zero has a source" is a theorem. What remains is that the source sits on the axis, i.e. that its offset is
zero. That is the house's `Source.SourcesOfZerosOnAxis`.
-/

open Complex Set MeasureTheory Filter Topology
open scoped ComplexConjugate Interval

noncomputable section

namespace CriticalLinePhasor.HelixZetaSource

open CriticalLinePhasor CriticalLinePhasor.GlobalHelix CriticalLinePhasor.HelixTwoEndedClosure
  CriticalLinePhasor.HelixTwoEndedNative CriticalLinePhasor.HelixOriginCentered
  CriticalLinePhasor.HelixTwoEndedCancellation CriticalLinePhasor.HelixFootMass

/-! ## 1. Zero-mode dominance at every exponent `0 < Re s ≤ 1` -/

theorem byParts_pow {c R a : ℝ} (hc : 0 < c) (hcR : c ≤ R) :
    ∫ x in c..R, x ^ a * bankSlope x =
      R ^ a * (gaussianLatticeTheta R - 1) - c ^ a * (gaussianLatticeTheta c - 1) -
        a * ∫ x in c..R, x ^ (a - 1) * (gaussianLatticeTheta x - 1) := by
  have hu : ∀ x ∈ [[c, R]], HasDerivAt (fun y : ℝ => y ^ a) (a * x ^ (a - 1)) x :=
    fun x hx => Real.hasDerivAt_rpow_const (Or.inl (pos_of_mem hc hcR hx).ne')
  have hv : ∀ x ∈ [[c, R]], HasDerivAt (fun y : ℝ => gaussianLatticeTheta y - 1) (bankSlope x) x :=
    fun x hx => (hasDerivAt_theta (pos_of_mem hc hcR hx)).sub_const 1
  have hu' : IntervalIntegrable (fun x : ℝ => a * x ^ (a - 1)) volume c R := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    exact (continuousAt_const.mul
      (Real.continuousAt_rpow_const _ _ (Or.inl (pos_of_mem hc hcR hx).ne'))).continuousWithinAt
  have hv' : IntervalIntegrable bankSlope volume c R :=
    (continuousOn_bankSlope.mono fun x hx => pos_of_mem hc hcR hx).intervalIntegrable
  rw [intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv']
  simp_rw [mul_assoc]
  rw [intervalIntegral.integral_const_mul]

theorem foot_bound_finite_gen {c R a : ℝ} (hc : 0 < c) (hcR : c ≤ R) {s : ℂ} (hs : s.re = a) :
    c ^ a - a * ∫ x in c..R, x ^ (a - 1) * (gaussianLatticeTheta x - 1) ≤
      ‖s * (∫ x in c..R, (x : ℂ) ^ (s - 1) * ((gaussianLatticeTheta x : ℂ) - 1)) - (c : ℂ) ^ s‖ := by
  have hR : 0 < R := hc.trans_le hcR
  have hA := byParts hc hcR s
  have hAr := byParts_pow (a := a) hc hcR
  set A := ∫ x in c..R, (x : ℂ) ^ s * (bankSlope x : ℂ) with hAdef
  set J := ∫ x in c..R, (x : ℂ) ^ (s - 1) * ((gaussianLatticeTheta x : ℂ) - 1)
  have hnormA : ‖A‖ ≤ -∫ x in c..R, x ^ a * bankSlope x := by
    calc ‖A‖ ≤ ∫ x in c..R, ‖(x : ℂ) ^ s * (bankSlope x : ℂ)‖ :=
          intervalIntegral.norm_integral_le_integral_norm hcR
      _ = ∫ x in c..R, -(x ^ a * bankSlope x) := by
          apply intervalIntegral.integral_congr
          intro x hx
          have hx0 := pos_of_mem hc hcR hx
          simp only
          rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, hs, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonpos (bankSlope_nonpos hx0)]
          ring
      _ = -∫ x in c..R, x ^ a * bankSlope x := intervalIntegral.integral_neg
  have hθc := one_le_theta hc
  have hθR := one_le_theta hR
  have h1 : ‖(c : ℂ) ^ s * (gaussianLatticeTheta c : ℂ)‖ = c ^ a * gaussianLatticeTheta c := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hc, hs, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  have h2 : ‖(R : ℂ) ^ s * ((gaussianLatticeTheta R : ℂ) - 1)‖ = R ^ a * (gaussianLatticeTheta R - 1) := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hR, hs,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hkey : (c : ℂ) ^ s * (gaussianLatticeTheta c : ℂ) =
      (R : ℂ) ^ s * ((gaussianLatticeTheta R : ℂ) - 1) - A - (s * J - (c : ℂ) ^ s) := by
    rw [hA]
    ring
  have htri : ‖(c : ℂ) ^ s * (gaussianLatticeTheta c : ℂ)‖ ≤
      ‖(R : ℂ) ^ s * ((gaussianLatticeTheta R : ℂ) - 1)‖ + ‖A‖ + ‖s * J - (c : ℂ) ^ s‖ := by
    rw [hkey]
    exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  rw [h1, h2] at htri
  linarith

theorem modes_integral_le_gen {c R a : ℝ} (hc : 1 ≤ c) (hcR : c ≤ R) (ha1 : a ≤ 1) :
    ∫ x in c..R, x ^ (a - 1) * (gaussianLatticeTheta x - 1) ≤ 4 * Real.exp (-c) := by
  have hc0 : 0 < c := by linarith
  have hint : IntervalIntegrable (fun x : ℝ => x ^ (a - 1) * (gaussianLatticeTheta x - 1)) volume c R := by
    apply ContinuousOn.intervalIntegrable
    intro x hx
    have hx0 := pos_of_mem hc0 hcR hx
    exact ((Real.continuousAt_rpow_const _ _ (Or.inl hx0.ne')).continuousWithinAt).mul
      ((gaussianLatticeTheta_continuousOn.mono fun y hy => pos_of_mem hc0 hcR hy) x hx |>.sub
        continuousWithinAt_const)
  have hexp : IntervalIntegrable (fun x : ℝ => 4 * Real.exp (-x)) volume c R :=
    (by fun_prop : Continuous fun x : ℝ => 4 * Real.exp (-x)).intervalIntegrable _ _
  have hmono : ∫ x in c..R, x ^ (a - 1) * (gaussianLatticeTheta x - 1) ≤ ∫ x in c..R, 4 * Real.exp (-x) := by
    apply intervalIntegral.integral_mono_on hcR hint hexp
    intro x hx
    have hx1 : 1 ≤ x := hc.trans hx.1
    have hx0 : 0 < x := by linarith
    have hg0 : 0 ≤ gaussianLatticeTheta x - 1 := by linarith [one_le_theta hx0]
    have hp : x ^ (a - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    calc x ^ (a - 1) * (gaussianLatticeTheta x - 1) ≤ 1 * (gaussianLatticeTheta x - 1) :=
          mul_le_mul_of_nonneg_right hp hg0
      _ ≤ 4 * Real.exp (-x) := by linarith [bank_modes_le hx1]
  have hcalc : ∫ x in c..R, 4 * Real.exp (-x) = 4 * (Real.exp (-c) - Real.exp (-R)) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x : ℝ => -Real.exp (-x))
      (f' := fun x : ℝ => Real.exp (-x)) (a := c) (b := R)
      (fun x _ => (((hasDerivAt_neg x).exp).neg).congr_deriv (by ring))
      ((by fun_prop : Continuous fun x : ℝ => Real.exp (-x)).intervalIntegrable _ _)
    rw [this]
    ring
  have hR := Real.exp_pos (-R)
  linarith

/-- **Zero-mode dominance at every exponent `0 < a ≤ 1`**, for cuts at or above the origin. -/
theorem foot_bound_gen {c a : ℝ} (hc : 1 ≤ c) (ha0 : 0 < a) (ha1 : a ≤ 1) {s : ℂ} (hs : s.re = a) :
    c ^ a - 4 * a * Real.exp (-c) ≤ ‖s * helixEndAt nativePair c s‖ := by
  have hc0 : 0 < c := by linarith
  have hs0 : s ≠ 0 := fun h => by rw [h, Complex.zero_re] at hs; linarith
  have hE : s * helixEndAt nativePair c s = s * helixStrandAt nativePair c s - (c : ℂ) ^ s := by
    unfold helixEndAt
    have : nativePair.f₀ = 1 := rfl
    rw [this]
    field_simp
  have hlim0 := intervalIntegral_tendsto_integral_Ioi c (integrableOn_strand nativePair hc0 s) tendsto_id
  have hlim : Tendsto (fun R : ℝ => ∫ x in c..R, (x : ℂ) ^ (s - 1) * ((gaussianLatticeTheta x : ℂ) - 1))
      atTop (𝓝 (helixStrandAt nativePair c s)) := by
    refine hlim0.congr' ?_
    filter_upwards [eventually_ge_atTop c] with R hR
    apply intervalIntegral.integral_congr
    intro x hx
    beta_reduce
    have : nativePair.f x = (gaussianLatticeTheta x : ℂ) := helixBank_eq (pos_of_mem hc0 hR hx)
    rw [this]
    rfl
  have hlim2 := ((hlim.const_mul s).sub_const ((c : ℂ) ^ s)).norm
  rw [hE]
  apply ge_of_tendsto hlim2
  filter_upwards [eventually_ge_atTop c] with R hR
  have h1 := foot_bound_finite_gen hc0 hR hs
  have h2 := mul_le_mul_of_nonneg_left (modes_integral_le_gen hc hR ha1) ha0.le
  linarith

/-- A helix end above a cut at or above the origin never vanishes, at every exponent `0 < Re s ≤ ½`. -/
theorem helixEndAt_ne_zero_gen {c : ℝ} (hc : 1 ≤ c) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re ≤ 1 / 2) :
    helixEndAt nativePair c s ≠ 0 := by
  intro h
  have hb := foot_bound_gen hc h0 (by linarith) rfl
  rw [h, mul_zero, norm_zero] at hb
  have hca : 1 ≤ c ^ s.re := Real.one_le_rpow hc h0.le
  have he1 : Real.exp (-c) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have he2 := Real.exp_neg_one_lt_half
  have hepos := Real.exp_pos (-c)
  nlinarith

/-! ## 2. The source configuration: two feet at offset `v` -/

/-- The two feet at offset `v`, labelled with height `Z`: the helix end at `v` above the cut `hc`, and the J-image
of the helix end at the mirrored offset `−v̄` above the reflected cut `−hc`. -/
def sourceConfig (v : ℂ) (Z hc : ℝ) : FocalFeet.PhasorConfig :=
  ⟨Z, 2, ![originEnd nativePair (Real.exp hc) v, conj (originEnd nativePair (Real.exp (-hc)) (-conj v))]⟩

theorem sourceConfig_resultant_feet (v : ℂ) (Z hc : ℝ) : (sourceConfig v Z hc).resultant =
    originEnd nativePair (Real.exp hc) v + conj (originEnd nativePair (Real.exp (-hc)) (-conj v)) := by
  show ∑ k : Fin 2, (![originEnd nativePair (Real.exp hc) v,
    conj (originEnd nativePair (Real.exp (-hc)) (-conj v))] : Fin 2 → ℂ) k = _
  rw [Fin.sum_univ_two]
  rfl

theorem sourceConfig_mass (v : ℂ) (Z hc : ℝ) : (sourceConfig v Z hc).mass =
    ‖originEnd nativePair (Real.exp hc) v‖ + ‖conj (originEnd nativePair (Real.exp (-hc)) (-conj v))‖ := by
  show ∑ k : Fin 2, ‖(![originEnd nativePair (Real.exp hc) v,
    conj (originEnd nativePair (Real.exp (-hc)) (-conj v))] : Fin 2 → ℂ) k‖ = _
  rw [Fin.sum_univ_two]
  rfl

theorem offset_re (v : ℂ) : ((nativePair.k : ℂ) / 2 + v).re = 1 / 4 + v.re := by
  rw [nativePair_k]
  simp
  norm_num

theorem mirror_re (v : ℂ) : ((nativePair.k : ℂ) / 2 + -conj v).re = 1 / 4 - v.re := by
  rw [nativePair_k]
  simp
  norm_num
  ring

/-- **The source has positive mass at every cut**, for every offset in the band `|Re v| < ¼`. -/
theorem sourceConfig_mass_pos {v : ℂ} (hv : |v.re| < 1 / 4) (Z hc : ℝ) : 0 < (sourceConfig v Z hc).mass := by
  rw [sourceConfig_mass]
  have hv1 := (abs_lt.mp hv).1
  have hv2 := (abs_lt.mp hv).2
  rcases le_total 0 hc with h | h
  · have hne : originEnd nativePair (Real.exp hc) v ≠ 0 :=
      helixEndAt_ne_zero_gen (Real.one_le_exp h) (by rw [offset_re]; linarith) (by rw [offset_re]; linarith)
    exact add_pos_of_pos_of_nonneg (norm_pos_iff.mpr hne) (norm_nonneg _)
  · have hne : originEnd nativePair (Real.exp (-hc)) (-conj v) ≠ 0 :=
      helixEndAt_ne_zero_gen (Real.one_le_exp (by linarith)) (by rw [mirror_re]; linarith)
        (by rw [mirror_re]; linarith)
    refine add_pos_of_nonneg_of_pos (norm_nonneg _) ?_
    rw [Complex.norm_conj]
    exact norm_pos_iff.mpr hne

/-- The two feet sum to the native two-ended fiber at offset `v`. -/
theorem sourceConfig_resultant {v : ℂ} (hv : |v.re| < 1 / 4) (Z hc : ℝ) :
    (sourceConfig v Z hc).resultant = originΛ nativePair v := by
  have hv1 := (abs_lt.mp hv).1
  have hv2 := (abs_lt.mp hv).2
  have hv0 : (nativePair.k : ℂ) / 2 + v ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [offset_re, Complex.zero_re] at this
    linarith
  have hvk : (nativePair.k : ℂ) / 2 + v ≠ nativePair.k := by
    intro h
    have := congrArg Complex.re h
    rw [offset_re, nativePair_k] at this
    norm_num at this
    linarith
  have h := origin_two_ended nativePair nativePair_conj nativePair_conj₀ (Real.exp_pos hc) hv0 hvk
  rw [show nativePair.ε = 1 from rfl, one_mul, ← Real.exp_neg] at h
  rw [sourceConfig_resultant_feet, ← h]

/-- **The feet cancel exactly when ζ vanishes at `½ + 2v`**, in the band. -/
theorem sourceConfig_cancels_iff {v : ℂ} (hv : |v.re| < 1 / 4) (Z hc : ℝ) :
    (sourceConfig v Z hc).Cancels ↔ riemannZeta (1 / 2 + 2 * v) = 0 := by
  have hv1 := (abs_lt.mp hv).1
  set s : ℂ := 1 / 2 + 2 * v with hsdef
  have hsre : s.re = 1 / 2 + 2 * v.re := by simp [hsdef]
  have hs0 : s ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hsre, Complex.zero_re] at this
    linarith
  have hΓ : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; linarith)
  unfold FocalFeet.PhasorConfig.Cancels
  rw [sourceConfig_resultant hv]
  unfold originΛ
  rw [nativePair_Λ]
  have hr := originΛ_readout v
  unfold originΛ at hr
  rw [show ((HurwitzZeta.hurwitzEvenFEPair 0).k : ℂ) = nativePair.k from rfl] at hr
  rw [hr, riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff, or_iff_left hΓ]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left two_ne_zero
  · intro h
    rw [h, mul_zero]

/-- **On the axis, the source is the native construction.** -/
theorem sourceConfig_axis (Z hc : ℝ) : sourceConfig (eventOffset Z) Z hc = twoEndedConfig Z hc := by
  unfold sourceConfig twoEndedConfig helixFoot antiHelixFoot
  rw [eventOffset_mirror]

/-! ## 3. Every zero has a source -/

theorem zero_offset_band {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) : |(ρ / 2 - 1 / 4).re| < 1 / 4 := by
  obtain ⟨h0, h1, _⟩ := hρ
  have : (ρ / 2 - 1 / 4).re = ρ.re / 2 - 1 / 4 := by simp
  rw [this, abs_lt]
  constructor <;> linarith

/-- **Every nontrivial zero has a source**: at height `e^{Im ρ}` and at every cut, the two nonzero feet of the
native bank at offset `v = ρ/2 − ¼` cancel exactly, and their mass is positive. -/
theorem every_zero_has_source {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) (hc : ℝ) :
    (sourceConfig (ρ / 2 - 1 / 4) (Real.exp ρ.im) hc).Cancels ∧
      0 < (sourceConfig (ρ / 2 - 1 / 4) (Real.exp ρ.im) hc).mass := by
  have hband := zero_offset_band hρ
  refine ⟨(sourceConfig_cancels_iff hband _ hc).mpr ?_, sourceConfig_mass_pos hband _ hc⟩
  have : (1 / 2 : ℂ) + 2 * (ρ / 2 - 1 / 4) = ρ := by ring
  rw [this]
  exact hρ.2.2

/-- The source's transverse offset. -/
theorem source_offset_re (ρ : ℂ) : (ρ / 2 - 1 / 4).re = (ρ.re - 1 / 2) / 2 := by
  simp
  ring

/-- The source sits on the axis exactly when the zero lies on the line. -/
theorem source_on_axis_iff (ρ : ℂ) : (ρ / 2 - 1 / 4).re = 0 ↔ ρ.re = 1 / 2 := by
  rw [source_offset_re]
  constructor <;> intro h <;> linarith

/-- On the axis, the source of a zero is the native two-ended configuration at its height. -/
theorem source_is_native_of_axis {ρ : ℂ} (h : ρ.re = 1 / 2) (hc : ℝ) :
    sourceConfig (ρ / 2 - 1 / 4) (Real.exp ρ.im) hc = twoEndedConfig (Real.exp ρ.im) hc := by
  have hv : ρ / 2 - 1 / 4 = eventOffset (Real.exp ρ.im) := by
    unfold eventOffset
    rw [Real.log_exp]
    apply Complex.ext <;> simp [h]
    norm_num
  rw [hv, sourceConfig_axis]

end CriticalLinePhasor.HelixZetaSource

end

#print axioms CriticalLinePhasor.HelixZetaSource.foot_bound_gen
#print axioms CriticalLinePhasor.HelixZetaSource.sourceConfig_mass_pos
#print axioms CriticalLinePhasor.HelixZetaSource.sourceConfig_cancels_iff
#print axioms CriticalLinePhasor.HelixZetaSource.every_zero_has_source
#print axioms CriticalLinePhasor.HelixZetaSource.source_is_native_of_axis
