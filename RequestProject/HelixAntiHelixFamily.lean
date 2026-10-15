import RequestProject.EulerMaclaurinDirichlet
import RequestProject.HelixZetaSource
import Mathlib.MeasureTheory.Function.Floor

/-!
# The anti-helix family and its annihilation by every drifted cancellation (ledger 1316)

Ledger 1283 (`HelixHalfLineSource.no_source_of_dense`) excludes a drifted source once a dense family below the
origin is annihilated by its functional, and records that the family is not built there. This file builds the
family's annihilation half on the helix side `u ≥ 1` (the anti-helix side `h ≤ 0` is `x = 1/u`).

The site-`k` function is the carrier's cell position read at the scaled site:
`siteFun k u = {u/k} − {u}/k`. Its Mellin transform against the completed readout is

  `mellinSite k s = ∫_1^∞ siteFun k u · u^{−(s+1)} du = −(k^{−s} − k^{−1}) · ζ(s) / s`

(`mellinSite_eq`), from the compiled `c_eq_zeta` of `EulerMaclaurinDirichlet` and one scaling of the integral.
Hence `mellinSite_annihilated`: at every zero of ζ in the strip, every site function is annihilated, and
`site_annihilated_of_source`: every drifted cancellation (1270's source) annihilates every member.

The density half is the content of the clause and is not here (ledger 003 measured the Gram distances; the
classical form is Báez-Duarte's version of Nyman–Beurling).
-/

open GRH.EulerMaclaurinDirichlet MeasureTheory Set Complex Filter

noncomputable section

namespace CriticalLinePhasor.AntiHelixFamily

/-- A bounded measurable real factor times `t^{−(s+1)}` is integrable on `Ioi a`, `a > 0`, for `Re s > 0`. -/
theorem integrableOn_bounded_mul_cpow {s : ℂ} (hσ : 0 < s.re) {a : ℝ} (ha : 0 < a)
    (φ : ℝ → ℝ) (hφm : Measurable φ) (hφb : ∀ t, |φ t| ≤ 1) :
    IntegrableOn (fun t : ℝ => (φ t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi a) := by
  have hg : IntegrableOn (fun t : ℝ => t ^ (-(s.re + 1))) (Ioi a) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) ha
  refine hg.integrable.mono' ?_ ?_
  · have hcont : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Ioi a) :=
      Complex.continuous_ofReal.continuousOn.cpow continuousOn_const
        (fun t ht => Complex.ofReal_mem_slitPlane.mpr (lt_trans ha ht))
    exact (Complex.measurable_ofReal.comp hφm).aestronglyMeasurable.mul
      (hcont.aestronglyMeasurable measurableSet_Ioi)
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    have ht0 : 0 < t := lt_trans ha ht
    rw [norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos ht0]
    have h1 : ‖φ t‖ ≤ 1 := by rw [Real.norm_eq_abs]; exact hφb t
    calc ‖φ t‖ * t ^ (-(s + 1)).re ≤ 1 * t ^ (-(s + 1)).re :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg ht0.le _)
      _ = t ^ (-(s.re + 1)) := by simp

theorem fract_abs_le (t : ℝ) : |fract t| ≤ 1 := by
  have h := Int.fract_nonneg t
  have h' := Int.fract_lt_one t
  rw [show fract t = Int.fract t from rfl, abs_of_nonneg h]
  exact h'.le

theorem measurable_fract : Measurable fract := by
  show Measurable (Int.fract : ℝ → ℝ)
  exact _root_.measurable_fract

/-- The helix-side tail integral `I(s) = ∫_1^∞ {t} t^{−(s+1)} dt`. -/
def I (s : ℂ) : ℂ := ∫ t in Ioi (1 : ℝ), (fract t : ℂ) * (t : ℂ) ^ (-(s + 1))

/-- **The tail integral in terms of ζ** (from the compiled `c_eq_zeta`): `I(s) = 1/(s−1) − ζ(s)/s`. -/
theorem I_eq {s : ℂ} (hσ : 0 < s.re) (hs : s ≠ 1) : I s = 1 / (s - 1) - riemannZeta s / s := by
  have h := c_eq_zeta s hσ hs
  unfold c_fun at h
  have hs0 : s ≠ 0 := by
    intro h0; rw [h0] at hσ; simp at hσ
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  set J := ∫ t in Ioi (1 : ℝ), (fract t : ℂ) * (t : ℂ) ^ (-(s + 1)) with hJ
  have hsJ : s * J = s / (s - 1) - riemannZeta s := by linear_combination -h
  unfold I
  rw [← hJ]
  calc J = (s * J) / s := by field_simp
    _ = (s / (s - 1) - riemannZeta s) / s := by rw [hsJ]
    _ = 1 / (s - 1) - riemannZeta s / s := by field_simp

/-- The site-`k` function: the cell position read at the scaled site, `{u/k} − {u}/k`. -/
def siteFun (k : ℕ) (u : ℝ) : ℝ := fract (u / k) - fract u / k

/-- Its Mellin transform against the completed readout, on the helix side. -/
def mellinSite (k : ℕ) (s : ℂ) : ℂ := ∫ u in Ioi (1 : ℝ), (siteFun k u : ℂ) * (u : ℂ) ^ (-(s + 1))

/-- Scaling: `∫_1^∞ {u/k} u^{−(s+1)} du = k^{−s} ∫_{1/k}^∞ {x} x^{−(s+1)} dx`. -/
theorem integral_fract_div_scale {s : ℂ} {k : ℕ} (hk : 1 ≤ k) :
    ∫ u in Ioi (1 : ℝ), (fract (u / k) : ℂ) * (u : ℂ) ^ (-(s + 1)) =
      (k : ℂ) ^ (-s) * ∫ x in Ioi (1 / (k : ℝ)), (fract x : ℂ) * (x : ℂ) ^ (-(s + 1)) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkne : (k : ℂ) ≠ 0 := by exact_mod_cast hkpos.ne'
  have hb : (0 : ℝ) < 1 / (k : ℝ) := by positivity
  have key := integral_comp_mul_right_Ioi
    (fun x : ℝ => (fract x : ℂ) * (((k : ℝ) * x : ℝ) : ℂ) ^ (-(s + 1))) 1 hb
  simp only [one_mul] at key
  have hleft : (fun u : ℝ => (fract (u / k) : ℂ) * (u : ℂ) ^ (-(s + 1))) =
      fun u : ℝ => (fract (u * (1 / (k : ℝ))) : ℂ) * (((k : ℝ) * (u * (1 / (k : ℝ))) : ℝ) : ℂ) ^ (-(s + 1)) := by
    funext u
    have h1 : u * (1 / (k : ℝ)) = u / k := by ring
    have h2 : (k : ℝ) * (u * (1 / (k : ℝ))) = u := by field_simp
    rw [h2, h1]
  rw [hleft, key, one_div, inv_inv, Complex.real_smul, ← integral_const_mul, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  have hx0 : 0 < x := lt_trans (by positivity) hx
  simp only [Complex.ofReal_mul]
  rw [Complex.mul_cpow_ofReal_nonneg hkpos.le hx0.le]
  simp only [Complex.ofReal_natCast]
  have hpow : (k : ℂ) * (k : ℂ) ^ (-(s + 1)) = (k : ℂ) ^ (-s) := by
    symm
    rw [show (-s : ℂ) = 1 + -(s + 1) by ring, Complex.cpow_add _ _ hkne, Complex.cpow_one]
  calc (k : ℂ) * ((fract x : ℂ) * ((k : ℂ) ^ (-(s + 1)) * (x : ℂ) ^ (-(s + 1))))
      = ((k : ℂ) * (k : ℂ) ^ (-(s + 1))) * ((fract x : ℂ) * (x : ℂ) ^ (-(s + 1))) := by ring
    _ = (k : ℂ) ^ (-s) * ((fract x : ℂ) * (x : ℂ) ^ (-(s + 1))) := by rw [hpow]

/-- Splitting at `1`: `∫_{1/k}^∞ {x} x^{−(s+1)} dx = (1 − (1/k)^{1−s})/(1−s) + I(s)`. -/
theorem integral_fract_split {s : ℂ} (hσ : 0 < s.re) (hs : s ≠ 1) {k : ℕ} (hk : 1 ≤ k) :
    ∫ x in Ioi (1 / (k : ℝ)), (fract x : ℂ) * (x : ℂ) ^ (-(s + 1)) =
      (1 - ((1 / (k : ℝ) : ℝ) : ℂ) ^ (1 - s)) / (1 - s) + I s := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hb : (0 : ℝ) < 1 / (k : ℝ) := by positivity
  have hb1 : 1 / (k : ℝ) ≤ 1 := by
    rw [div_le_one hkpos]; exact_mod_cast hk
  have hint : IntegrableOn (fun t : ℝ => (fract t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Ioi (1 / (k : ℝ))) :=
    integrableOn_bounded_mul_cpow hσ hb fract measurable_fract fract_abs_le
  rw [← Ioc_union_Ioi_eq_Ioi hb1,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hb1))]
  unfold I
  congr 1
  rw [integral_Ioc_eq_integral_Ioo]
  have hcongr : ∫ x in Ioo (1 / (k : ℝ)) 1, (fract x : ℂ) * (x : ℂ) ^ (-(s + 1)) =
      ∫ x in Ioo (1 / (k : ℝ)) 1, (x : ℂ) ^ (-s) := by
    refine setIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
    have hx0 : 0 < x := lt_trans hb hx.1
    have hfr : fract x = x := by
      rw [show fract x = Int.fract x from rfl, Int.fract_eq_self]
      exact ⟨hx0.le, hx.2⟩
    rw [hfr]
    have hx0' : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
    symm
    rw [show (-s : ℂ) = 1 + -(s + 1) by ring, Complex.cpow_add _ _ hx0', Complex.cpow_one]
  rw [hcongr, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hb1,
    integral_cpow (Or.inr ⟨?_, ?_⟩)]
  · rw [Complex.ofReal_one, Complex.one_cpow]
    have : -s + 1 = 1 - s := by ring
    rw [this]
  · intro h
    apply hs
    linear_combination -h
  · rw [Set.uIcc_of_le hb1]
    intro h
    exact absurd h.1 (not_le.mpr hb)

/-- **The site function's Mellin transform**: `mellinSite k s = −(k^{−s} − k^{−1}) ζ(s)/s`. -/
theorem mellinSite_eq {s : ℂ} (hσ : 0 < s.re) (hs : s ≠ 1) {k : ℕ} (hk : 1 ≤ k) :
    mellinSite k s = -((k : ℂ) ^ (-s) - (k : ℂ)⁻¹) * riemannZeta s / s := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkne : (k : ℂ) ≠ 0 := by exact_mod_cast hkpos.ne'
  have hs0 : s ≠ 0 := by
    intro h0; rw [h0] at hσ; simp at hσ
  have hs1 : 1 - s ≠ 0 := fun h => hs (by linear_combination -h)
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs
  have hmeas : Measurable fun u : ℝ => fract (u / k) :=
    measurable_fract.comp (measurable_id.div_const _)
  have hint1 : IntegrableOn (fun u : ℝ => (fract (u / k) : ℂ) * (u : ℂ) ^ (-(s + 1))) (Ioi 1) :=
    integrableOn_bounded_mul_cpow hσ one_pos _ hmeas (fun u => fract_abs_le _)
  have hint2 : IntegrableOn (fun u : ℝ => (fract u : ℂ) * (u : ℂ) ^ (-(s + 1))) (Ioi 1) :=
    integrableOn_bounded_mul_cpow hσ one_pos fract measurable_fract fract_abs_le
  have hsplit : mellinSite k s =
      (∫ u in Ioi (1 : ℝ), (fract (u / k) : ℂ) * (u : ℂ) ^ (-(s + 1))) -
        (k : ℂ)⁻¹ * ∫ u in Ioi (1 : ℝ), (fract u : ℂ) * (u : ℂ) ^ (-(s + 1)) := by
    unfold mellinSite
    rw [← integral_const_mul, ← integral_sub hint1 (hint2.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    simp only [siteFun, Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_natCast]
    ring
  have hpow : ((1 / (k : ℝ) : ℝ) : ℂ) ^ (1 - s) = (k : ℂ) ^ (s - 1) := by
    have hk' : ((1 / (k : ℝ) : ℝ) : ℂ) = (k : ℂ)⁻¹ := by push_cast; rw [one_div]
    have harg : Complex.arg (k : ℂ) ≠ Real.pi := by
      rw [← Complex.ofReal_natCast, Complex.arg_ofReal_of_nonneg hkpos.le]
      exact Real.pi_ne_zero.symm
    rw [hk', Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
    congr 1; ring
  have hac : (k : ℂ) ^ (-s) * (k : ℂ) ^ (s - 1) = (k : ℂ)⁻¹ := by
    rw [← Complex.cpow_add _ _ hkne, show -s + (s - 1) = (-1 : ℂ) by ring, Complex.cpow_neg_one]
  rw [hsplit, integral_fract_div_scale hk, integral_fract_split hσ hs hk]
  change _ - (k : ℂ)⁻¹ * I s = _
  rw [I_eq hσ hs, hpow, ← hac]
  field_simp
  ring

/-- **Every zero of the readout in the strip annihilates every site function.** -/
theorem mellinSite_annihilated {s : ℂ} (hσ : 0 < s.re) (hs : s ≠ 1) (hζ : riemannZeta s = 0) {k : ℕ}
    (hk : 1 ≤ k) : mellinSite k s = 0 := by
  rw [mellinSite_eq hσ hs hk, hζ]; simp

/-- **Every drifted cancellation annihilates every site function**: if the source at offset `v` cancels
(1270), the site functions' Mellin transforms vanish at its readout `½ + 2v`. -/
theorem site_annihilated_of_source {v : ℂ} (hv : |v.re| < 1 / 4) (Z hc : ℝ)
    (hcancel : (HelixZetaSource.sourceConfig v Z hc).Cancels) {k : ℕ} (hk : 1 ≤ k) :
    mellinSite k (1 / 2 + 2 * v) = 0 := by
  have hζ := (HelixZetaSource.sourceConfig_cancels_iff hv Z hc).mp hcancel
  have hv1 := (abs_lt.mp hv).1
  have hre : (1 / 2 + 2 * v : ℂ).re = 1 / 2 + 2 * v.re := by simp
  have hσ : 0 < (1 / 2 + 2 * v : ℂ).re := by rw [hre]; linarith
  have hs : (1 / 2 + 2 * v : ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    rw [hre] at this
    simp at this
    linarith [(abs_lt.mp hv).2]
  exact mellinSite_annihilated hσ hs hζ hk

end CriticalLinePhasor.AntiHelixFamily

end

#print axioms CriticalLinePhasor.AntiHelixFamily.I_eq
#print axioms CriticalLinePhasor.AntiHelixFamily.mellinSite_eq
#print axioms CriticalLinePhasor.AntiHelixFamily.mellinSite_annihilated
#print axioms CriticalLinePhasor.AntiHelixFamily.site_annihilated_of_source
