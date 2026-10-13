import RequestProject.HelixWindowCompletion3D

/-!
# The two-ended fiber about the origin (ledger 1260)

The helix's functional equation reflects and conjugates about ZERO: the origin, signed height `h = 0`. The Lean
bank variable `x` is the positive encoding `exp h`; the reflection reads `x ↦ 1/x` in it, and the encoding's value
at the origin is not the origin. This file states the two-ended fiber in that frame, with no `½` and no `1` in
any helix statement.

* `halfDensity P x = x^{k/2}·P.f x`: the bank with its reflection weight absorbed.
  `halfDensity_reflect`: `halfDensity P (1/x) = ε·halfDensity P.symm x`. The reflection is weight-free.
* `originΛ P v = P.Λ (k/2 + v)`: the completed fiber in the offset `v` from the origin. This is the Mellin
  transform of the half-density bank; the `k/2` only converts Mathlib's uncentered variable.
  `originEnd P c v` is the helix end at the cut `c`, in the same offset.
* `origin_reflection`: `originΛ P (-v) = ε·originΛ P.symm v`. Reflection about zero.
* `origin_reflection_conj` (conjugate dual, `ε = 1`): `originΛ P (-conj v) = conj (originΛ P v)`.
  Reflect AND conjugate about zero.
* `origin_two_ended` (conjugate dual): at every offset `v` and every cut `c`,
  `originΛ P v = originEnd P c v + ε·conj (originEnd P (1/c) (-conj v))`.
  The anti-helix end at `v` is the J-image of the helix end at the mirrored offset `-v̄`, at the same height
  `Im v`.
  - On the axis (`Re v = 0`): `-v̄ = v`, so the two ends are mirror images and the closure is a sign change.
  - Off the axis: the end at offset `+δ` against the mirrored end at `-δ`.
* The readout (`riemannZeta_eq_zero_iff_origin`): for the Gaussian bank, `originΛ` at offset `v` reads out
  `ζ` at `s = ½ + 2v`. The `½` is the chart's placement of the origin; it appears here and nowhere above. At the
  event's physical height `Z`: `v = i·log Z / 2`.
-/

open Complex Set MeasureTheory Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace CriticalLinePhasor.HelixOriginCentered

open CriticalLinePhasor CriticalLinePhasor.HelixTwoEndedClosure HurwitzZeta

/-- The bank with its half-density: the reflection weight `x^{k/2}` absorbed into the profile. -/
def halfDensity (P : WeakFEPair ℂ) (x : ℝ) : ℂ := ((x ^ (P.k / 2) : ℝ) : ℂ) * P.f x

/-- **The half-density reflection is weight-free**: under `h ↦ -h` (encoded `x ↦ 1/x`), the bank goes to `ε`
times the dual bank. -/
theorem halfDensity_reflect (P : WeakFEPair ℂ) {x : ℝ} (hx : 0 < x) :
    halfDensity P (1 / x) = P.ε * halfDensity P.symm x := by
  unfold halfDensity
  rw [P.h_feq x hx, smul_eq_mul, WeakFEPair.symm_f, WeakFEPair.symm_k]
  have h1 : ((1 / x) ^ (P.k / 2) : ℝ) = (x ^ (P.k / 2))⁻¹ := by
    rw [one_div, Real.inv_rpow hx.le]
  have h2 : (x ^ P.k : ℝ) = x ^ (P.k / 2) * x ^ (P.k / 2) := by
    rw [← Real.rpow_add hx]
    ring_nf
  have hne : (x ^ (P.k / 2) : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
  rw [h1, h2]
  push_cast
  field_simp

/-- The completed fiber in the offset `v` from the origin. -/
def originΛ (P : WeakFEPair ℂ) (v : ℂ) : ℂ := P.Λ (P.k / 2 + v)

/-- The helix end at the cut `c`, in the offset from the origin. -/
def originEnd (P : WeakFEPair ℂ) (c : ℝ) (v : ℂ) : ℂ := helixEndAt P c (P.k / 2 + v)

/-- **Reflection about zero.** -/
theorem origin_reflection (P : WeakFEPair ℂ) (v : ℂ) :
    originΛ P (-v) = P.ε • originΛ P.symm v := by
  unfold originΛ
  have h := P.functional_equation (P.k / 2 + v)
  rw [show (P.k : ℂ) - (P.k / 2 + v) = P.k / 2 + -v by ring] at h
  rw [h, WeakFEPair.symm_k]

/-- **The two-ended fiber about the origin, at every offset and every cut** (conjugate dual): the anti-helix end
at `v` is the J-image of the helix end at the mirrored offset `-v̄`. -/
theorem origin_two_ended (P : WeakFEPair ℂ) (hg : ∀ x, 0 < x → P.g x = conj (P.f x))
    (hg₀ : P.g₀ = conj P.f₀) {c : ℝ} (hc : 0 < c) {v : ℂ} (hv0 : P.k / 2 + v ≠ 0)
    (hvk : P.k / 2 + v ≠ P.k) :
    originΛ P v = originEnd P c v + P.ε * conj (originEnd P c⁻¹ (-conj v)) := by
  unfold originΛ originEnd helixEndAt
  rw [Λ_two_ended_cut P hc hv0 hvk, helixStrandAt_symm_of_conj P hg hg₀ (inv_pos.mpr hc), hg₀]
  have harg : ((c⁻¹ : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (inv_pos.mpr hc).le]
    exact Real.pi_pos.ne
  have hconj : conj ((((c⁻¹ : ℝ) : ℂ)) ^ ((P.k : ℂ) / 2 + -conj v)) = (c : ℂ) ^ (P.k / 2 + v - P.k) := by
    have h := Complex.cpow_conj ((c⁻¹ : ℝ) : ℂ) ((P.k : ℂ) / 2 + v - P.k) harg
    rw [Complex.conj_ofReal] at h
    rw [show ((P.k : ℂ) / 2 + -conj v) = conj ((P.k : ℂ) - (P.k / 2 + v)) by
      simp only [map_sub, map_add, map_div₀, Complex.conj_ofReal, map_ofNat]; ring]
    rw [Complex.cpow_conj _ _ harg, Complex.conj_ofReal, Complex.conj_conj, ofReal_inv_cpow hc]
    ring_nf
  have hpt : conj ((P.k : ℂ) - (P.k / 2 + v)) = P.k / 2 + -conj v := by
    simp only [map_sub, map_add, map_div₀, Complex.conj_ofReal, map_ofNat]
    ring
  rw [hpt, map_sub, map_mul, map_div₀, hconj]
  have hd : conj ((P.k : ℂ) / 2 + -conj v) = (P.k : ℂ) - (P.k / 2 + v) := by
    simp only [map_add, map_div₀, Complex.conj_ofReal, map_ofNat, map_neg, Complex.conj_conj]
    ring
  rw [hd]
  ring

/-- **Reflect and conjugate about zero**, for a conjugate-dual pair with `ε = 1`. -/
theorem origin_reflection_conj (P : WeakFEPair ℂ) (hg : ∀ x, 0 < x → P.g x = conj (P.f x))
    (hg₀ : P.g₀ = conj P.f₀) (hε : P.ε = 1) {v : ℂ} (hv0 : P.k / 2 + v ≠ 0) (hvk : P.k / 2 + v ≠ P.k) :
    originΛ P (-conj v) = conj (originΛ P v) := by
  have hs0 : (P.k : ℂ) / 2 + -conj v ≠ 0 := by
    intro h
    apply hvk
    have := congrArg conj h
    simp only [map_add, map_div₀, Complex.conj_ofReal, map_neg, Complex.conj_conj, map_ofNat, map_zero]
      at this
    linear_combination -this
  have hsk : (P.k : ℂ) / 2 + -conj v ≠ P.k := by
    intro h
    apply hv0
    have := congrArg conj h
    simp only [map_add, map_div₀, Complex.conj_ofReal, map_neg, Complex.conj_conj, map_ofNat] at this
    linear_combination -this
  have h1 := origin_two_ended P hg hg₀ one_pos hv0 hvk
  have h2 := origin_two_ended P hg hg₀ one_pos hs0 hsk
  rw [inv_one, hε, one_mul] at h1 h2
  simp only [map_neg, Complex.conj_conj, neg_neg] at h2
  rw [h1, h2, map_add, Complex.conj_conj]
  ring

/-! ## The Gaussian bank and the readout -/

theorem riemannPair_conj' : ∀ x, 0 < x → (hurwitzEvenFEPair 0).g x = conj ((hurwitzEvenFEPair 0).f x) :=
  fun x _ => riemannPair_conj x

/-- **The readout**: the Gaussian bank's completed fiber at offset `v` is `2·completedRiemannZeta (½ + 2v)`. The
chart places the origin at `½`. -/
theorem originΛ_readout (v : ℂ) :
    originΛ (hurwitzEvenFEPair 0) v = 2 * completedRiemannZeta (1 / 2 + 2 * v) := by
  unfold originΛ
  rw [completedRiemannZeta, completedHurwitzZetaEven]
  rw [show ((hurwitzEvenFEPair 0).k : ℂ) = 1 / 2 from by simp [hurwitzEvenFEPair]]
  rw [show (1 / 2 + 2 * v) / 2 = 1 / 2 / 2 + v by ring]
  ring

/-- **At the event's physical height `Z`, about the origin**: the readout vanishes exactly when the helix end at
offset `v = i·log Z / 2` cancels its own J-image (on the axis `-v̄ = v`). -/
theorem riemannZeta_eq_zero_iff_origin (Z : ℝ) {c : ℝ} (hc : 0 < c) :
    riemannZeta (1 / 2 + (Real.log Z : ℂ) * I) = 0 ↔
      originEnd (hurwitzEvenFEPair 0) c ((Real.log Z : ℂ) * I / 2) +
        conj (originEnd (hurwitzEvenFEPair 0) c⁻¹ ((Real.log Z : ℂ) * I / 2)) = 0 := by
  set v : ℂ := (Real.log Z : ℂ) * I / 2 with hvdef
  have hmirror : -conj v = v := by
    rw [hvdef, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  have hk : ((hurwitzEvenFEPair 0).k : ℂ) = 1 / 2 := by simp [hurwitzEvenFEPair]
  have hv0 : ((hurwitzEvenFEPair 0).k : ℂ) / 2 + v ≠ 0 := by
    rw [hk]
    intro h
    have := congrArg Complex.re h
    simp [hvdef] at this
  have hvk : ((hurwitzEvenFEPair 0).k : ℂ) / 2 + v ≠ (hurwitzEvenFEPair 0).k := by
    rw [hk]
    intro h
    have := congrArg Complex.re h
    simp [hvdef] at this
    norm_num at this
  have hs : (1 / 2 + (Real.log Z : ℂ) * I) = 1 / 2 + 2 * v := by
    rw [hvdef]
    ring
  have hs0 : (1 / 2 + 2 * v) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp [hvdef] at this
  have hΓ : Gammaℝ (1 / 2 + 2 * v) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp [hvdef])
  have h2 := origin_two_ended (hurwitzEvenFEPair 0) riemannPair_conj' riemannPair_conj₀ hc hv0 hvk
  rw [hmirror, show (hurwitzEvenFEPair 0).ε = 1 from rfl, one_mul, originΛ_readout] at h2
  rw [hs, riemannZeta_def_of_ne_zero hs0, div_eq_zero_iff, or_iff_left hΓ, ← h2]
  constructor
  · intro h; rw [h, mul_zero]
  · intro h; exact (mul_eq_zero.mp h).resolve_left two_ne_zero

end CriticalLinePhasor.HelixOriginCentered

end

#print axioms CriticalLinePhasor.HelixOriginCentered.halfDensity_reflect
#print axioms CriticalLinePhasor.HelixOriginCentered.origin_reflection
#print axioms CriticalLinePhasor.HelixOriginCentered.origin_reflection_conj
#print axioms CriticalLinePhasor.HelixOriginCentered.origin_two_ended
#print axioms CriticalLinePhasor.HelixOriginCentered.originΛ_readout
#print axioms CriticalLinePhasor.HelixOriginCentered.riemannZeta_eq_zero_iff_origin
