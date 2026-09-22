import RequestProject.FiberZeroMidpointRoute

/-!
# The partner pair at the phasor level

The lane-balanced chart of the three-dimensional fiber at `(σ, y)` is the paired sum of the
plane parts of `phasor3D χ₂ σ y n`; the involution pairs `(σ, y)` with `(1 − σ, y)`: the SAME
rotating configuration `u_n = e^{−iy log n}`, with complementary radial weights
`n^{−σ}·n^{−(1−σ)} = n^{−1}`.  Writing `σ = ½ + δ`, the two banks are the midpoint bank
`m_n = χ₂(n) n^{−½} u_n` deformed by `q_n(δ) = n^{−δ}` and by `q_n(δ)⁻¹`.

This file opens `laneChart3D` down to the phasors and proves, unconditionally:

* **the deformation** `q` and its reciprocal: `q(δ)·q(−δ) = 1`; AM–GM `q + q⁻¹ ≥ 2` with equality
  iff `q = 1` iff `δ = 0` (site ≥ 2); the cosh/sinh (log-weight) forms;
* **the 3-D magnitudes** in the lane fiber: `mag3 = n^{−σ}`, no mass; the **partner product**
  `mag3(σ)·mag3(1−σ) = n⁻¹` re-proved in this vocabulary; partner magnitudes coincide iff `σ = ½`;
* **term-level identities**: `plane(½+δ) = q·m`, the even/odd split, and the AM–GM identity
  `plane(½+δ) + plane(½−δ) − 2·plane(½) = (q + q⁻¹ − 2)·m` with a nonnegative coefficient;
* **chart-level identities** (paired sums, `|δ| < ½`): the AM–GM identity for `laneChart3D`, and
  under partner vanishing the midpoint chart is `−½` times the asymmetry-energy sum;
* **partner vanishing ⟺ even part = odd part = 0**;
* **the finite anchor bound**: for ANY unimodular phases and ANY finite bank, joint closure under
  `q` and `q⁻¹` forces `2 ≤ Σ_{n≥2} |w_n⁺ + w_n⁻ − C(w_n⁻ − w_n⁺)|` for every real `C` — site 1 is
  undeformed (`q₀ = 1`) and must be balanced by the deformed remainder twice over; when the
  remainder's mass is short, no phase configuration closes both banks;
* **THE MECHANISM** (`laneChart3D_partner_eq`, `partner_vanishing_iff`): for the infinite
  log-linear bank the reciprocal deformation is the functional equation — the partner chart is a
  NONVANISHING explicit factor (the carrier's registration: `(2π)^{−s} Γ(s) cos(πs/2)` and the two
  lane factors) times the conjugate of the chart.  So `laneChart3D (1−σ) y = 0 ⟺ laneChart3D σ y = 0`:
  simultaneous complementary cancellation occurs at EVERY vanishing, on or off the midpoint; the
  pair carries exactly one datum.

No `axiom`, no `sorry`.
-/

open CriticalLinePhasor
open scoped BigOperators

noncomputable section

namespace CarrierReadout

theorem site_pos (n : ℕ) : (0 : ℝ) < (n : ℝ) + 1 := by positivity

theorem one_lt_site {n : ℕ} (hn : 1 ≤ n) : (1 : ℝ) < (n : ℝ) + 1 := by
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-! ### 1. The radial deformation and its reciprocal -/

/-- The radial deformation of the midpoint profile at site `n+1`: `q_n(δ) = (n+1)^{−δ}`. -/
def deformation (δ : ℝ) (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (-δ)

theorem deformation_pos (δ : ℝ) (n : ℕ) : 0 < deformation δ n :=
  Real.rpow_pos_of_pos (site_pos n) _

theorem deformation_zero (n : ℕ) : deformation 0 n = 1 := by simp [deformation]

/-- **Site 1 is undeformed**: `q_0(δ) = 1` for every `δ`.  Both partner banks share it. -/
theorem deformation_site_one (δ : ℝ) : deformation δ 0 = 1 := by simp [deformation]

/-- The partner's deformation is the reciprocal. -/
theorem deformation_neg (δ : ℝ) (n : ℕ) : deformation (-δ) n = (deformation δ n)⁻¹ := by
  unfold deformation
  rw [neg_neg, Real.rpow_neg (site_pos n).le δ, inv_inv]

/-- `q(δ)·q(−δ) = 1`: the partner product in deformation form. -/
theorem deformation_mul_neg (δ : ℝ) (n : ℕ) : deformation δ n * deformation (-δ) n = 1 := by
  rw [deformation_neg]; exact mul_inv_cancel₀ (deformation_pos δ n).ne'

/-- The asymmetry energy `q + q⁻¹ − 2 = (q − 1)²/q`. -/
theorem deformation_add_neg_sub_two (δ : ℝ) (n : ℕ) :
    deformation δ n + deformation (-δ) n - 2 = (deformation δ n - 1) ^ 2 / deformation δ n := by
  rw [deformation_neg]
  have hq := (deformation_pos δ n).ne'
  field_simp
  ring

/-- **AM–GM**: `q + q⁻¹ ≥ 2`. -/
theorem two_le_deformation_add_neg (δ : ℝ) (n : ℕ) :
    2 ≤ deformation δ n + deformation (-δ) n := by
  have h : 0 ≤ (deformation δ n - 1) ^ 2 / deformation δ n :=
    div_nonneg (sq_nonneg _) (deformation_pos δ n).le
  rw [← deformation_add_neg_sub_two] at h
  linarith

theorem asymmetry_nonneg (δ : ℝ) (n : ℕ) : 0 ≤ deformation δ n + deformation (-δ) n - 2 := by
  linarith [two_le_deformation_add_neg δ n]

/-- The AM–GM equality case: `q + q⁻¹ = 2 ↔ q = 1`. -/
theorem deformation_add_neg_eq_two_iff (δ : ℝ) (n : ℕ) :
    deformation δ n + deformation (-δ) n = 2 ↔ deformation δ n = 1 := by
  rw [← sub_eq_zero, deformation_add_neg_sub_two, div_eq_zero_iff, pow_eq_zero_iff two_ne_zero,
    sub_eq_zero]
  exact ⟨fun h => h.resolve_right (deformation_pos δ n).ne', fun h => Or.inl h⟩

/-- At a site `≥ 2` the deformation is trivial iff `δ = 0`. -/
theorem deformation_eq_one_iff {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) : deformation δ n = 1 ↔ δ = 0 := by
  constructor
  · intro h
    have h0 : ((n : ℝ) + 1) ^ (-δ) = ((n : ℝ) + 1) ^ (0 : ℝ) := by rw [Real.rpow_zero]; exact h
    have := (Real.strictMono_rpow_of_base_gt_one (one_lt_site hn)).injective h0
    linarith
  · rintro rfl; exact deformation_zero n

/-- The asymmetry energy vanishes at a site `≥ 2` iff `δ = 0`. -/
theorem asymmetry_eq_zero_iff {n : ℕ} (hn : 1 ≤ n) (δ : ℝ) :
    deformation δ n + deformation (-δ) n - 2 = 0 ↔ δ = 0 := by
  rw [sub_eq_zero, deformation_add_neg_eq_two_iff, deformation_eq_one_iff hn]

/-- Log-weight form: `q + q⁻¹ = 2 cosh(δ log(n+1))`. -/
theorem deformation_add_neg_eq_cosh (δ : ℝ) (n : ℕ) :
    deformation δ n + deformation (-δ) n = 2 * Real.cosh (δ * Real.log ((n : ℝ) + 1)) := by
  unfold deformation
  rw [Real.rpow_def_of_pos (site_pos n), Real.rpow_def_of_pos (site_pos n), Real.cosh_eq]
  have e1 : Real.log ((n : ℝ) + 1) * -δ = -(δ * Real.log ((n : ℝ) + 1)) := by ring
  have e2 : Real.log ((n : ℝ) + 1) * -(-δ) = δ * Real.log ((n : ℝ) + 1) := by ring
  rw [e1, e2]; ring

/-- Log-weight form: `q⁻¹ − q = 2 sinh(δ log(n+1))`. -/
theorem deformation_neg_sub_eq_sinh (δ : ℝ) (n : ℕ) :
    deformation (-δ) n - deformation δ n = 2 * Real.sinh (δ * Real.log ((n : ℝ) + 1)) := by
  unfold deformation
  rw [Real.rpow_def_of_pos (site_pos n), Real.rpow_def_of_pos (site_pos n), Real.sinh_eq]
  have e1 : Real.log ((n : ℝ) + 1) * -δ = -(δ * Real.log ((n : ℝ) + 1)) := by ring
  have e2 : Real.log ((n : ℝ) + 1) * -(-δ) = δ * Real.log ((n : ℝ) + 1) := by ring
  rw [e1, e2]; ring

/-! ### 2. The 3-D magnitudes of the lane fiber, and the partner product -/

theorem chi2_succ (n : ℕ) : chi2 (n + 1) = 1 ∨ chi2 (n + 1) = -1 := by
  unfold chi2
  rcases Nat.mod_two_eq_zero_or_one (n + 1) with h | h <;> simp [h]

theorem norm_plane_chi2 (σ y : ℝ) (n : ℕ) :
    ‖Phasor3D.plane (Phasor3D.phasor3D chi2 σ y (n + 1))‖ = ((n : ℝ) + 1) ^ (-σ) := by
  have h := Phasor3D.phasor3D_charged_plane_norm chi2 σ y (n + 1) (Nat.succ_pos n) (chi2_succ n)
  have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [h, hc]

/-- The lane fiber has no mass: every site is charged. -/
theorem massAxis_chi2 (σ y : ℝ) (n : ℕ) :
    Phasor3D.massAxis (Phasor3D.phasor3D chi2 σ y (n + 1)) = 0 :=
  Phasor3D.phasor3D_charged_massless chi2 σ y (n + 1) (chi2_succ n)

/-- The 3-D magnitude of the lane fiber at site `n+1` is `(n+1)^{−σ}`. -/
theorem mag3_chi2 (σ y : ℝ) (n : ℕ) :
    Phasor3D.mag3 (Phasor3D.phasor3D chi2 σ y (n + 1)) = ((n : ℝ) + 1) ^ (-σ) := by
  unfold Phasor3D.mag3
  change Real.sqrt (‖Phasor3D.plane (Phasor3D.phasor3D chi2 σ y (n + 1))‖ ^ 2
    + Phasor3D.massAxis (Phasor3D.phasor3D chi2 σ y (n + 1)) ^ 2) = _
  rw [massAxis_chi2, norm_plane_chi2, zero_pow two_ne_zero, add_zero,
    Real.sqrt_sq (Real.rpow_nonneg (site_pos n).le _)]

/-- **The partner product**, in the lane fiber: the 3-D magnitudes at abscissae `σ` and `1 − σ`
multiply to `(n+1)⁻¹`, independently of `σ` and `y`. -/
theorem partner_mag3_product (σ y : ℝ) (n : ℕ) :
    Phasor3D.mag3 (Phasor3D.phasor3D chi2 σ y (n + 1))
      * Phasor3D.mag3 (Phasor3D.phasor3D chi2 (1 - σ) y (n + 1)) = ((n : ℝ) + 1)⁻¹ := by
  rw [mag3_chi2, mag3_chi2, ← Real.rpow_add (site_pos n)]
  have : -σ + -(1 - σ) = (-1 : ℝ) := by ring
  rw [this, Real.rpow_neg_one]

/-- Partner magnitudes coincide at a site `≥ 2` iff `σ = ½`. -/
theorem partner_mag3_eq_iff (σ y : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    Phasor3D.mag3 (Phasor3D.phasor3D chi2 σ y (n + 1))
      = Phasor3D.mag3 (Phasor3D.phasor3D chi2 (1 - σ) y (n + 1)) ↔ σ = 1 / 2 := by
  rw [mag3_chi2, mag3_chi2]
  constructor
  · intro h
    have := (Real.strictMono_rpow_of_base_gt_one (one_lt_site hn)).injective h
    linarith
  · rintro rfl; norm_num

/-- Deformation form of the magnitude: at `σ = ½ + δ` it is the midpoint magnitude times `q_n(δ)`. -/
theorem mag3_half_add (δ y : ℝ) (n : ℕ) :
    Phasor3D.mag3 (Phasor3D.phasor3D chi2 (1 / 2 + δ) y (n + 1))
      = ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ)) * deformation δ n := by
  rw [mag3_chi2]; unfold deformation; rw [← Real.rpow_add (site_pos n)]; congr 1; ring

/-! ### 3. Term-level identities -/

/-- The plane part of the lane fiber: lane sign × magnitude × Mellin spin. -/
theorem plane_chi2_eq (σ y : ℝ) (n : ℕ) :
    Phasor3D.plane (Phasor3D.phasor3D chi2 σ y (n + 1))
      = chi2 (n + 1) * ((((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) * LFunctionPhasor.mellinSpin y (n + 1) := by
  rw [plane_phasor3D_eq, bank_eq_rpow_mul_spin]; ring

/-- **The deformed phasor is the deformation times the midpoint phasor**: `plane(½+δ) = q·m`. -/
theorem plane_half_add (δ y : ℝ) (n : ℕ) :
    Phasor3D.plane (Phasor3D.phasor3D chi2 (1 / 2 + δ) y (n + 1))
      = (deformation δ n : ℂ) * Phasor3D.plane (Phasor3D.phasor3D chi2 (1 / 2) y (n + 1)) := by
  rw [plane_chi2_eq, plane_chi2_eq]
  unfold deformation
  rw [show -(1 / 2 + δ) = -(1 / 2 : ℝ) + -δ by ring, Real.rpow_add (site_pos n)]
  push_cast
  ring

/-- Even part at the term level: `plane(½+δ) + plane(½−δ) = (q + q⁻¹)·m`. -/
theorem plane_partner_add (δ y : ℝ) (n : ℕ) :
    Phasor3D.plane (Phasor3D.phasor3D chi2 (1 / 2 + δ) y (n + 1))
      + Phasor3D.plane (Phasor3D.phasor3D chi2 (1 / 2 - δ) y (n + 1))
      = ((deformation δ n + deformation (-δ) n : ℝ) : ℂ)
          * Phasor3D.plane (Phasor3D.phasor3D chi2 (1 / 2) y (n + 1)) := by
  rw [show (1 / 2 - δ : ℝ) = 1 / 2 + -δ by ring, plane_half_add, plane_half_add]
  push_cast
  ring

/-- Odd part at the term level: `plane(½+δ) − plane(½−δ) = (q − q⁻¹)·m`. -/
theorem plane_partner_sub (δ y : ℝ) (n : ℕ) :
    Phasor3D.plane (Phasor3D.phasor3D chi2 (1 / 2 + δ) y (n + 1))
      - Phasor3D.plane (Phasor3D.phasor3D chi2 (1 / 2 - δ) y (n + 1))
      = ((deformation δ n - deformation (-δ) n : ℝ) : ℂ)
          * Phasor3D.plane (Phasor3D.phasor3D chi2 (1 / 2) y (n + 1)) := by
  rw [show (1 / 2 - δ : ℝ) = 1 / 2 + -δ by ring, plane_half_add, plane_half_add]
  push_cast
  ring

/-- **The AM–GM identity at the term level**: the partner sum minus twice the midpoint phasor is
the asymmetry energy `q + q⁻¹ − 2 ≥ 0` times the midpoint phasor. -/
theorem plane_partner_amgm (δ y : ℝ) (n : ℕ) :
    Phasor3D.plane (Phasor3D.phasor3D chi2 (1 / 2 + δ) y (n + 1))
      + Phasor3D.plane (Phasor3D.phasor3D chi2 (1 / 2 - δ) y (n + 1))
      - 2 * Phasor3D.plane (Phasor3D.phasor3D chi2 (1 / 2) y (n + 1))
      = ((deformation δ n + deformation (-δ) n - 2 : ℝ) : ℂ)
          * Phasor3D.plane (Phasor3D.phasor3D chi2 (1 / 2) y (n + 1)) := by
  rw [plane_partner_add]; push_cast; ring

/-! ### 4. Chart-level identities (paired sums) -/

/-- The `k`-th paired summand of `laneChart3D σ y`: sites `2k+1` and `2k+2`. -/
def laneSummand (σ y : ℝ) (k : ℕ) : ℂ :=
  Phasor3D.plane (Phasor3D.phasor3D chi2 σ y (2 * k + 1))
    + Phasor3D.plane (Phasor3D.phasor3D chi2 σ y (2 * k + 2))

theorem laneChart3D_eq_tsum (σ y : ℝ) : laneChart3D σ y = ∑' k, laneSummand σ y k := rfl

theorem laneSummand_eq_pairTerm (σ y : ℝ) (k : ℕ) :
    laneSummand σ y k = DVP.pairTerm ((σ : ℂ) + (y : ℂ) * Complex.I) k := by
  unfold laneSummand
  have h2 : 2 * k + 2 = (2 * k + 1) + 1 := by ring
  rw [h2, plane_phasor3D_eq, plane_phasor3D_eq, DVP.pairTerm_eq]
  have c1 : chi2 (2 * k + 1) = 1 := by
    simp [chi2, show (2 * k + 1) % 2 = 1 by omega]
  have c2 : chi2 (2 * k + 1 + 1) = -1 := by
    simp [chi2, show (2 * k + 1 + 1) % 2 = 0 by omega]
  rw [c1, c2, bank_apply, bank_apply]
  push_cast
  ring_nf

/-- The paired summands are summable on the channel `σ > 0`. -/
theorem laneSummand_summable {σ : ℝ} (hσ : 0 < σ) (y : ℝ) : Summable (laneSummand σ y) := by
  have h := DVP.pairTerm_summable (s := (σ : ℂ) + (y : ℂ) * Complex.I)
    (by rw [re_add_mul_I]; exact hσ)
  exact h.congr fun k => (laneSummand_eq_pairTerm σ y k).symm

theorem half_add_pos {δ : ℝ} (hδ : |δ| < 1 / 2) : 0 < 1 / 2 + δ := by
  have := (abs_lt.mp hδ).1; linarith

theorem half_sub_pos {δ : ℝ} (hδ : |δ| < 1 / 2) : 0 < 1 / 2 - δ := by
  have := (abs_lt.mp hδ).2; linarith

/-- The asymmetry-energy summand: nonnegative coefficients on the midpoint phasors. -/
def asymmetrySummand (δ y : ℝ) (k : ℕ) : ℂ :=
  ((deformation δ (2 * k) + deformation (-δ) (2 * k) - 2 : ℝ) : ℂ)
      * Phasor3D.plane (Phasor3D.phasor3D chi2 (1 / 2) y (2 * k + 1))
    + ((deformation δ (2 * k + 1) + deformation (-δ) (2 * k + 1) - 2 : ℝ) : ℂ)
      * Phasor3D.plane (Phasor3D.phasor3D chi2 (1 / 2) y (2 * k + 2))

/-- **The AM–GM identity for the chart** (`|δ| < ½`): the partner sum minus twice the midpoint
chart is the asymmetry-energy sum. -/
theorem laneChart3D_partner_amgm {δ : ℝ} (hδ : |δ| < 1 / 2) (y : ℝ) :
    laneChart3D (1 / 2 + δ) y + laneChart3D (1 / 2 - δ) y - 2 * laneChart3D (1 / 2) y
      = ∑' k, asymmetrySummand δ y k := by
  have s1 := laneSummand_summable (half_add_pos hδ) y
  have s2 := laneSummand_summable (half_sub_pos hδ) y
  have s3 := laneSummand_summable (by norm_num : (0 : ℝ) < 1 / 2) y
  rw [laneChart3D_eq_tsum, laneChart3D_eq_tsum, laneChart3D_eq_tsum, ← s1.tsum_add s2,
    ← tsum_mul_left, ← Summable.tsum_sub (s1.add s2) (s3.mul_left 2)]
  refine tsum_congr fun k => ?_
  unfold laneSummand asymmetrySummand
  have e1 := plane_partner_amgm δ y (2 * k)
  have e2 := plane_partner_amgm δ y (2 * k + 1)
  rw [show 2 * k + 2 = 2 * k + 1 + 1 by ring]
  linear_combination e1 + e2

/-- **Under partner vanishing the midpoint chart is `−½` times the asymmetry-energy sum.** -/
theorem midpoint_chart_of_partner_vanishing {δ : ℝ} (hδ : |δ| < 1 / 2) {y : ℝ}
    (h : laneChart3D (1 / 2 + δ) y = 0) (hp : laneChart3D (1 / 2 - δ) y = 0) :
    laneChart3D (1 / 2) y = -(1 / 2) * ∑' k, asymmetrySummand δ y k := by
  have := laneChart3D_partner_amgm hδ y
  rw [h, hp] at this
  linear_combination (-(1 / 2 : ℂ)) * this

/-! ### 5. Even and odd parts -/

/-- The even part of the deformation: `½(B(δ) + B(−δ))`. -/
def evenChart (δ y : ℝ) : ℂ := (laneChart3D (1 / 2 + δ) y + laneChart3D (1 / 2 - δ) y) / 2

/-- The odd part of the deformation: `½(B(δ) − B(−δ))`. -/
def oddChart (δ y : ℝ) : ℂ := (laneChart3D (1 / 2 + δ) y - laneChart3D (1 / 2 - δ) y) / 2

theorem laneChart3D_eq_even_add_odd (δ y : ℝ) :
    laneChart3D (1 / 2 + δ) y = evenChart δ y + oddChart δ y := by
  unfold evenChart oddChart; ring

theorem laneChart3D_partner_eq_even_sub_odd (δ y : ℝ) :
    laneChart3D (1 / 2 - δ) y = evenChart δ y - oddChart δ y := by
  unfold evenChart oddChart; ring

theorem evenChart_neg (δ y : ℝ) : evenChart (-δ) y = evenChart δ y := by
  unfold evenChart
  rw [show (1 / 2 + -δ : ℝ) = 1 / 2 - δ by ring, show (1 / 2 - -δ : ℝ) = 1 / 2 + δ by ring, add_comm]

theorem oddChart_neg (δ y : ℝ) : oddChart (-δ) y = -oddChart δ y := by
  unfold oddChart
  rw [show (1 / 2 + -δ : ℝ) = 1 / 2 - δ by ring, show (1 / 2 - -δ : ℝ) = 1 / 2 + δ by ring]; ring

/-- **Partner vanishing ⟺ the even part and the odd part both vanish.** -/
theorem partner_vanishing_iff_even_odd (δ y : ℝ) :
    (laneChart3D (1 / 2 + δ) y = 0 ∧ laneChart3D (1 / 2 - δ) y = 0)
      ↔ (evenChart δ y = 0 ∧ oddChart δ y = 0) := by
  constructor
  · rintro ⟨h, hp⟩
    unfold evenChart oddChart
    rw [h, hp]; simp
  · rintro ⟨he, ho⟩
    rw [laneChart3D_eq_even_add_odd, laneChart3D_partner_eq_even_sub_odd, he, ho]; simp

/-! ### 6. The finite anchor bound: joint closure of a finite bank under `q` and `q⁻¹` -/

/-- **The anchor bound.**  For any finite bank with unimodular phases `u`, weights `w⁺ w⁻` that
agree at site `0` (the undeformed anchor, `w⁺ 0 = w⁻ 0 = 1`), joint closure under both weightings
forces, for EVERY real `C`, `2 ≤ Σ_{n=1}^{N-1} |w⁺ n + w⁻ n − C (w⁻ n − w⁺ n)|`: the anchor must be
balanced twice over by the deformed remainder. -/
theorem finite_partner_closure_anchor_bound {N : ℕ} (hN : 1 ≤ N) (u : ℕ → ℂ) (hu : ∀ n, ‖u n‖ = 1)
    (wp wm : ℕ → ℝ) (h0p : wp 0 = 1) (h0m : wm 0 = 1)
    (hp : ∑ n ∈ Finset.range N, (wp n : ℂ) * u n = 0)
    (hm : ∑ n ∈ Finset.range N, (wm n : ℂ) * u n = 0) (C : ℝ) :
    2 ≤ ∑ n ∈ Finset.Ico 1 N, |wp n + wm n - C * (wm n - wp n)| := by
  have hsplit : ∀ w : ℕ → ℝ, ∑ n ∈ Finset.range N, (w n : ℂ) * u n
      = (w 0 : ℂ) * u 0 + ∑ n ∈ Finset.Ico 1 N, (w n : ℂ) * u n := by
    intro w
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) hN]
    simp
  have hp' := hp; have hm' := hm
  rw [hsplit, h0p] at hp'
  rw [hsplit, h0m] at hm'
  -- 2 u 0 = -(Σ (wp + wm) u) = -(Σ (wp + wm - C (wm - wp)) u)  since Σ (wm - wp) u = 0
  have key : (2 : ℂ) * u 0
      = -∑ n ∈ Finset.Ico 1 N, ((wp n + wm n - C * (wm n - wp n) : ℝ) : ℂ) * u n := by
    have hdiff : ∑ n ∈ Finset.Ico 1 N, ((wm n - wp n : ℝ) : ℂ) * u n = 0 := by
      have h2 : ∑ n ∈ Finset.Ico 1 N, ((wm n - wp n : ℝ) : ℂ) * u n
          = ∑ n ∈ Finset.Ico 1 N, (wm n : ℂ) * u n - ∑ n ∈ Finset.Ico 1 N, (wp n : ℂ) * u n := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun n _ => ?_; push_cast; ring
      rw [h2]
      simp only [Complex.ofReal_one, one_mul] at hp' hm'
      linear_combination hm' - hp'
    have hsum : ∑ n ∈ Finset.Ico 1 N, ((wp n + wm n - C * (wm n - wp n) : ℝ) : ℂ) * u n
        = ∑ n ∈ Finset.Ico 1 N, ((wp n : ℂ) * u n + (wm n : ℂ) * u n)
          - (C : ℂ) * ∑ n ∈ Finset.Ico 1 N, ((wm n - wp n : ℝ) : ℂ) * u n := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_; push_cast; ring
    rw [hsum, hdiff, mul_zero, sub_zero, Finset.sum_add_distrib]
    simp only [Complex.ofReal_one, one_mul] at hp' hm'
    linear_combination hp' + hm'
  have hnorm : ‖(2 : ℂ) * u 0‖ = 2 := by rw [norm_mul, hu 0, mul_one]; norm_num
  rw [← hnorm, key, norm_neg]
  calc ‖∑ n ∈ Finset.Ico 1 N, ((wp n + wm n - C * (wm n - wp n) : ℝ) : ℂ) * u n‖
      ≤ ∑ n ∈ Finset.Ico 1 N, ‖((wp n + wm n - C * (wm n - wp n) : ℝ) : ℂ) * u n‖ :=
        norm_sum_le _ _
    _ = ∑ n ∈ Finset.Ico 1 N, |wp n + wm n - C * (wm n - wp n)| := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [norm_mul, hu n, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- **No joint closure when the deformed remainder is short**: if for some `C` the remainder's
mass `Σ_{n≥1} |w⁺ + w⁻ − C(w⁻ − w⁺)|` is below `2`, no unimodular phase configuration closes both
banks. -/
theorem no_finite_partner_closure_of_short_remainder {N : ℕ} (hN : 1 ≤ N) (u : ℕ → ℂ)
    (hu : ∀ n, ‖u n‖ = 1) (wp wm : ℕ → ℝ) (h0p : wp 0 = 1) (h0m : wm 0 = 1) (C : ℝ)
    (hshort : ∑ n ∈ Finset.Ico 1 N, |wp n + wm n - C * (wm n - wp n)| < 2) :
    ¬ (∑ n ∈ Finset.range N, (wp n : ℂ) * u n = 0 ∧ ∑ n ∈ Finset.range N, (wm n : ℂ) * u n = 0) := by
  rintro ⟨hp, hm⟩
  exact absurd (finite_partner_closure_anchor_bound hN u hu wp wm h0p h0m hp hm C) (not_le.mpr hshort)

/-! ### 7. THE MECHANISM: the reciprocal deformation of the infinite bank is the functional equation -/

theorem mellinSpin_neg (y : ℝ) (n : ℕ) :
    LFunctionPhasor.mellinSpin (-y) n = (starRingEnd ℂ) (LFunctionPhasor.mellinSpin y n) := by
  unfold LFunctionPhasor.mellinSpin
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The chart at height `−y` is the conjugate of the chart at height `y`. -/
theorem laneChart3D_neg (σ y : ℝ) : laneChart3D σ (-y) = (starRingEnd ℂ) (laneChart3D σ y) := by
  rw [laneChart3D_eq_tsum, laneChart3D_eq_tsum]
  have hterm : ∀ k, laneSummand σ (-y) k = (starRingEnd ℂ) (laneSummand σ y k) := by
    intro k
    unfold laneSummand
    rw [show 2 * k + 2 = 2 * k + 1 + 1 by ring, plane_chi2_eq, plane_chi2_eq, plane_chi2_eq,
      plane_chi2_eq, mellinSpin_neg, mellinSpin_neg, map_add, map_mul, map_mul, map_mul, map_mul,
      Complex.conj_ofReal, Complex.conj_ofReal]
    have hc : ∀ m, (starRingEnd ℂ) (chi2 m) = chi2 m := by
      intro m; unfold chi2; split_ifs <;> simp
    rw [hc, hc]
  simp_rw [hterm]
  exact (Complex.conjCLE.map_tsum (f := laneSummand σ y)).symm

/-- The registration factor of the functional equation, read on the lane chart:
`Ψ(s) = (1 − 2^{s}) · 2 (2π)^{−s} Γ(s) cos(πs/2) / (1 − 2^{1−s})`. -/
def partnerFactor (s : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ s) * (2 * (2 * (Real.pi : ℂ)) ^ (-s) * Complex.Gamma s
    * Complex.cos (Real.pi * s / 2)) / (1 - (2 : ℂ) ^ ((1 : ℂ) - s))

theorem two_cpow_ne_one_of_re_pos {s : ℂ} (hs : 0 < s.re) : (1 : ℂ) - (2 : ℂ) ^ s ≠ 0 := by
  intro h
  have h2 : (2 : ℂ) ^ s = 1 := by linear_combination -h
  have hn : ‖(2 : ℂ) ^ s‖ = 1 := by rw [h2, norm_one]
  have hcast : (2 : ℂ) = ((2 : ℕ) : ℂ) := by norm_num
  rw [hcast, Complex.norm_natCast_cpow_of_pos (by norm_num)] at hn
  have : (2 : ℝ) ^ s.re = 1 := by simpa using hn
  have hlt : (1 : ℝ) < (2 : ℝ) ^ s.re := Real.one_lt_rpow (by norm_num) hs
  linarith

theorem cos_half_pi_mul_ne_zero {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    Complex.cos (Real.pi * s / 2) ≠ 0 := by
  intro h
  rw [Complex.cos_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : (Real.pi : ℂ) * s = (Real.pi : ℂ) * (2 * (k : ℂ) + 1) := by
    linear_combination 2 * hk
  have hsk : s = 2 * (k : ℂ) + 1 := mul_left_cancel₀ hπ h1
  have hre := congrArg Complex.re hsk
  simp only [Complex.add_re, Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat,
    Complex.intCast_re, Complex.intCast_im, Complex.one_re, mul_zero, sub_zero] at hre
  have hk0 : (-1 : ℤ) < k := by
    have : (-1 : ℝ) < k := by linarith
    exact_mod_cast this
  have hk1 : k < 0 := by
    have : (k : ℝ) < 0 := by linarith
    exact_mod_cast this
  omega

/-- **The registration factor does not vanish in the strip.** -/
theorem partnerFactor_ne_zero {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) : partnerFactor s ≠ 0 := by
  unfold partnerFactor
  have hΓ : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs0
  have h2π : (2 * (Real.pi : ℂ)) ^ (-s) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    rintro ⟨h, -⟩
    have : (2 * Real.pi : ℝ) = 0 := by exact_mod_cast h
    linarith [Real.pi_pos]
  exact div_ne_zero
    (mul_ne_zero (two_cpow_ne_one_of_re_pos hs0)
      (mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero h2π) hΓ) (cos_half_pi_mul_ne_zero hs0 hs1)))
    (lane_factor_ne_zero hs1)

/-- The chart is the lane factor times `ζ` (Theorem 17 at carrier scale `1`). -/
theorem laneChart3D_eq_lane_mul_zeta {σ y : ℝ} (hσ : 0 < σ)
    (h1 : ((σ : ℂ) + (y : ℂ) * Complex.I) ≠ 1) :
    laneChart3D σ y
      = (1 - (2 : ℂ) ^ ((1 : ℂ) - ((σ : ℂ) + (y : ℂ) * Complex.I)))
          * riemannZeta ((σ : ℂ) + (y : ℂ) * Complex.I) := by
  have h := fiber3D_eq_function 1 one_pos σ y hσ h1
  unfold CarrierParity.carrierFiber at h
  simp only [Complex.ofReal_one, Complex.one_cpow, one_mul] at h
  exact h

/-- **THE MECHANISM — the reciprocal deformation is the functional equation.**  In the strip, the
partner chart at the same height is the registration factor times the conjugate of the chart. -/
theorem laneChart3D_partner_eq {σ y : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    laneChart3D (1 - σ) y
      = (starRingEnd ℂ) (partnerFactor ((σ : ℂ) + (y : ℂ) * Complex.I) * laneChart3D σ y) := by
  have hs0 : 0 < ((σ : ℂ) + (y : ℂ) * Complex.I).re := by rw [re_add_mul_I]; exact hσ0
  have hs1 : ((σ : ℂ) + (y : ℂ) * Complex.I).re < 1 := by rw [re_add_mul_I]; exact hσ1
  have hsne1 : ((σ : ℂ) + (y : ℂ) * Complex.I) ≠ 1 := by
    intro h; rw [h] at hs1; simp at hs1
  have hden := lane_factor_ne_zero hs1
  -- the chart at (1−σ, −y) is η(1 − s)
  have e : (((1 - σ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * Complex.I) = 1 - ((σ : ℂ) + (y : ℂ) * Complex.I) := by
    push_cast; ring
  have hpart : laneChart3D (1 - σ) (-y)
      = (1 - (2 : ℂ) ^ ((1 : ℂ) - (1 - ((σ : ℂ) + (y : ℂ) * Complex.I))))
          * riemannZeta (1 - ((σ : ℂ) + (y : ℂ) * Complex.I)) := by
    have h := laneChart3D_eq_lane_mul_zeta (σ := 1 - σ) (y := -y) (by linarith) (by
      rw [e]; intro h
      have h' := congrArg Complex.re h
      simp only [Complex.sub_re, Complex.one_re] at h'
      linarith)
    rw [e] at h; exact h
  have hfe := riemannZeta_one_sub (s := (σ : ℂ) + (y : ℂ) * Complex.I) (by
    intro n h
    have h' := congrArg Complex.re h
    simp only [Complex.neg_re, Complex.natCast_re] at h'
    linarith [Nat.cast_nonneg (α := ℝ) n]) hsne1
  have hζ : riemannZeta ((σ : ℂ) + (y : ℂ) * Complex.I)
      = laneChart3D σ y / (1 - (2 : ℂ) ^ ((1 : ℂ) - ((σ : ℂ) + (y : ℂ) * Complex.I))) := by
    rw [laneChart3D_eq_lane_mul_zeta hσ0 hsne1, mul_div_cancel_left₀ _ hden]
  have hconj : laneChart3D (1 - σ) y = (starRingEnd ℂ) (laneChart3D (1 - σ) (-y)) := by
    have := laneChart3D_neg (1 - σ) (-y)
    rw [neg_neg] at this
    exact this
  rw [hconj, hpart, show (1 : ℂ) - (1 - ((σ : ℂ) + (y : ℂ) * Complex.I)) = (σ : ℂ) + (y : ℂ) * Complex.I
    by ring, hfe, hζ]
  unfold partnerFactor
  congr 1
  field_simp

/-- **Simultaneous complementary cancellation is automatic.**  In the strip the partner chart
vanishes iff the chart vanishes: the pair `(σ, y), (1 − σ, y)` carries exactly one datum. -/
theorem partner_vanishing_iff {σ y : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    laneChart3D (1 - σ) y = 0 ↔ laneChart3D σ y = 0 := by
  rw [laneChart3D_partner_eq hσ0 hσ1, map_eq_zero, mul_eq_zero]
  have hne := partnerFactor_ne_zero (s := (σ : ℂ) + (y : ℂ) * Complex.I)
    (by rw [re_add_mul_I]; exact hσ0) (by rw [re_add_mul_I]; exact hσ1)
  exact ⟨fun h => h.resolve_left hne, fun h => Or.inr h⟩

/-- In deformation variables: a vanishing at `½ + δ` is a vanishing at `½ − δ`, same height. -/
theorem partner_of_vanishing {δ y : ℝ} (hδ : |δ| < 1 / 2)
    (h : laneChart3D (1 / 2 + δ) y = 0) : laneChart3D (1 / 2 - δ) y = 0 := by
  have := (partner_vanishing_iff (σ := 1 / 2 + δ) (half_add_pos hδ)
    (by linarith [(abs_lt.mp hδ).2])).mpr h
  rwa [show (1 - (1 / 2 + δ) : ℝ) = 1 / 2 - δ by ring] at this

/-- The partner map `B ↦ conj(Ψ B)` squares to `‖Ψ‖²`: it is an anti-linear involution exactly
where `‖Ψ‖ = 1`; off that locus it is a similarity with ratio `‖Ψ‖ ≠ 1`. -/
theorem partner_map_sq (Ψ B : ℂ) :
    (starRingEnd ℂ) (Ψ * (starRingEnd ℂ) (Ψ * B)) = ((‖Ψ‖ ^ 2 : ℝ) : ℂ) * B := by
  rw [map_mul, Complex.conj_conj, ← mul_assoc, mul_comm ((starRingEnd ℂ) Ψ) Ψ, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]

/-- **The even part or the odd part alone can vanish at a non-vanishing point only where the
registration factor is unimodular**: `evenChart δ y = 0 ∨ oddChart δ y = 0`, with the chart
nonzero, forces `‖Ψ(½ + δ + iy)‖ = 1`. -/
theorem norm_partnerFactor_eq_one_of_even_or_odd_zero {δ y : ℝ} (hδ : |δ| < 1 / 2)
    (hB : laneChart3D (1 / 2 + δ) y ≠ 0) (h : evenChart δ y = 0 ∨ oddChart δ y = 0) :
    ‖partnerFactor (((1 / 2 + δ : ℝ) : ℂ) + (y : ℂ) * Complex.I)‖ = 1 := by
  have hp := laneChart3D_partner_eq (σ := 1 / 2 + δ) (y := y) (half_add_pos hδ)
    (by linarith [(abs_lt.mp hδ).2])
  rw [show (1 - (1 / 2 + δ) : ℝ) = 1 / 2 - δ by ring] at hp
  set Ψ := partnerFactor (((1 / 2 + δ : ℝ) : ℂ) + (y : ℂ) * Complex.I)
  set B := laneChart3D (1 / 2 + δ) y
  have hnorm : ‖laneChart3D (1 / 2 - δ) y‖ = ‖Ψ‖ * ‖B‖ := by
    rw [hp, Complex.norm_conj, norm_mul]
  have key : ‖laneChart3D (1 / 2 - δ) y‖ = ‖B‖ := by
    rcases h with he | ho
    · unfold evenChart at he
      have : laneChart3D (1 / 2 - δ) y = -B := by
        have := div_eq_zero_iff.mp he
        rcases this with h0 | h0
        · linear_combination h0
        · norm_num at h0
      rw [this, norm_neg]
    · unfold oddChart at ho
      have : laneChart3D (1 / 2 - δ) y = B := by
        have := div_eq_zero_iff.mp ho
        rcases this with h0 | h0
        · linear_combination -h0
        · norm_num at h0
      rw [this]
  have hBpos : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have : ‖Ψ‖ * ‖B‖ = 1 * ‖B‖ := by rw [← hnorm, key, one_mul]
  exact mul_right_cancel₀ hBpos.ne' this

end CarrierReadout
