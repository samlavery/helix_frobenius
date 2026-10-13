import RequestProject.FocalPartnerTest

/-!
# What survives from the magnitudes at a focal cancellation (ledger 1229)

Sam's question (2026-10-11), native only: when focal cancellation occurs, what survives from the magnitudes? `Q`
keeps the surviving mass `M = Σ |c_k|` (`cancellingMass_eq`: the sum of the magnitudes of the cancelling
phasors). Does vanishing itself, through the actual `FocalEvent` construction, force a unique surviving mass?

* `two_mul_norm_le_mass`: what vanishing DOES force on the magnitudes is the polygon closure inequality
  `2‖c_k‖ ≤ M` for every phasor. An inequality, not a value.
* `scaleEvent`, `eigenMass_scaleEvent`: the construction allows any positive amplitude law. Scaling it by `r > 0`
  keeps the routing, the ordinate, the height and the cancellation, and multiplies the surviving mass by `r`.
* `focal_mass_not_forced`: even with the routing, the ordinate (hence height and every carrier phase) and the
  first amplitude ALL fixed, if the head carries three sites past the first, with nonzero weight and pairwise
  distinct carrier phases, then the surviving masses of cancelling events fill an open interval around `M`.
  The direction moves three amplitudes by the cross-product coefficients of their phases (`triangle_combination`),
  which keeps the cancellation; the mass moves at rate `A` = twice the signed area of the triangle of the three
  phases (`triangle_area_ne_zero`: nonzero for three distinct points on the unit circle).

So the surviving mass is carried over from the input's magnitude profile (magnitude conservation), and vanishing
does not select it.
-/

open Complex Finset

noncomputable section

namespace CriticalLinePhasor.FocalMass

open CriticalLinePhasor CriticalLinePhasor.FocalFeet CriticalLinePhasor.FocalQuotient
open CriticalLinePhasor.FocalEventProjection CriticalLinePhasor.CancellationEigenstatePair
open CriticalLinePhasor.ThreeDFocal CriticalLinePhasor.CarrierHeadFiniteFiber
open CriticalLinePhasor.GrownFiberEvolution CriticalLinePhasor.HarmonicCell

/-! ## 1. What vanishing forces on the magnitudes -/

/-- **Polygon closure**: in a cancelling configuration no phasor exceeds half the surviving mass. -/
theorem two_mul_norm_le_mass {c : PhasorConfig} (hc : c.Cancels) (k : Fin c.size) :
    2 * ‖c.phasor k‖ ≤ c.mass := by
  unfold PhasorConfig.Cancels PhasorConfig.resultant at hc
  unfold PhasorConfig.mass
  have hsplit := Finset.add_sum_erase Finset.univ c.phasor (Finset.mem_univ k)
  have hsplitN := Finset.add_sum_erase Finset.univ (fun j => ‖c.phasor j‖) (Finset.mem_univ k)
  beta_reduce at hsplitN
  rw [← hsplit] at hc
  have hk : c.phasor k = -∑ j ∈ Finset.univ.erase k, c.phasor j := eq_neg_of_add_eq_zero_left hc
  have hle : ‖c.phasor k‖ ≤ ∑ j ∈ Finset.univ.erase k, ‖c.phasor j‖ := by
    rw [hk, norm_neg]
    exact norm_sum_le _ _
  rw [← hsplitN]
  linarith

/-! ## 2. Scale -/

/-- The same event with its amplitude law scaled by `r > 0`. -/
def scaleEvent (e : FocalEvent) {r : ℝ} (hr : 0 < r) : FocalEvent where
  w := e.w
  w_one := e.w_one
  a := fun k => r * e.a k
  a_pos := fun k => mul_pos hr (e.a_pos k)
  y := e.y
  head_gt := e.head_gt
  cancel := by
    have h : headSum e.w (fun k => r * e.a k) e.y = (r : ℂ) * headSum e.w e.a e.y := by
      unfold headSum
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring
    rw [h, e.cancel, mul_zero]

theorem scaleEvent_height (e : FocalEvent) {r : ℝ} (hr : 0 < r) :
    (scaleEvent e hr).height = e.height :=
  rfl

/-- **Scaling the amplitude law scales the surviving mass.** -/
theorem eigenMass_scaleEvent (e : FocalEvent) {r : ℝ} (hr : 0 < r) :
    eigenMass (scaleEvent e hr) = r * eigenMass e := by
  show headUnsigned e.w (fun k => r * e.a k) e.y = r * headUnsigned e.w e.a e.y
  unfold headUnsigned
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ## 3. Three phases: the cross-product direction and the triangle area -/

/-- **The cross-product coefficients of three planar vectors combine them to zero.** -/
theorem triangle_combination (u₁ u₂ u₃ : ℂ) :
    (((starRingEnd ℂ) u₂ * u₃).im : ℂ) * u₁ + (((starRingEnd ℂ) u₃ * u₁).im : ℂ) * u₂ +
      (((starRingEnd ℂ) u₁ * u₂).im : ℂ) * u₃ = 0 := by
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- **Three distinct points of the unit circle span a triangle of nonzero area.** -/
theorem triangle_area_ne_zero {u₁ u₂ u₃ : ℂ} (h₁ : ‖u₁‖ = 1) (h₂ : ‖u₂‖ = 1) (h₃ : ‖u₃‖ = 1)
    (h12 : u₁ ≠ u₂) (h23 : u₂ ≠ u₃) (h31 : u₃ ≠ u₁) :
    ((starRingEnd ℂ) u₂ * u₃).im + ((starRingEnd ℂ) u₃ * u₁).im +
      ((starRingEnd ℂ) u₁ * u₂).im ≠ 0 := by
  have hu₁ : u₁ ≠ 0 := fun h => by rw [h, norm_zero] at h₁; exact zero_ne_one h₁
  have hu₂ : u₂ ≠ 0 := fun h => by rw [h, norm_zero] at h₂; exact zero_ne_one h₂
  have hu₃ : u₃ ≠ 0 := fun h => by rw [h, norm_zero] at h₃; exact zero_ne_one h₃
  have hc₁ : (starRingEnd ℂ) u₁ = u₁⁻¹ := (Complex.inv_eq_conj h₁).symm
  have hc₂ : (starRingEnd ℂ) u₂ = u₂⁻¹ := (Complex.inv_eq_conj h₂).symm
  have hc₃ : (starRingEnd ℂ) u₃ = u₃⁻¹ := (Complex.inv_eq_conj h₃).symm
  have key : (u₁ - u₂) * (u₂ - u₃) * (u₃ - u₁) =
      -(2 * I) * ((((starRingEnd ℂ) u₂ * u₃).im + ((starRingEnd ℂ) u₃ * u₁).im +
        ((starRingEnd ℂ) u₁ * u₂).im : ℝ) : ℂ) * (u₁ * u₂ * u₃) := by
    push_cast
    simp only [Complex.im_eq_sub_conj, map_mul, map_inv₀, Complex.conj_conj, hc₁, hc₂, hc₃,
      inv_inv]
    field_simp
    ring
  intro hS
  rw [hS, Complex.ofReal_zero, mul_zero, zero_mul] at key
  rcases mul_eq_zero.mp key with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact h12 (sub_eq_zero.mp h)
    · exact h23 (sub_eq_zero.mp h)
  · exact h31 (sub_eq_zero.mp h)

/-! ## 4. Linearity of the two channels in the amplitude law -/

/-- The unit amplitude at one site. -/
def single (k₀ k : ℕ) : ℝ := if k = k₀ then 1 else 0

theorem headSum_add (w : ℕ → ℂ) (a b : ℕ → ℝ) (y : ℝ) :
    headSum w (fun k => a k + b k) y = headSum w a y + headSum w b y := by
  unfold headSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

theorem headSum_mul (w : ℕ → ℂ) (r : ℝ) (a : ℕ → ℝ) (y : ℝ) :
    headSum w (fun k => r * a k) y = (r : ℂ) * headSum w a y := by
  unfold headSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

theorem headSum_single (w : ℕ → ℂ) (y : ℝ) {k₀ : ℕ} (hk : k₀ ∈ Finset.range ⌈physicalHead y⌉₊) :
    headSum w (single k₀) y =
      ((headWindow (physicalHead y) k₀ : ℝ) : ℂ) *
        (w (k₀ + 1) * LFunctionPhasor.mellinSpin y (k₀ + 1)) := by
  unfold headSum
  rw [Finset.sum_eq_single k₀ (fun k _ hne => by simp [single, hne]) (fun h => absurd hk h)]
  simp [single]

theorem headUnsigned_add (w : ℕ → ℂ) (a b : ℕ → ℝ) (y : ℝ) :
    headUnsigned w (fun k => a k + b k) y = headUnsigned w a y + headUnsigned w b y := by
  unfold headUnsigned
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem headUnsigned_mul (w : ℕ → ℂ) (r : ℝ) (a : ℕ → ℝ) (y : ℝ) :
    headUnsigned w (fun k => r * a k) y = r * headUnsigned w a y := by
  unfold headUnsigned
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem headUnsigned_single (w : ℕ → ℂ) (y : ℝ) {k₀ : ℕ}
    (hk : k₀ ∈ Finset.range ⌈physicalHead y⌉₊) :
    headUnsigned w (single k₀) y = headWindow (physicalHead y) k₀ * ‖w (k₀ + 1)‖ := by
  unfold headUnsigned
  rw [Finset.sum_eq_single k₀ (fun k _ hne => by simp [single, hne]) (fun h => absurd hk h)]
  simp [single]

/-- The unit carrier phase of the cancelling phasor at site `k + 1`. -/
def sitePhase (w : ℕ → ℂ) (y : ℝ) (k : ℕ) : ℂ :=
  w (k + 1) / ((‖w (k + 1)‖ : ℝ) : ℂ) * LFunctionPhasor.mellinSpin y (k + 1)

theorem sitePhase_norm {w : ℕ → ℂ} {k : ℕ} (hw : w (k + 1) ≠ 0) (y : ℝ) :
    ‖sitePhase w y k‖ = 1 := by
  unfold sitePhase
  rw [norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr hw), LFunctionPhasor.mellinSpin_norm, one_mul]

/-- The site term, rescaled by `c` with `c·v = x`, is `x` times the site's unit phase. -/
theorem site_term (w : ℕ → ℂ) (y : ℝ) (k : ℕ)
    (hv : 0 < headWindow (physicalHead y) k * ‖w (k + 1)‖) {c x : ℝ}
    (hcx : c * (headWindow (physicalHead y) k * ‖w (k + 1)‖) = x) :
    (c : ℂ) * (((headWindow (physicalHead y) k : ℝ) : ℂ) *
        (w (k + 1) * LFunctionPhasor.mellinSpin y (k + 1))) =
      (x : ℂ) * sitePhase w y k := by
  have hwin : headWindow (physicalHead y) k ≠ 0 := by
    intro h; rw [h, zero_mul] at hv; exact lt_irrefl 0 hv
  have hnw : ‖w (k + 1)‖ ≠ 0 := by
    intro h; rw [h, mul_zero] at hv; exact lt_irrefl 0 hv
  have hnwC : ((‖w (k + 1)‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnw
  rw [← hcx]
  unfold sitePhase
  push_cast
  field_simp

/-! ## 5. Vanishing does not force a unique surviving mass -/

/-- **The surviving mass is not forced by vanishing.** With routing, ordinate, height and first amplitude fixed,
cancelling events realize every mass in an open interval around `M`. -/
theorem focal_mass_not_forced (e : FocalEvent) {k₁ k₂ k₃ : ℕ}
    (hk₁ : k₁ ∈ Finset.range ⌈physicalHead e.y⌉₊) (hk₂ : k₂ ∈ Finset.range ⌈physicalHead e.y⌉₊)
    (hk₃ : k₃ ∈ Finset.range ⌈physicalHead e.y⌉₊) (h1₁ : 1 ≤ k₁) (h1₂ : 1 ≤ k₂) (h1₃ : 1 ≤ k₃)
    (hv₁ : 0 < headWindow (physicalHead e.y) k₁ * ‖e.w (k₁ + 1)‖)
    (hv₂ : 0 < headWindow (physicalHead e.y) k₂ * ‖e.w (k₂ + 1)‖)
    (hv₃ : 0 < headWindow (physicalHead e.y) k₃ * ‖e.w (k₃ + 1)‖)
    (h12 : sitePhase e.w e.y k₁ ≠ sitePhase e.w e.y k₂)
    (h23 : sitePhase e.w e.y k₂ ≠ sitePhase e.w e.y k₃)
    (h31 : sitePhase e.w e.y k₃ ≠ sitePhase e.w e.y k₁) :
    ∃ A : ℝ, A ≠ 0 ∧ ∃ ε > 0, ∀ t : ℝ, |t| < ε →
      ∃ e' : FocalEvent, e'.w = e.w ∧ e'.y = e.y ∧ e'.height = e.height ∧ e'.a 0 = e.a 0 ∧
        eigenMass e' = eigenMass e + t * A := by
  have hw₁ : e.w (k₁ + 1) ≠ 0 := fun h => by
    rw [h, norm_zero, mul_zero] at hv₁; exact lt_irrefl 0 hv₁
  have hw₂ : e.w (k₂ + 1) ≠ 0 := fun h => by
    rw [h, norm_zero, mul_zero] at hv₂; exact lt_irrefl 0 hv₂
  have hw₃ : e.w (k₃ + 1) ≠ 0 := fun h => by
    rw [h, norm_zero, mul_zero] at hv₃; exact lt_irrefl 0 hv₃
  obtain ⟨x₁, hx₁⟩ : ∃ x : ℝ,
      x = ((starRingEnd ℂ) (sitePhase e.w e.y k₂) * sitePhase e.w e.y k₃).im := ⟨_, rfl⟩
  obtain ⟨x₂, hx₂⟩ : ∃ x : ℝ,
      x = ((starRingEnd ℂ) (sitePhase e.w e.y k₃) * sitePhase e.w e.y k₁).im := ⟨_, rfl⟩
  obtain ⟨x₃, hx₃⟩ : ∃ x : ℝ,
      x = ((starRingEnd ℂ) (sitePhase e.w e.y k₁) * sitePhase e.w e.y k₂).im := ⟨_, rfl⟩
  have hA : x₁ + x₂ + x₃ ≠ 0 := by
    rw [hx₁, hx₂, hx₃]
    exact triangle_area_ne_zero (sitePhase_norm hw₁ _) (sitePhase_norm hw₂ _)
      (sitePhase_norm hw₃ _) h12 h23 h31
  have tri : (x₁ : ℂ) * sitePhase e.w e.y k₁ + (x₂ : ℂ) * sitePhase e.w e.y k₂ +
      (x₃ : ℂ) * sitePhase e.w e.y k₃ = 0 := by
    rw [hx₁, hx₂, hx₃]
    exact triangle_combination _ _ _
  obtain ⟨c₁, hc₁⟩ : ∃ c : ℝ, c * (headWindow (physicalHead e.y) k₁ * ‖e.w (k₁ + 1)‖) = x₁ :=
    ⟨x₁ / _, div_mul_cancel₀ _ hv₁.ne'⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c : ℝ, c * (headWindow (physicalHead e.y) k₂ * ‖e.w (k₂ + 1)‖) = x₂ :=
    ⟨x₂ / _, div_mul_cancel₀ _ hv₂.ne'⟩
  obtain ⟨c₃, hc₃⟩ : ∃ c : ℝ, c * (headWindow (physicalHead e.y) k₃ * ‖e.w (k₃ + 1)‖) = x₃ :=
    ⟨x₃ / _, div_mul_cancel₀ _ hv₃.ne'⟩
  refine ⟨x₁ + x₂ + x₃, hA, ?_⟩
  have hm : 0 < min (e.a k₁) (min (e.a k₂) (e.a k₃)) :=
    lt_min (e.a_pos _) (lt_min (e.a_pos _) (e.a_pos _))
  have hC : 0 < 1 + |c₁| + |c₂| + |c₃| := by positivity
  refine ⟨min (e.a k₁) (min (e.a k₂) (e.a k₃)) / (1 + |c₁| + |c₂| + |c₃|), div_pos hm hC,
    fun t ht => ?_⟩
  have htC : |t| * (1 + |c₁| + |c₂| + |c₃|) < min (e.a k₁) (min (e.a k₂) (e.a k₃)) := by
    rwa [lt_div_iff₀ hC] at ht
  have hsing : ∀ k₀ k, |single k₀ k| ≤ 1 := fun k₀ k => by
    unfold single
    split_ifs <;> simp
  have hterm : ∀ (c : ℝ) (k₀ k : ℕ), |t * c * single k₀ k| ≤ |t| * |c| := fun c k₀ k => by
    rw [abs_mul, abs_mul]
    exact mul_le_of_le_one_right (by positivity) (hsing _ _)
  have hpos : ∀ k, 0 < e.a k + t * c₁ * single k₁ k + t * c₂ * single k₂ k +
      t * c₃ * single k₃ k := by
    intro k
    by_cases hk : k = k₁ ∨ k = k₂ ∨ k = k₃
    · have ham : min (e.a k₁) (min (e.a k₂) (e.a k₃)) ≤ e.a k := by
        rcases hk with rfl | rfl | rfl
        · exact min_le_left _ _
        · exact (min_le_right _ _).trans (min_le_left _ _)
        · exact (min_le_right _ _).trans (min_le_right _ _)
      have hb : |t * c₁ * single k₁ k + t * c₂ * single k₂ k + t * c₃ * single k₃ k| ≤
          |t| * |c₁| + |t| * |c₂| + |t| * |c₃| := by
        calc |t * c₁ * single k₁ k + t * c₂ * single k₂ k + t * c₃ * single k₃ k|
            ≤ |t * c₁ * single k₁ k + t * c₂ * single k₂ k| + |t * c₃ * single k₃ k| :=
              abs_add_le _ _
          _ ≤ |t * c₁ * single k₁ k| + |t * c₂ * single k₂ k| + |t * c₃ * single k₃ k| := by
              gcongr
              exact abs_add_le _ _
          _ ≤ |t| * |c₁| + |t| * |c₂| + |t| * |c₃| := by
              linarith [hterm c₁ k₁ k, hterm c₂ k₂ k, hterm c₃ k₃ k]
      have hneg := neg_abs_le (t * c₁ * single k₁ k + t * c₂ * single k₂ k + t * c₃ * single k₃ k)
      have ht0 : 0 ≤ |t| := abs_nonneg t
      nlinarith
    · simp only [not_or] at hk
      simp [single, hk.1, hk.2.1, hk.2.2, e.a_pos k]
  have hcancel : headSum e.w (fun k => e.a k + t * c₁ * single k₁ k + t * c₂ * single k₂ k +
      t * c₃ * single k₃ k) e.y = 0 := by
    rw [headSum_add, headSum_add, headSum_add, headSum_mul, headSum_mul, headSum_mul,
      headSum_single _ _ hk₁, headSum_single _ _ hk₂, headSum_single _ _ hk₃, e.cancel, zero_add]
    have s₁ := site_term e.w e.y k₁ hv₁ hc₁
    have s₂ := site_term e.w e.y k₂ hv₂ hc₂
    have s₃ := site_term e.w e.y k₃ hv₃ hc₃
    push_cast
    linear_combination (t : ℂ) * s₁ + (t : ℂ) * s₂ + (t : ℂ) * s₃ + (t : ℂ) * tri
  refine ⟨⟨e.w, e.w_one,
      fun k => e.a k + t * c₁ * single k₁ k + t * c₂ * single k₂ k + t * c₃ * single k₃ k,
      hpos, e.y, e.head_gt, hcancel⟩, rfl, rfl, rfl, ?_, ?_⟩
  · show e.a 0 + t * c₁ * single k₁ 0 + t * c₂ * single k₂ 0 + t * c₃ * single k₃ 0 = e.a 0
    simp [single, show (0 : ℕ) ≠ k₁ by omega, show (0 : ℕ) ≠ k₂ by omega,
      show (0 : ℕ) ≠ k₃ by omega]
  · show headUnsigned e.w (fun k => e.a k + t * c₁ * single k₁ k + t * c₂ * single k₂ k +
      t * c₃ * single k₃ k) e.y = headUnsigned e.w e.a e.y + t * (x₁ + x₂ + x₃)
    rw [headUnsigned_add, headUnsigned_add, headUnsigned_add, headUnsigned_mul, headUnsigned_mul,
      headUnsigned_mul, headUnsigned_single _ _ hk₁, headUnsigned_single _ _ hk₂,
      headUnsigned_single _ _ hk₃]
    linear_combination t * hc₁ + t * hc₂ + t * hc₃

end CriticalLinePhasor.FocalMass

end

#print axioms CriticalLinePhasor.FocalMass.two_mul_norm_le_mass
#print axioms CriticalLinePhasor.FocalMass.eigenMass_scaleEvent
#print axioms CriticalLinePhasor.FocalMass.triangle_combination
#print axioms CriticalLinePhasor.FocalMass.triangle_area_ne_zero
#print axioms CriticalLinePhasor.FocalMass.focal_mass_not_forced
