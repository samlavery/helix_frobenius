import RequestProject.HilbertPolyaResolventTrace
import RequestProject.FoliatedGlobalPolarization

/-!
# The scalar seat: the resolvent energy identity, compiled

`hp_pencil` (`prop:scalarseat`) works with
`S(s) = Σ_ρ m_ρ (s−ρ)^{-1}(s̄−1+ρ)^{-1}`, whose closed form is
`2 Re[ξ'/ξ](s)/(2σ−1)`, and RH ⟺ `S ≥ 0` in the strip off the zero set.

This file compiles the engine identity in spectral coordinates: the seat
energy is the FE-pairing energy of the resolvent vector
`c_w(ρ) = (t_ρ − w)^{-1}`, and it equals one instance of the compiled
two-point resolvent trace at the anchor pair `(w, conj w)` divided by the
anchor separation:

`Σ'_ρ m_ρ (t_ρ−w)^{-1}(t_ρ−w̄)^{-1}
   = [−i(ξ'/ξ(½+iw) − ξ'/ξ(½+iw̄))] / (w − w̄)`.

Chart reading: `½ + i·conj w = 1 − conj(½+iw)` (`chart_conj_anchor`), so the
anchor pair is `(s, 1−s̄)` — the scalar seat's FE pairing exactly; and
`w − w̄ ≠ 0` is `σ ≠ ½`, the seat's `(2σ−1)` denominator.  Everything is
unconditional and exact; nothing here constrains the sign of the energy.
-/

open Complex

namespace CriticalLinePhasor.SeatScalar

open CriticalLinePhasor.HilbertPolya

/-- The conjugate anchor in the chart is the FE-reflected conjugate point:
`½ + i·conj w = 1 − conj(½ + i·w)`. -/
theorem chart_conj_anchor (w : ℂ) :
    (1 : ℂ) / 2 + Complex.I * (starRingEnd ℂ) w
      = 1 - (starRingEnd ℂ) (1 / 2 + Complex.I * w) := by
  simp only [map_add, map_mul, Complex.conj_I, map_div₀, map_one, map_ofNat]
  ring

/-- Off the zero set in the chart, the spectral resolvent is nonsingular. -/
theorem spectral_sub_ne {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) :
    spectralCoord ρ.val - w ≠ 0 := by
  rw [spectralCoord_sub]
  exact mul_ne_zero Complex.I_ne_zero (sub_ne_zero_of_not_mem hw ρ.2)

/-- **Summability of the seat energy.** -/
theorem summable_seat_energy {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (him : w - (starRingEnd ℂ) w ≠ 0) :
    Summable (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} =>
      (ZD.xiOrderNat ρ.val : ℂ) *
        ((spectralCoord ρ.val - w)⁻¹ *
          (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)) := by
  have h := (summable_spectral_diff hw hw').mul_left (w - (starRingEnd ℂ) w)⁻¹
  apply h.congr
  intro ρ
  have h1 := spectral_sub_ne hw ρ
  have h2 := spectral_sub_ne hw' ρ
  field_simp
  ring

/-- **The seat energy identity** (`prop:scalarseat`'s engine, compiled): the
FE-pairing energy of the resolvent vector at anchor `w` equals the two-point
resolvent trace at the anchor pair `(w, conj w)` divided by `w − conj w`.
Unconditional; the anchor is off the critical line (`w ≠ conj w`) with both
chart points off the zero set. -/
theorem seat_energy_identity {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (him : w - (starRingEnd ℂ) w ≠ 0) :
    ∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)
      = (-Complex.I *
          (deriv ZD.riemannXi (1 / 2 + Complex.I * w)
              / ZD.riemannXi (1 / 2 + Complex.I * w)
            - deriv ZD.riemannXi (1 / 2 + Complex.I * (starRingEnd ℂ) w)
              / ZD.riemannXi (1 / 2 + Complex.I * (starRingEnd ℂ) w)))
        / (w - (starRingEnd ℂ) w) := by
  rw [eq_div_iff him, ← hilbertPolya_resolvent_trace hw hw', ← tsum_mul_right]
  refine tsum_congr fun ρ => ?_
  have h1 := spectral_sub_ne hw ρ
  have h2 := spectral_sub_ne hw' ρ
  field_simp
  ring

/-- On the critical line the spectral coordinate is real. -/
theorem spectralCoord_real_of_online {ρ : ℂ} (h : ρ.re = 1 / 2) :
    (starRingEnd ℂ) (spectralCoord ρ) = spectralCoord ρ := by
  rw [Complex.conj_eq_iff_im]
  unfold spectralCoord
  simp only [Complex.mul_im, Complex.neg_re, Complex.I_re, Complex.neg_im,
    Complex.I_im, Complex.sub_re, Complex.sub_im, neg_zero, zero_mul]
  norm_num [h]

/-- **The forward half of the scalar seat criterion, compiled**: if every
nontrivial zero lies on the critical line, every seat-energy term is
`m_ρ · |t_ρ − w|⁻²`, so the energy has nonnegative real part at every
admissible anchor.  The converse — an off-line zero forces a negative anchor
value — is the criterion's open content; its finite-window form is the
witness `feFormOn_offlineWitness` of the global polarization file. -/
theorem seat_energy_nonneg_of_online
    (hon : ∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2) {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (him : w - (starRingEnd ℂ) w ≠ 0) :
    0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re := by
  have hsum := summable_seat_energy hw hw' him
  rw [Complex.re_tsum hsum]
  refine tsum_nonneg fun ρ => ?_
  have hfac : spectralCoord ρ.val - (starRingEnd ℂ) w
      = (starRingEnd ℂ) (spectralCoord ρ.val - w) := by
    rw [map_sub, spectralCoord_real_of_online (hon ρ.val ρ.2)]
  rw [hfac, ← map_inv₀, Complex.mul_conj, ← Complex.ofReal_natCast,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)

/-! ## The converse witness, piece (i): exact off-line term blow-up

The criterion's converse (an off-line zero forces a negative anchor value)
decomposes as (i) the family term at the off-line zero, (ii) a uniform tail
bound on an anchor ball, (iii) limit assembly.  Piece (i) is *exact*: at the
vertical anchor `w = t₀ + εi` the seat term of a zero with spectral
coordinate `t₀` is the real number `1/(ε(2·Im t₀ + ε))` — for an off-line
zero `Im t₀ = ½ − β ≠ 0`, so on the side `Im t₀ < 0` and depth `ε < 2|Im t₀|`
the term is exactly `−1/(ε(2|Im t₀| − ε))`, blowing down like `−1/ε`.  No
estimate enters. -/

/-- **Exact seat term at vertical approach**: the resolvent-pair product of a
zero against the anchor `t₀ + εi` is real with closed form
`1/(ε(2·Im t₀ + ε))`. -/
theorem seat_term_vertical (t₀ : ℂ) {ε : ℝ} (hε : ε ≠ 0)
    (hδ : 2 * t₀.im + ε ≠ 0) :
    (t₀ - (t₀ + (ε : ℂ) * Complex.I))⁻¹ *
      (t₀ - (starRingEnd ℂ) (t₀ + (ε : ℂ) * Complex.I))⁻¹
      = (((ε * (2 * t₀.im + ε) : ℝ) : ℂ))⁻¹ := by
  have h1 : t₀ - (t₀ + (ε : ℂ) * Complex.I) = -(ε : ℂ) * Complex.I := by ring
  have h2 : t₀ - (starRingEnd ℂ) (t₀ + (ε : ℂ) * Complex.I)
      = ((2 * t₀.im + ε : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;>
      simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im] <;>
      ring
  rw [h1, h2, ← mul_inv]
  congr 1
  push_cast
  linear_combination (-(ε : ℂ) * (2 * (t₀.im : ℂ) + ε)) * Complex.I_sq

/-- **The off-line sign, exact**: on the shallow side (`Im t₀ < 0`, i.e.
`β > ½`) and inside the pair depth (`0 < ε < 2|Im t₀|`), the seat term at the
vertical anchor is strictly negative — value `1/(ε(2·Im t₀ + ε)) < 0`. -/
theorem seat_term_vertical_neg (t₀ : ℂ) {ε : ℝ}
    (him : t₀.im < 0) (hε : 0 < ε) (hdepth : ε < 2 * (-t₀.im)) :
    ((t₀ - (t₀ + (ε : ℂ) * Complex.I))⁻¹ *
      (t₀ - (starRingEnd ℂ) (t₀ + (ε : ℂ) * Complex.I))⁻¹).re < 0 := by
  have hδ : 2 * t₀.im + ε ≠ 0 := by nlinarith
  rw [seat_term_vertical t₀ (ne_of_gt hε) hδ, ← Complex.ofReal_inv,
    Complex.ofReal_re]
  have hneg : ε * (2 * t₀.im + ε) < 0 := by nlinarith
  exact inv_lt_zero.mpr hneg

/-! ## Converse pieces toward (ii): the partner term, the chart isometry, and
the far-zero majorant -/

/-- **The FE partner doubles the negativity**: at the same vertical anchor the
term of the reflected zero (spectral coordinate `conj t₀`) has the SAME real
closed form — no cancellation inside the reflection family. -/
theorem seat_term_vertical_partner (t₀ : ℂ) {ε : ℝ} (hε : ε ≠ 0)
    (hδ : 2 * t₀.im + ε ≠ 0) :
    ((starRingEnd ℂ) t₀ - (t₀ + (ε : ℂ) * Complex.I))⁻¹ *
      ((starRingEnd ℂ) t₀ - (starRingEnd ℂ) (t₀ + (ε : ℂ) * Complex.I))⁻¹
      = (((ε * (2 * t₀.im + ε) : ℝ) : ℂ))⁻¹ := by
  have h1 : (starRingEnd ℂ) t₀ - (t₀ + (ε : ℂ) * Complex.I)
      = -(((2 * t₀.im + ε : ℝ) : ℂ)) * Complex.I := by
    apply Complex.ext <;>
      simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im] <;>
      ring
  have h2 : (starRingEnd ℂ) t₀ - (starRingEnd ℂ) (t₀ + (ε : ℂ) * Complex.I)
      = (ε : ℂ) * Complex.I := by
    apply Complex.ext <;>
      simp [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
        Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
        Complex.ofReal_re, Complex.ofReal_im]
  rw [h1, h2, ← mul_inv]
  congr 1
  push_cast
  linear_combination (-(2 * (t₀.im : ℂ) + ε) * ε) * Complex.I_sq

/-- Chart isometry: spectral-coordinate distances are s-chart distances. -/
theorem norm_spectralCoord_sub (ρ w : ℂ) :
    ‖spectralCoord ρ - w‖ = ‖(1 / 2 + Complex.I * w) - ρ‖ := by
  rw [spectralCoord_sub, norm_mul, Complex.norm_I, one_mul]

/-- **Far-zero majorant, uniform over anchor balls**: if both chart points
have norm at most `S` and `‖ρ‖ ≥ 2S + 2`, the seat term is bounded by
`4 m_ρ / ‖ρ‖²` — the compiled counting majorant's shape, so the far tail is
summable uniformly on anchor balls. -/
theorem seat_term_far_bound {w : ℂ} {S : ℝ}
    (h1 : ‖(1 / 2 + Complex.I * w)‖ ≤ S)
    (h2 : ‖(1 / 2 + Complex.I * (starRingEnd ℂ) w)‖ ≤ S)
    (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) (hρ : 2 * S + 2 ≤ ‖ρ.val‖) :
    ‖(ZD.xiOrderNat ρ.val : ℂ) *
        ((spectralCoord ρ.val - w)⁻¹ *
          (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)‖
      ≤ 4 * (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2 := by
  have hS : 0 ≤ S := le_trans (norm_nonneg _) h1
  have hρpos : 0 < ‖ρ.val‖ := by linarith
  have hhalf : ‖ρ.val‖ / 2 ≤ ‖ρ.val‖ - S := by linarith
  have hd1 : ‖ρ.val‖ / 2 ≤ ‖spectralCoord ρ.val - w‖ := by
    rw [norm_spectralCoord_sub]
    have := norm_sub_norm_le ρ.val (1 / 2 + Complex.I * w)
    have hrev : ‖ρ.val‖ - ‖(1 / 2 + Complex.I * w)‖
        ≤ ‖(1 / 2 + Complex.I * w) - ρ.val‖ := by
      rw [norm_sub_rev]
      linarith [norm_sub_norm_le ρ.val (1 / 2 + Complex.I * w)]
    linarith
  have hd2 : ‖ρ.val‖ / 2 ≤ ‖spectralCoord ρ.val - (starRingEnd ℂ) w‖ := by
    rw [norm_spectralCoord_sub]
    have hrev : ‖ρ.val‖ - ‖(1 / 2 + Complex.I * (starRingEnd ℂ) w)‖
        ≤ ‖(1 / 2 + Complex.I * (starRingEnd ℂ) w) - ρ.val‖ := by
      rw [norm_sub_rev]
      linarith [norm_sub_norm_le ρ.val (1 / 2 + Complex.I * (starRingEnd ℂ) w)]
    linarith
  have hpos1 : (0 : ℝ) < ‖spectralCoord ρ.val - w‖ := by linarith
  have hpos2 : (0 : ℝ) < ‖spectralCoord ρ.val - (starRingEnd ℂ) w‖ := by linarith
  rw [norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_natCast]
  have hi1 : ‖spectralCoord ρ.val - w‖⁻¹ ≤ (‖ρ.val‖ / 2)⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) hd1
  have hi2 : ‖spectralCoord ρ.val - (starRingEnd ℂ) w‖⁻¹ ≤ (‖ρ.val‖ / 2)⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) hd2
  have hprod : ‖spectralCoord ρ.val - w‖⁻¹ *
      ‖spectralCoord ρ.val - (starRingEnd ℂ) w‖⁻¹ ≤ 4 / ‖ρ.val‖ ^ 2 := by
    calc ‖spectralCoord ρ.val - w‖⁻¹ *
          ‖spectralCoord ρ.val - (starRingEnd ℂ) w‖⁻¹
        ≤ (‖ρ.val‖ / 2)⁻¹ * (‖ρ.val‖ / 2)⁻¹ :=
          mul_le_mul hi1 hi2 (by positivity) (by positivity)
      _ = 4 / ‖ρ.val‖ ^ 2 := by
          field_simp
          ring
  calc (ZD.xiOrderNat ρ.val : ℝ) * (‖spectralCoord ρ.val - w‖⁻¹ *
        ‖spectralCoord ρ.val - (starRingEnd ℂ) w‖⁻¹)
      ≤ (ZD.xiOrderNat ρ.val : ℝ) * (4 / ‖ρ.val‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _)
    _ = 4 * (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2 := by ring

/-! ## Assembly of the converse: the two spectral coordinates line up -/

/-- The two `spectralCoord` definitions agree. -/
theorem spectralCoord_eq_foliated (ρ : ℂ) :
    CriticalLinePhasor.HilbertPolya.spectralCoord ρ
      = CriticalLinePhasor.FoliatedPolarization.spectralCoord ρ := rfl

/-- The FE partner's spectral coordinate is the conjugate. -/
theorem spectralCoord_feReflect' (ρ : ℂ) :
    CriticalLinePhasor.HilbertPolya.spectralCoord
        (CriticalLinePhasor.FoliatedPolarization.feReflect ρ)
      = (starRingEnd ℂ) (CriticalLinePhasor.HilbertPolya.spectralCoord ρ) := by
  rw [spectralCoord_eq_foliated, spectralCoord_eq_foliated]
  exact CriticalLinePhasor.FoliatedPolarization.spectralCoord_feReflect ρ

/-- The chart point of the vertical anchor: `½ + i(t₀ + εi) = ρ₀ − ε`. -/
theorem chart_vertical_anchor (ρ₀ : ℂ) (ε : ℝ) :
    (1 : ℂ) / 2 + Complex.I * (spectralCoord ρ₀ + (ε : ℂ) * Complex.I)
      = ρ₀ - (ε : ℂ) := by
  unfold spectralCoord
  linear_combination (-(ρ₀ - 1 / 2) + (ε : ℂ)) * Complex.I_mul_I

/-- The conjugate chart point of the vertical anchor:
`½ + i·conj(t₀ + εi) = (1 − conj ρ₀) + ε`. -/
theorem chart_vertical_anchor_conj (ρ₀ : ℂ) (ε : ℝ) :
    (1 : ℂ) / 2 + Complex.I *
        (starRingEnd ℂ) (spectralCoord ρ₀ + (ε : ℂ) * Complex.I)
      = (1 - (starRingEnd ℂ) ρ₀) + (ε : ℂ) := by
  unfold spectralCoord
  simp only [map_add, map_mul, map_sub, Complex.conj_I, map_neg, map_div₀,
    map_one, map_ofNat, Complex.conj_ofReal]
  linear_combination ((starRingEnd ℂ) ρ₀ - 1 / 2 - (ε : ℂ)) * Complex.I_mul_I

/-- Bad anchors are finite: only finitely many `ε` put the chart point on a
zero. -/
theorem finite_bad_eps (z : ℂ) :
    {ε : ℝ | z - (ε : ℂ) ∈ ZD.NontrivialZeros ∧ |ε| < 1}.Finite := by
  have hfin : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} |
      ‖ρ.val‖ < ‖z‖ + 1}.Finite :=
    CriticalLinePhasor.StBridge.finite_smallZeros (‖z‖ + 1)
  have hmap : {ε : ℝ | z - (ε : ℂ) ∈ ZD.NontrivialZeros ∧ |ε| < 1}
      ⊆ (fun ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} => (z - ρ.val).re) ''
        {ρ | ‖ρ.val‖ < ‖z‖ + 1} := by
    intro ε ⟨hε, hlt⟩
    refine ⟨⟨z - (ε : ℂ), hε⟩, ?_, ?_⟩
    · show ‖z - (ε : ℂ)‖ < ‖z‖ + 1
      calc ‖z - (ε : ℂ)‖ ≤ ‖z‖ + ‖(ε : ℂ)‖ := norm_sub_le z _
        _ < ‖z‖ + 1 := by
            rw [Complex.norm_real]
            simpa [Real.norm_eq_abs] using hlt
    · show (z - (z - (ε : ℂ))).re = ε
      simp
  exact (hfin.image _).subset hmap

/-- **Clearance radius**: around any two marked points there is `r > 0` with
every other zero at distance at least `2r` from both. -/
theorem exists_clearance (ρ₀ ρstar : ℂ) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 2 ∧
      ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, ρ.val ≠ ρ₀ → ρ.val ≠ ρstar →
        2 * r ≤ ‖ρ.val - ρ₀‖ ∧ 2 * r ≤ ‖ρ.val - ρstar‖ := by
  classical
  set R₁ : ℝ := max ‖ρ₀‖ ‖ρstar‖ + 1 with hR₁
  have hfin := CriticalLinePhasor.StBridge.finite_smallZeros R₁
  set E : Finset {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} :=
    hfin.toFinset.filter (fun ρ => ρ.val ≠ ρ₀ ∧ ρ.val ≠ ρstar) with hE
  have hfar : ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}, ρ.val ≠ ρ₀ →
      ρ.val ≠ ρstar → ρ ∉ E →
      1 ≤ ‖ρ.val - ρ₀‖ ∧ 1 ≤ ‖ρ.val - ρstar‖ := by
    intro ρ h1 h2 hnotE
    have hbig : R₁ ≤ ‖ρ.val‖ := by
      by_contra hlt
      push_neg at hlt
      exact hnotE (by
        rw [hE, Finset.mem_filter]
        exact ⟨hfin.mem_toFinset.mpr hlt, h1, h2⟩)
    constructor
    · calc (1 : ℝ) ≤ R₁ - ‖ρ₀‖ := by
            have := le_max_left ‖ρ₀‖ ‖ρstar‖
            rw [hR₁]; linarith
        _ ≤ ‖ρ.val‖ - ‖ρ₀‖ := by linarith
        _ ≤ ‖ρ.val - ρ₀‖ := by
            have := norm_sub_norm_le ρ.val ρ₀
            linarith [abs_le.mp (abs_norm_sub_norm_le ρ.val ρ₀)]
    · calc (1 : ℝ) ≤ R₁ - ‖ρstar‖ := by
            have := le_max_right ‖ρ₀‖ ‖ρstar‖
            rw [hR₁]; linarith
        _ ≤ ‖ρ.val‖ - ‖ρstar‖ := by linarith
        _ ≤ ‖ρ.val - ρstar‖ := by
            linarith [abs_le.mp (abs_norm_sub_norm_le ρ.val ρstar)]
  by_cases hEne : E.Nonempty
  · obtain ⟨a, haE, hamin⟩ := E.exists_min_image
      (fun ρ => min ‖ρ.val - ρ₀‖ ‖ρ.val - ρstar‖) hEne
    have haprop := Finset.mem_filter.mp (hE ▸ haE)
    have hdpos : 0 < min ‖a.val - ρ₀‖ ‖a.val - ρstar‖ :=
      lt_min (norm_sub_pos_iff.mpr haprop.2.1) (norm_sub_pos_iff.mpr haprop.2.2)
    set d : ℝ := min ‖a.val - ρ₀‖ ‖a.val - ρstar‖ with hd
    refine ⟨min (d / 2) (1 / 2), by positivity, min_le_right _ _, ?_⟩
    intro ρ h1 h2
    by_cases hρE : ρ ∈ E
    · have hm := hamin ρ hρE
      have h2r : 2 * min (d / 2) (1 / 2) ≤ d := by
        have := min_le_left (d / 2) (1 / 2)
        linarith
      constructor
      · calc 2 * min (d / 2) (1 / 2) ≤ d := h2r
          _ ≤ min ‖ρ.val - ρ₀‖ ‖ρ.val - ρstar‖ := hm
          _ ≤ ‖ρ.val - ρ₀‖ := min_le_left _ _
      · calc 2 * min (d / 2) (1 / 2) ≤ d := h2r
          _ ≤ min ‖ρ.val - ρ₀‖ ‖ρ.val - ρstar‖ := hm
          _ ≤ ‖ρ.val - ρstar‖ := min_le_right _ _
    · have hf := hfar ρ h1 h2 hρE
      have h2r : 2 * min (d / 2) (1 / 2) ≤ 1 := by
        have := min_le_right (d / 2) (1 / 2)
        linarith
      exact ⟨le_trans h2r hf.1, le_trans h2r hf.2⟩
  · refine ⟨1 / 2, by norm_num, le_refl _, ?_⟩
    intro ρ h1 h2
    have hρE : ρ ∉ E := fun h => hEne ⟨ρ, h⟩
    have hf := hfar ρ h1 h2 hρE
    constructor <;> linarith [hf.1, hf.2]

set_option maxHeartbeats 1600000 in
/-- **The converse of the scalar seat criterion, compiled**: an off-line zero
(`Re ρ₀ > ½`) forces an admissible anchor at which the seat energy is
strictly negative.  The anchor is vertical over the zero's spectral
coordinate; the reflection family contributes the exact value
`−2m₀/(ε(2δ−ε))` and the tail is beaten by choosing `ε` small against the
uniform clearance majorant. -/
theorem exists_seat_energy_neg {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ ZD.NontrivialZeros)
    (hoff : 1 / 2 < ρ₀.re) :
    ∀ ε₀ : ℝ, 0 < ε₀ →
    ∃ w : ℂ, w.re = ρ₀.im ∧ ρ₀.re - 1 / 2 - ε₀ < |w.im| ∧
      ((1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros) ∧
      ((1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros) ∧
      (w - (starRingEnd ℂ) w ≠ 0) ∧
      (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          (ZD.xiOrderNat ρ.val : ℂ) *
            ((spectralCoord ρ.val - w)⁻¹ *
              (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re < 0 := by
  classical
  intro ε₀ hε₀
  set t₀ : ℂ := spectralCoord ρ₀ with ht₀
  set δ : ℝ := ρ₀.re - 1 / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have ht₀im : t₀.im = -δ := by
    rw [ht₀, hδdef]
    unfold spectralCoord
    simp [Complex.mul_im]
  set ρstar : ℂ := CriticalLinePhasor.FoliatedPolarization.feReflect ρ₀ with hρs
  have hρstarmem : ρstar ∈ ZD.NontrivialZeros :=
    CriticalLinePhasor.FoliatedGlobalPolarization.feReflect_mem hρ₀
  have hstar_ne : ρstar ≠ ρ₀ := by
    intro h
    have := (CriticalLinePhasor.FoliatedPolarization.feReflect_eq_self_iff ρ₀).mp
      (hρs ▸ h)
    linarith
  set P₀ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} := ⟨ρ₀, hρ₀⟩ with hP₀
  set P₁ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} := ⟨ρstar, hρstarmem⟩ with hP₁
  have hP01 : P₀ ≠ P₁ := fun h => hstar_ne (congrArg Subtype.val h).symm
  set m₀ : ℕ := ZD.xiOrderNat ρ₀ with hm₀
  have hm₀pos : 0 < m₀ := ZD.xiOrderNat_pos_of_mem_NontrivialZeros hρ₀
  have hm₁ : ZD.xiOrderNat ρstar = m₀ := by
    rw [hρs, hm₀]
    exact CriticalLinePhasor.FoliatedGlobalPolarization.xiOrderNat_feReflect ρ₀
  -- clearance and majorant data
  obtain ⟨r, hrpos, hr12, hclear⟩ := exists_clearance ρ₀ ρstar
  set S : ℝ := max ‖ρ₀‖ ‖ρstar‖ + 2 with hSdef
  set R₀ : ℝ := 2 * S + 2 with hR₀def
  have hfinE := CriticalLinePhasor.StBridge.finite_smallZeros R₀
  set Efin : Finset {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} := hfinE.toFinset with hEfin
  set u : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} → ℝ := fun ρ =>
    (if ρ ∈ Efin then (ZD.xiOrderNat ρ.val : ℝ) / r ^ 2 else 0) +
      4 * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) with hu
  have hu_nonneg : ∀ ρ, 0 ≤ u ρ := by
    intro ρ
    simp only [hu]
    have h2 : (0:ℝ) ≤ 4 * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by positivity
    split_ifs with h
    · have : (0:ℝ) ≤ (ZD.xiOrderNat ρ.val : ℝ) / r ^ 2 := by positivity
      linarith
    · linarith
  have hu_summ : Summable u := by
    apply Summable.add
    · apply summable_of_ne_finset_zero (s := Efin)
      intro ρ hρ
      simp [hu, hρ]
    · exact (ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros).mul_left 4
  set C : ℝ := ∑' ρ, u ρ with hC
  have hC_nonneg : 0 ≤ C := tsum_nonneg hu_nonneg
  -- choose ε
  set ε₂ : ℝ := min (min (min r δ) (1 / (δ * (C + 1)))) ε₀ with hε₂
  have hε₂pos : 0 < ε₂ := by
    rw [hε₂]
    have : 0 < 1 / (δ * (C + 1)) := by positivity
    exact lt_min (lt_min (lt_min hrpos hδ) this) hε₀
  have hbadfin : ({ε : ℝ | ρ₀ - (ε : ℂ) ∈ ZD.NontrivialZeros ∧ |ε| < 1} ∪
      (fun ε => -ε) '' {ε : ℝ | ρstar - (ε : ℂ) ∈ ZD.NontrivialZeros ∧ |ε| < 1}).Finite :=
    (finite_bad_eps ρ₀).union ((finite_bad_eps ρstar).image _)
  obtain ⟨ε, hεmem⟩ := ((Set.Ioo_infinite hε₂pos).diff hbadfin).nonempty
  obtain ⟨⟨hε0, hεlt⟩, hεgood⟩ := hεmem
  have hεr : ε < r := lt_of_lt_of_le hεlt
    (le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_left _ _))
  have hεδ : ε < δ := lt_of_lt_of_le hεlt
    (le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_right _ _))
  have hεC : ε < 1 / (δ * (C + 1)) := lt_of_lt_of_le hεlt
    (le_trans (min_le_left _ _) (min_le_right _ _))
  have hεε₀ : ε < ε₀ := lt_of_lt_of_le hεlt (min_le_right _ _)
  have hε1 : |ε| < 1 := by
    rw [abs_of_pos hε0]
    linarith
  -- the anchor
  set w : ℂ := t₀ + (ε : ℂ) * Complex.I with hw
  have hchart : (1 : ℂ) / 2 + Complex.I * w = ρ₀ - (ε : ℂ) := by
    rw [hw, ht₀]; exact chart_vertical_anchor ρ₀ ε
  have hchart' : (1 : ℂ) / 2 + Complex.I * (starRingEnd ℂ) w
      = ρstar + (ε : ℂ) := by
    rw [hw, ht₀, hρs]
    have := chart_vertical_anchor_conj ρ₀ ε
    rw [this]
    rfl
  have hadm : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros := by
    rw [hchart]
    intro hmem
    exact hεgood (Set.mem_union_left _ ⟨hmem, hε1⟩)
  have hadm' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros := by
    rw [hchart']
    intro hmem
    refine hεgood (Set.mem_union_right _ ⟨-ε, ⟨?_, ?_⟩, ?_⟩)
    · push_cast
      simpa [sub_neg_eq_add] using hmem
    · rwa [abs_neg]
    · ring
  have hwim : w.im = ε - δ := by
    have h1 : ((ε : ℂ) * Complex.I).im = ε := by simp
    rw [hw, Complex.add_im, h1, ht₀im]
    ring
  have him : w - (starRingEnd ℂ) w ≠ 0 := by
    intro h
    have h2 : (w - (starRingEnd ℂ) w).im = 0 := by rw [h]; simp
    rw [Complex.sub_im, Complex.conj_im, hwim] at h2
    have : ε = δ := by linarith
    linarith [hεδ]
  have hwre : w.re = ρ₀.im := by
    have h1 : ((ε : ℂ) * Complex.I).re = 0 := by simp
    have h2 : t₀.re = ρ₀.im := by
      rw [ht₀]
      unfold spectralCoord
      simp [Complex.mul_re]
    rw [hw, Complex.add_re, h1, h2, add_zero]
  have hwimabs : ρ₀.re - 1 / 2 - ε₀ < |w.im| := by
    rw [hwim, abs_of_neg (by linarith : ε - δ < 0)]
    have : δ = ρ₀.re - 1 / 2 := hδdef
    linarith [hεε₀]
  refine ⟨w, hwre, hwimabs, hadm, hadm', him, ?_⟩
  set f : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} → ℂ := fun ρ =>
    (ZD.xiOrderNat ρ.val : ℂ) *
      ((spectralCoord ρ.val - w)⁻¹ *
        (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹) with hf
  have hsumm : Summable f := summable_seat_energy hadm hadm' him
  have hsplit := hsumm.sum_add_tsum_compl (s := ({P₀, P₁} : Finset _))
  -- the exact family values
  have hδε : 2 * t₀.im + ε ≠ 0 := by
    rw [ht₀im]
    intro h
    have : ε = 2 * δ := by linarith
    linarith [hεδ, hδ]
  have hV : f P₀ = (m₀ : ℂ) * (((ε * (2 * t₀.im + ε) : ℝ) : ℂ))⁻¹ := by
    have h0 : f P₀ = (m₀ : ℂ) *
        ((t₀ - w)⁻¹ * (t₀ - (starRingEnd ℂ) w)⁻¹) := by
      simp only [hf, hP₀, ht₀, hm₀]
    rw [h0, hw, seat_term_vertical t₀ (ne_of_gt hε0) hδε]
  have hV' : f P₁ = (m₀ : ℂ) * (((ε * (2 * t₀.im + ε) : ℝ) : ℂ))⁻¹ := by
    have hsc : spectralCoord ρstar = (starRingEnd ℂ) t₀ := by
      rw [hρs, ht₀]
      exact spectralCoord_feReflect' ρ₀
    have h0 : f P₁ = (m₀ : ℂ) *
        (((starRingEnd ℂ) t₀ - w)⁻¹ *
          ((starRingEnd ℂ) t₀ - (starRingEnd ℂ) w)⁻¹) := by
      simp only [hf, hP₁, hsc, hm₁]
    rw [h0, hw, seat_term_vertical_partner t₀ (ne_of_gt hε0) hδε]
  have hfam : ∑ x ∈ ({P₀, P₁} : Finset _), f x
      = ((2 * m₀ : ℝ) : ℂ) * (((ε * (2 * t₀.im + ε) : ℝ) : ℂ))⁻¹ := by
    rw [Finset.sum_pair hP01, hV, hV']
    push_cast
    ring
  -- the tail bound: termwise majorant u, uniform in the anchor
  have hterm_u : ∀ x : ((({P₀, P₁} : Finset _) : Set _)ᶜ : Set _),
      ‖f x.val‖ ≤ u x.val := by
    rintro ⟨ρ, hρc⟩
    have hρnot : ρ ∉ ({P₀, P₁} : Finset _) := by
      simpa using hρc
    have hv0 : ρ.val ≠ ρ₀ := fun h => hρnot (by
      rw [Finset.mem_insert]
      exact Or.inl (Subtype.ext h))
    have hv1 : ρ.val ≠ ρstar := fun h => hρnot (by
      rw [Finset.mem_insert, Finset.mem_singleton]
      exact Or.inr (Subtype.ext h))
    obtain ⟨hc0, hc1⟩ := hclear ρ hv0 hv1
    have hεnorm : ‖((ε : ℂ))‖ = ε := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]
    have hd1 : r ≤ ‖spectralCoord ρ.val - w‖ := by
      rw [norm_spectralCoord_sub, hchart]
      have htri := dist_triangle ρ.val (ρ₀ - (ε : ℂ)) ρ₀
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at htri
      have hεn : ‖(ρ₀ - (ε : ℂ)) - ρ₀‖ = ε := by
        rw [show (ρ₀ - (ε : ℂ)) - ρ₀ = -(ε : ℂ) by ring, norm_neg, hεnorm]
      rw [norm_sub_rev]
      rw [hεn] at htri
      linarith
    have hd2 : r ≤ ‖spectralCoord ρ.val - (starRingEnd ℂ) w‖ := by
      rw [norm_spectralCoord_sub, hchart']
      have htri := dist_triangle ρ.val (ρstar + (ε : ℂ)) ρstar
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at htri
      have hεn : ‖(ρstar + (ε : ℂ)) - ρstar‖ = ε := by
        rw [show (ρstar + (ε : ℂ)) - ρstar = (ε : ℂ) by ring, hεnorm]
      rw [norm_sub_rev]
      rw [hεn] at htri
      linarith
    have hnormf : ‖f ρ‖ = (ZD.xiOrderNat ρ.val : ℝ) *
        (‖spectralCoord ρ.val - w‖⁻¹ *
          ‖spectralCoord ρ.val - (starRingEnd ℂ) w‖⁻¹) := by
      rw [hf]
      simp only [norm_mul, norm_inv, Complex.norm_natCast]
    by_cases hin : ρ ∈ Efin
    · have hb1 : ‖spectralCoord ρ.val - w‖⁻¹ ≤ r⁻¹ := by
        rw [← one_div, ← one_div]
        exact one_div_le_one_div_of_le hrpos hd1
      have hb2 : ‖spectralCoord ρ.val - (starRingEnd ℂ) w‖⁻¹ ≤ r⁻¹ := by
        rw [← one_div, ← one_div]
        exact one_div_le_one_div_of_le hrpos hd2
      have hp1 : (0:ℝ) < ‖spectralCoord ρ.val - w‖ := lt_of_lt_of_le hrpos hd1
      have hp2 : (0:ℝ) < ‖spectralCoord ρ.val - (starRingEnd ℂ) w‖ :=
        lt_of_lt_of_le hrpos hd2
      calc ‖f ρ‖ = (ZD.xiOrderNat ρ.val : ℝ) *
            (‖spectralCoord ρ.val - w‖⁻¹ *
              ‖spectralCoord ρ.val - (starRingEnd ℂ) w‖⁻¹) := hnormf
        _ ≤ (ZD.xiOrderNat ρ.val : ℝ) * (r⁻¹ * r⁻¹) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul hb1 hb2 (by positivity) (by positivity))
              (Nat.cast_nonneg _)
        _ = (ZD.xiOrderNat ρ.val : ℝ) / r ^ 2 := by
            field_simp
        _ ≤ u ρ := by
            simp only [hu, if_pos hin]
            have : (0:ℝ) ≤ 4 * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
              positivity
            linarith
    · have hfar : R₀ ≤ ‖ρ.val‖ := by
        by_contra hlt
        push_neg at hlt
        exact hin (hEfin ▸ hfinE.mem_toFinset.mpr hlt)
      have hs1 : ‖(1 / 2 + Complex.I * w : ℂ)‖ ≤ S := by
        rw [hchart]
        calc ‖ρ₀ - (ε : ℂ)‖ ≤ ‖ρ₀‖ + ‖(ε : ℂ)‖ := norm_sub_le _ _
          _ ≤ ‖ρ₀‖ + 1 := by rw [hεnorm]; linarith [hεr, hr12]
          _ ≤ S := by
              rw [hSdef]
              have := le_max_left ‖ρ₀‖ ‖ρstar‖
              linarith
      have hs2 : ‖(1 / 2 + Complex.I * (starRingEnd ℂ) w : ℂ)‖ ≤ S := by
        rw [hchart']
        calc ‖ρstar + (ε : ℂ)‖ ≤ ‖ρstar‖ + ‖(ε : ℂ)‖ := norm_add_le _ _
          _ ≤ ‖ρstar‖ + 1 := by rw [hεnorm]; linarith [hεr, hr12]
          _ ≤ S := by
              rw [hSdef]
              have := le_max_right ‖ρ₀‖ ‖ρstar‖
              linarith
      have hb := seat_term_far_bound hs1 hs2 ρ (by rw [← hR₀def]; exact hfar)
      calc ‖f ρ‖ ≤ 4 * (ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2 := by
            rw [hf]; exact hb
        _ = u ρ := by
            simp only [hu, if_neg hin]
            ring
  -- assemble
  have hcompl_summ : Summable fun x : ((({P₀, P₁} : Finset _) : Set _)ᶜ : Set _) =>
      ‖f x.val‖ := (hsumm.subtype _).norm
  have hucompl_summ : Summable fun x : ((({P₀, P₁} : Finset _) : Set _)ᶜ : Set _) =>
      u x.val := hu_summ.subtype _
  have htail_le : ‖∑' x : ((({P₀, P₁} : Finset _) : Set _)ᶜ : Set _), f x.val‖ ≤ C := by
    calc ‖∑' x : ((({P₀, P₁} : Finset _) : Set _)ᶜ : Set _), f x.val‖
        ≤ ∑' x : ((({P₀, P₁} : Finset _) : Set _)ᶜ : Set _), ‖f x.val‖ :=
          norm_tsum_le_tsum_norm hcompl_summ
      _ ≤ ∑' x : ((({P₀, P₁} : Finset _) : Set _)ᶜ : Set _), u x.val :=
          hcompl_summ.tsum_le_tsum hterm_u hucompl_summ
      _ ≤ C := by
          have hsplitu := hu_summ.sum_add_tsum_compl (s := ({P₀, P₁} : Finset _))
          have hfamu : 0 ≤ ∑ x ∈ ({P₀, P₁} : Finset _), u x :=
            Finset.sum_nonneg fun x _ => hu_nonneg x
          rw [hC]
          linarith [hsplitu]
  -- numbers
  set X : ℝ := ε * (2 * δ - ε) with hX
  have hXpos : 0 < X := by
    rw [hX]
    have : 0 < 2 * δ - ε := by linarith
    positivity
  have hXle : X ≤ 2 * δ * ε := by rw [hX]; nlinarith
  have hval : ε * (2 * t₀.im + ε) = -X := by rw [ht₀im, hX]; ring
  have hfamre : (((2 * m₀ : ℝ) : ℂ) * (((ε * (2 * t₀.im + ε) : ℝ) : ℂ))⁻¹).re
      = (2 * m₀ : ℝ) * (ε * (2 * t₀.im + ε))⁻¹ := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, Complex.ofReal_re]
  have htail_re : (∑' x : ((({P₀, P₁} : Finset _) : Set _)ᶜ : Set _), f x.val).re ≤ C := by
    have h1 : |(∑' x : ((({P₀, P₁} : Finset _) : Set _)ᶜ : Set _), f x.val).re|
        ≤ ‖∑' x : ((({P₀, P₁} : Finset _) : Set _)ᶜ : Set _), f x.val‖ :=
      Complex.abs_re_le_norm _
    have := abs_le.mp (le_trans h1 htail_le)
    linarith [this.2]
  have htotre : (∑' ρ, f ρ).re
      = (∑ x ∈ ({P₀, P₁} : Finset _), f x).re
        + (∑' x : ((({P₀, P₁} : Finset _) : Set _)ᶜ : Set _), f x.val).re := by
    rw [← hsplit, Complex.add_re]
  rw [htotre, hfam, hfamre, hval]
  -- (2m₀)·(−X)⁻¹ + tail.re < 0
  have hm₀1 : (1 : ℝ) ≤ (m₀ : ℝ) := by exact_mod_cast hm₀pos
  have hfamval : (2 * m₀ : ℝ) * (-X)⁻¹ ≤ -(2 / X) := by
    rw [inv_neg]
    have h2X : 0 < X⁻¹ := by positivity
    have : 2 / X ≤ (2 * m₀ : ℝ) * X⁻¹ := by
      rw [div_eq_mul_inv]
      have : (2:ℝ) ≤ 2 * m₀ := by linarith
      exact mul_le_mul_of_nonneg_right this (le_of_lt h2X)
    linarith
  have hCX : C * X < 2 := by
    have hδε' : δ * ε < 1 / (C + 1) := by
      have := (lt_div_iff₀ (by positivity : (0:ℝ) < δ * (C + 1))).mp hεC
      calc δ * ε = ε * δ := by ring
        _ < 1 / (C + 1) := by
          rw [lt_div_iff₀ (by positivity : (0:ℝ) < C + 1)]
          nlinarith
    have hδεpos : (0:ℝ) < δ * ε := by positivity
    have h3 : (δ * ε) * (C + 1) < 1 :=
      (lt_div_iff₀ (by positivity : (0:ℝ) < C + 1)).mp hδε'
    nlinarith [mul_le_mul_of_nonneg_left hXle hC_nonneg, h3, hδεpos, hC_nonneg]
  have hC2X : C < 2 / X := (lt_div_iff₀ hXpos).mpr hCX
  linarith [htail_re, hfamval, hC2X]

/-- **The scalar seat criterion, as a compiled iff** (`prop:scalarseat` of
`hp_pencil`, machine-checked in spectral coordinates): every nontrivial zero
lies on the critical line **iff** the seat energy is nonnegative at every
admissible anchor.  Forward: on-line terms are `m_ρ·|t_ρ−w|⁻²`.  Converse:
an off-line zero (either side, via its FE partner) yields an anchor with
strictly negative energy.  With `seat_energy_identity` the left side of the
inequality is the explicit arithmetic function
`[−i(ξ'/ξ(s) − ξ'/ξ(1−s̄))]/(w−w̄)`. -/
theorem seat_criterion_iff :
    (∀ ρ ∈ ZD.NontrivialZeros, ρ.re = 1 / 2)
      ↔ ∀ w : ℂ, ((1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros) →
          ((1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros) →
          (w - (starRingEnd ℂ) w ≠ 0) →
          0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
              (ZD.xiOrderNat ρ.val : ℂ) *
                ((spectralCoord ρ.val - w)⁻¹ *
                  (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re := by
  constructor
  · intro hon w hw hw' him
    exact seat_energy_nonneg_of_online hon hw hw' him
  · intro hpos ρ hρ
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hmem' := CriticalLinePhasor.FoliatedGlobalPolarization.feReflect_mem hρ
      have hre' : 1 / 2 <
          (CriticalLinePhasor.FoliatedPolarization.feReflect ρ).re := by
        have : (CriticalLinePhasor.FoliatedPolarization.feReflect ρ).re
            = 1 - ρ.re := by
          simp [CriticalLinePhasor.FoliatedPolarization.feReflect,
            Complex.sub_re, Complex.conj_re]
        rw [this]
        linarith
      obtain ⟨w, _, _, h1, h2, h3, h4⟩ :=
        exists_seat_energy_neg hmem' hre' 1 one_pos
      exact absurd (hpos w h1 h2 h3) (not_le.mpr h4)
    · obtain ⟨w, _, _, h1, h2, h3, h4⟩ :=
        exists_seat_energy_neg hρ hgt 1 one_pos
      exact absurd (hpos w h1 h2 h3) (not_le.mpr h4)

/-- The spectral coordinate's real part is the zero's ordinate. -/
theorem spectralCoord_re (z : ℂ) : (spectralCoord z).re = z.im := by
  unfold spectralCoord
  simp [Complex.mul_re]

/-- **The band tail bound**: zeros of height above `H` contribute to the seat
energy at anchors of height at most `H/2` no more than `8·Σ m_ρ/‖ρ‖²` over
the tail — uniformly in the anchor, with no admissibility hypothesis (the
tail's terms are nonsingular by the height separation alone). -/
theorem seat_tail_norm_le {w : ℂ} {H : ℝ} (hH : 2 ≤ H) (hre : |w.re| ≤ H / 2)
    (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) (hband : H < |ρ.val.im|) :
    ‖(ZD.xiOrderNat ρ.val : ℂ) *
        ((spectralCoord ρ.val - w)⁻¹ *
          (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)‖
      ≤ 8 * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
  have him2 : (0:ℝ) < |ρ.val.im| := by linarith
  -- both resolvent distances are at least |Im ρ|/2, by the ordinate identity
  have hkey : ∀ v : ℂ, v.re = w.re →
      |ρ.val.im| / 2 ≤ ‖spectralCoord ρ.val - v‖ := by
    intro v hv
    have hre' : (spectralCoord ρ.val - v).re = ρ.val.im - w.re := by
      rw [Complex.sub_re, spectralCoord_re, hv]
    calc |ρ.val.im| / 2 ≤ |ρ.val.im| - H / 2 := by linarith
      _ ≤ |ρ.val.im| - |w.re| := by linarith
      _ ≤ |ρ.val.im - w.re| := by
          have := abs_sub_abs_le_abs_sub ρ.val.im w.re
          linarith
      _ = |(spectralCoord ρ.val - v).re| := by rw [hre']
      _ ≤ ‖spectralCoord ρ.val - v‖ := Complex.abs_re_le_norm _
  have hd1 := hkey w rfl
  have hd2 := hkey ((starRingEnd ℂ) w) (Complex.conj_re w)
  have hp : (0:ℝ) < |ρ.val.im| / 2 := by linarith
  have hb1 : ‖spectralCoord ρ.val - w‖⁻¹ ≤ (|ρ.val.im| / 2)⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hp hd1
  have hb2 : ‖spectralCoord ρ.val - (starRingEnd ℂ) w‖⁻¹ ≤ (|ρ.val.im| / 2)⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hp hd2
  -- ‖ρ‖² ≤ 2·(Im ρ)², from the strip bound |Re ρ| < 1 < |Im ρ|
  have hstrip1 : 0 < ρ.val.re := ρ.2.1
  have hstrip2 : ρ.val.re < 1 := ρ.2.2.1
  have hnorm2 : ‖ρ.val‖ ^ 2 ≤ 2 * ρ.val.im ^ 2 := by
    have h1 : ‖ρ.val‖ ^ 2 = ρ.val.re ^ 2 + ρ.val.im ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    have h2 : ρ.val.re ^ 2 ≤ 1 := by nlinarith
    have h3 : (1:ℝ) ≤ ρ.val.im ^ 2 := by
      have : (2:ℝ) ≤ |ρ.val.im| := by linarith
      nlinarith [sq_abs ρ.val.im]
    linarith
  have hnormpos : (0:ℝ) < ‖ρ.val‖ := by
    rw [norm_pos_iff]
    intro h
    rw [h] at hstrip1
    simp at hstrip1
  rw [norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_natCast]
  calc (ZD.xiOrderNat ρ.val : ℝ) *
        (‖spectralCoord ρ.val - w‖⁻¹ *
          ‖spectralCoord ρ.val - (starRingEnd ℂ) w‖⁻¹)
      ≤ (ZD.xiOrderNat ρ.val : ℝ) * ((|ρ.val.im| / 2)⁻¹ * (|ρ.val.im| / 2)⁻¹) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hb1 hb2 (by positivity) (by positivity))
          (Nat.cast_nonneg _)
    _ = 4 * ((ZD.xiOrderNat ρ.val : ℝ) / ρ.val.im ^ 2) := by
        rw [show (|ρ.val.im| / 2)⁻¹ * (|ρ.val.im| / 2)⁻¹
            = 4 / |ρ.val.im| ^ 2 by field_simp; ring]
        rw [sq_abs]
        ring
    _ ≤ 8 * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
        have him2sq : (0:ℝ) < ρ.val.im ^ 2 := by
          nlinarith [him2, sq_abs ρ.val.im]
        have hnormsq : (0:ℝ) < ‖ρ.val‖ ^ 2 := pow_pos hnormpos 2
        have hdiv : (ZD.xiOrderNat ρ.val : ℝ) / ρ.val.im ^ 2
            ≤ 2 * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2) := by
          rw [show (2:ℝ) * ((ZD.xiOrderNat ρ.val : ℝ) / ‖ρ.val‖ ^ 2)
              = (2 * (ZD.xiOrderNat ρ.val : ℝ)) / ‖ρ.val‖ ^ 2 by ring]
          rw [div_le_div_iff₀ him2sq hnormsq]
          nlinarith [hnorm2, (Nat.cast_nonneg (ZD.xiOrderNat ρ.val) :
            (0:ℝ) ≤ (ZD.xiOrderNat ρ.val : ℝ))]
        linarith

/-- **The band tail, summed**: the total seat energy of all zeros above
height `H`, at any anchor of height at most `H/2`, is bounded by eight times
the tail of the compiled counting series — uniformly in the anchor. -/
theorem seat_tail_tsum_le {w : ℂ} {H : ℝ} (hH : 2 ≤ H) (hre : |w.re| ≤ H / 2) :
    ‖∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} // H < |ρ.val.im|},
        (ZD.xiOrderNat x.val.val : ℂ) *
          ((spectralCoord x.val.val - w)⁻¹ *
            (spectralCoord x.val.val - (starRingEnd ℂ) w)⁻¹)‖
      ≤ 8 * ∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} // H < |ρ.val.im|},
          (ZD.xiOrderNat x.val.val : ℝ) / ‖x.val.val‖ ^ 2 := by
  have hmaj : Summable fun
      x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} // H < |ρ.val.im|} =>
      (ZD.xiOrderNat x.val.val : ℝ) / ‖x.val.val‖ ^ 2 :=
    (ZD.summable_xiOrderNat_div_norm_sq_nontrivialZeros).subtype _
  have hbound : ∀ x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} // H < |ρ.val.im|},
      ‖(ZD.xiOrderNat x.val.val : ℂ) *
        ((spectralCoord x.val.val - w)⁻¹ *
          (spectralCoord x.val.val - (starRingEnd ℂ) w)⁻¹)‖
        ≤ 8 * ((ZD.xiOrderNat x.val.val : ℝ) / ‖x.val.val‖ ^ 2) :=
    fun x => seat_tail_norm_le hH hre x.val x.2
  have hnorm_summ : Summable fun
      x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} // H < |ρ.val.im|} =>
      ‖(ZD.xiOrderNat x.val.val : ℂ) *
        ((spectralCoord x.val.val - w)⁻¹ *
          (spectralCoord x.val.val - (starRingEnd ℂ) w)⁻¹)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound (hmaj.mul_left 8)
  calc ‖∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} // H < |ρ.val.im|},
        (ZD.xiOrderNat x.val.val : ℂ) *
          ((spectralCoord x.val.val - w)⁻¹ *
            (spectralCoord x.val.val - (starRingEnd ℂ) w)⁻¹)‖
      ≤ ∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} // H < |ρ.val.im|},
          ‖(ZD.xiOrderNat x.val.val : ℂ) *
            ((spectralCoord x.val.val - w)⁻¹ *
              (spectralCoord x.val.val - (starRingEnd ℂ) w)⁻¹)‖ :=
        norm_tsum_le_tsum_norm hnorm_summ
    _ ≤ ∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} // H < |ρ.val.im|},
          8 * ((ZD.xiOrderNat x.val.val : ℝ) / ‖x.val.val‖ ^ 2) :=
        hnorm_summ.tsum_le_tsum hbound (hmaj.mul_left 8)
    _ = 8 * ∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} // H < |ρ.val.im|},
          (ZD.xiOrderNat x.val.val : ℝ) / ‖x.val.val‖ ^ 2 := tsum_mul_left

/-- **The half-band floor** (the compiled shape of `prop:bandlocal` (i)): if
every zero of height ≤ `H` is on the line, then at any admissible strip
anchor of height ≤ `H/2` that has some zero within unit horizontal distance,
the seat energy is at least `4/5 − 8·τ(H)`, `τ(H)` the tail of the compiled
counting series.  The single hypothesis `hnear` — a zero near every height —
is the Riemann–von Mangoldt lower density, the one analytic input separating
this from an unconditional band positivity at half height. -/
theorem seat_energy_ge_floor_of_band_online {H : ℝ} (hH : 2 ≤ H)
    (hon : ∀ ρ ∈ ZD.NontrivialZeros, |ρ.im| ≤ H → ρ.re = 1 / 2)
    {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (hwim : w - (starRingEnd ℂ) w ≠ 0)
    (hre : |w.re| ≤ H / 2) (himw : |w.im| ≤ 1 / 2)
    {ρ₁ : ℂ} (hρ₁ : ρ₁ ∈ ZD.NontrivialZeros) (hρ₁h : |ρ₁.im| ≤ H)
    (hnear : |ρ₁.im - w.re| ≤ 1) :
    4 / 5 - 8 * (∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} // H < |ρ.val.im|},
        (ZD.xiOrderNat x.val.val : ℝ) / ‖x.val.val‖ ^ 2)
      ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          (ZD.xiOrderNat ρ.val : ℂ) *
            ((spectralCoord ρ.val - w)⁻¹ *
              (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re := by
  classical
  set f : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} → ℂ := fun ρ =>
    (ZD.xiOrderNat ρ.val : ℂ) *
      ((spectralCoord ρ.val - w)⁻¹ *
        (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹) with hf
  have hsumm : Summable f := summable_seat_energy hw hw' hwim
  set s : Set {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} := {ρ | H < |ρ.val.im|} with hs
  have hsum_s : Summable fun x : s => f x.val := hsumm.subtype _
  have hsum_sc : Summable fun x : ↑sᶜ => f x.val := hsumm.subtype _
  have hsplit : (∑' x : s, f x.val) + (∑' x : ↑sᶜ, f x.val) = ∑' x, f x :=
    hsum_s.tsum_add_tsum_compl hsum_sc
  -- each below-band term is real nonnegative, since its zero is on-line
  have hbelow_term : ∀ x : ↑sᶜ,
      f x.val = ((ZD.xiOrderNat x.val.val : ℝ) *
        (Complex.normSq (spectralCoord x.val.val - w))⁻¹ : ℝ) := by
    rintro ⟨ρ, hρc⟩
    have hband : |ρ.val.im| ≤ H := by
      have := hρc
      simp only [hs, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt] at this
      exact this
    have honρ : ρ.val.re = 1 / 2 := hon ρ.val ρ.2 hband
    have hreal : (starRingEnd ℂ) (spectralCoord ρ.val) = spectralCoord ρ.val :=
      spectralCoord_real_of_online honρ
    have hfac : spectralCoord ρ.val - (starRingEnd ℂ) w
        = (starRingEnd ℂ) (spectralCoord ρ.val - w) := by
      rw [map_sub, hreal]
    simp only [hf]
    rw [hfac, ← map_inv₀, Complex.mul_conj, Complex.normSq_inv]
    push_cast
    ring
  have hbelow_nonneg : ∀ x : ↑sᶜ, 0 ≤ (f x.val).re := by
    intro x
    rw [hbelow_term x, Complex.ofReal_re]
    exact mul_nonneg (Nat.cast_nonneg _)
      (inv_nonneg.mpr (Complex.normSq_nonneg _))
  -- the near zero sits below the band and its term is at least 4/5
  set P₁ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} := ⟨ρ₁, hρ₁⟩ with hP₁
  have hP₁mem : P₁ ∈ sᶜ := by
    simp only [hs, Set.mem_compl_iff, Set.mem_setOf_eq, not_lt, hP₁]
    exact hρ₁h
  have hterm₁ : 4 / 5 ≤ (f P₁).re := by
    have honρ₁ : ρ₁.re = 1 / 2 := hon ρ₁ hρ₁ hρ₁h
    have hns : Complex.normSq (spectralCoord ρ₁ - w) ≤ 5 / 4 := by
      have hre₁ : (spectralCoord ρ₁ - w).re = ρ₁.im - w.re := by
        rw [Complex.sub_re, spectralCoord_re]
      have him₁ : |(spectralCoord ρ₁ - w).im| ≤ 1 / 2 := by
        rw [Complex.sub_im]
        have : (spectralCoord ρ₁).im = 0 := by
          have := spectralCoord_real_of_online honρ₁
          rw [Complex.conj_eq_iff_im] at this
          exact this
        rw [this, zero_sub, abs_neg]
        exact himw
      rw [Complex.normSq_apply]
      have h1 : (spectralCoord ρ₁ - w).re ^ 2 ≤ 1 := by
        rw [hre₁]
        nlinarith [hnear, sq_abs (ρ₁.im - w.re), abs_nonneg (ρ₁.im - w.re)]
      have h2 : (spectralCoord ρ₁ - w).im ^ 2 ≤ 1 / 4 := by
        nlinarith [him₁, sq_abs (spectralCoord ρ₁ - w).im,
          abs_nonneg (spectralCoord ρ₁ - w).im]
      nlinarith [h1, h2]
    have hnspos : 0 < Complex.normSq (spectralCoord ρ₁ - w) := by
      rw [Complex.normSq_pos]
      rw [sub_ne_zero]
      intro h
      have := spectral_sub_ne hw P₁
      rw [hP₁] at this
      exact this (by rw [← h]; ring)
    have hm₁ : (1:ℝ) ≤ (ZD.xiOrderNat ρ₁ : ℝ) := by
      exact_mod_cast ZD.xiOrderNat_pos_of_mem_NontrivialZeros hρ₁
    have hb : (4:ℝ) / 5 ≤ (Complex.normSq (spectralCoord ρ₁ - w))⁻¹ := by
      rw [show (4:ℝ)/5 = (5/4 : ℝ)⁻¹ by norm_num]
      rw [← one_div, ← one_div]
      exact one_div_le_one_div_of_le hnspos hns
    have := hbelow_term ⟨P₁, hP₁mem⟩
    rw [this, Complex.ofReal_re]
    calc (4:ℝ)/5 ≤ (Complex.normSq (spectralCoord ρ₁ - w))⁻¹ := hb
      _ ≤ (ZD.xiOrderNat ρ₁ : ℝ) * (Complex.normSq (spectralCoord ρ₁ - w))⁻¹ := by
          nlinarith [hb, hm₁]
  -- below-band sum dominates the single near term
  have hbelow_ge : 4 / 5 ≤ (∑' x : ↑sᶜ, f x.val).re := by
    have hre_summ : Summable fun x : ↑sᶜ => (f x.val).re :=
      (Complex.hasSum_re hsum_sc.hasSum).summable
    rw [Complex.re_tsum hsum_sc]
    calc (4:ℝ)/5 ≤ (f P₁).re := hterm₁
      _ ≤ ∑' x : ↑sᶜ, (f x.val).re :=
          hre_summ.le_tsum ⟨P₁, hP₁mem⟩ fun j _ => hbelow_nonneg j
  -- above-band sum is bounded by the tail
  have habove : -(8 * (∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} // H < |ρ.val.im|},
      (ZD.xiOrderNat x.val.val : ℝ) / ‖x.val.val‖ ^ 2)) ≤ (∑' x : s, f x.val).re := by
    have h1 : |(∑' x : s, f x.val).re| ≤ ‖∑' x : s, f x.val‖ :=
      Complex.abs_re_le_norm _
    have h2 := seat_tail_tsum_le (w := w) hH hre
    have h3 : ‖∑' x : s, f x.val‖
        ≤ 8 * (∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} // H < |ρ.val.im|},
          (ZD.xiOrderNat x.val.val : ℝ) / ‖x.val.val‖ ^ 2) := h2
    have := abs_le.mp (le_trans h1 h3)
    linarith [this.1]
  have htot : (∑' x, f x).re = (∑' x : s, f x.val).re + (∑' x : ↑sᶜ, f x.val).re := by
    rw [← hsplit, Complex.add_re]
  rw [htot]
  linarith [hbelow_ge, habove]

/-- Anchors outside the closed strip have chart points off the zero set. -/
theorem chart_not_zero_of_outside {w : ℂ} (h : 1 / 2 < |w.im|) :
    (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros := by
  intro hmem
  have hre : (1 / 2 + Complex.I * w : ℂ).re = 1 / 2 - w.im := by
    simp [Complex.add_re, Complex.mul_re]
    ring
  have h1 := hmem.1
  have h2 := hmem.2.1
  rw [hre] at h1 h2
  rcases lt_or_ge w.im 0 with hneg | hpos
  · have : 1 / 2 < -w.im := by
      rwa [abs_of_neg hneg] at h
    linarith
  · have : 1 / 2 < w.im := by
      rwa [abs_of_nonneg hpos] at h
    linarith

/-- **Unconditional seat positivity outside the closed strip**: for every
anchor with `|Im w| > ½` — chart abscissa outside `[0,1]` — every individual
seat term has nonnegative real part: `(z₁z₂).re = (Im ρ − Re w)² + (Im w)² −
(½−β)² > 0` by the strip bound alone.  The criterion's open content is
thereby exactly the closed strip; no hypothesis and no pairing is needed
outside it. -/
theorem seat_energy_nonneg_of_outside_strip {w : ℂ} (hstrip : 1 / 2 < |w.im|) :
    0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re := by
  have hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros :=
    chart_not_zero_of_outside hstrip
  have hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros := by
    apply chart_not_zero_of_outside
    rw [Complex.conj_im, abs_neg]
    exact hstrip
  have him : w - (starRingEnd ℂ) w ≠ 0 := by
    intro h
    have h2 : (w - (starRingEnd ℂ) w).im = 0 := by rw [h]; simp
    rw [Complex.sub_im, Complex.conj_im] at h2
    have : w.im = 0 := by linarith
    rw [this] at hstrip
    simp at hstrip
    linarith
  have hsumm := summable_seat_energy hw hw' him
  rw [Complex.re_tsum hsumm]
  refine tsum_nonneg fun ρ => ?_
  have hprod : (spectralCoord ρ.val - w)⁻¹ *
      (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹
      = ((spectralCoord ρ.val - w) * (spectralCoord ρ.val - (starRingEnd ℂ) w))⁻¹ := by
    rw [mul_inv]
  have hre_prod : (0:ℝ) ≤
      ((spectralCoord ρ.val - w) * (spectralCoord ρ.val - (starRingEnd ℂ) w)).re := by
    rw [Complex.mul_re]
    have hz1re : (spectralCoord ρ.val - w).re = ρ.val.im - w.re := by
      rw [Complex.sub_re, spectralCoord_re]
    have hz2re : (spectralCoord ρ.val - (starRingEnd ℂ) w).re = ρ.val.im - w.re := by
      rw [Complex.sub_re, spectralCoord_re, Complex.conj_re]
    have hz1im : (spectralCoord ρ.val - w).im = (1/2 - ρ.val.re) - w.im := by
      rw [Complex.sub_im]
      congr 1
      unfold spectralCoord
      simp [Complex.mul_im]
    have hz2im : (spectralCoord ρ.val - (starRingEnd ℂ) w).im
        = (1/2 - ρ.val.re) + w.im := by
      rw [Complex.sub_im, Complex.conj_im]
      have : (spectralCoord ρ.val).im = 1/2 - ρ.val.re := by
        unfold spectralCoord
        simp [Complex.mul_im]
      rw [this]
      ring
    rw [hz1re, hz2re, hz1im, hz2im]
    have hβ : |1/2 - ρ.val.re| < 1/2 := by
      have h1 := ρ.2.1
      have h2 := ρ.2.2.1
      rw [abs_lt]
      constructor <;> linarith
    nlinarith [sq_nonneg (ρ.val.im - w.re), sq_abs (1/2 - ρ.val.re),
      sq_abs w.im, abs_nonneg (1/2 - ρ.val.re), abs_nonneg w.im,
      mul_self_le_mul_self (abs_nonneg (1/2 - ρ.val.re)) hβ.le,
      mul_self_lt_mul_self (by norm_num : (0:ℝ) ≤ 1/2) hstrip]
  rw [hprod, Complex.mul_re]
  simp only [Complex.natCast_re, Complex.natCast_im, Complex.inv_re,
    Complex.inv_im]
  have hns : (0:ℝ) ≤ Complex.normSq ((spectralCoord ρ.val - w) *
      (spectralCoord ρ.val - (starRingEnd ℂ) w)) := Complex.normSq_nonneg _
  have hdivpos : (0:ℝ) ≤ ((spectralCoord ρ.val - w) *
      (spectralCoord ρ.val - (starRingEnd ℂ) w)).re /
      Complex.normSq ((spectralCoord ρ.val - w) *
        (spectralCoord ρ.val - (starRingEnd ℂ) w)) :=
    div_nonneg hre_prod hns
  have hm : (0:ℝ) ≤ (ZD.xiOrderNat ρ.val : ℝ) := Nat.cast_nonneg _
  nlinarith [hdivpos, hm]

/-- **The band-local seat criterion** (`prop:bandlocal` (ii) of `hp_pencil`,
compiled): seat-energy positivity at anchors of height at most `H` forces
every zero of height at most `H` onto the critical line.  The witness anchor
of the converse sits exactly at the off-line zero's ordinate, so the
criterion is height-local with no boundary loss in this direction. -/
theorem zeros_online_of_band_nonneg {H : ℝ}
    (hpos : ∀ w : ℂ, |w.re| ≤ H →
      ((1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros) →
      ((1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros) →
      (w - (starRingEnd ℂ) w ≠ 0) →
      0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          (ZD.xiOrderNat ρ.val : ℂ) *
            ((spectralCoord ρ.val - w)⁻¹ *
              (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re) :
    ∀ ρ ∈ ZD.NontrivialZeros, |ρ.im| ≤ H → ρ.re = 1 / 2 := by
  intro ρ hρ hband
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmem' := CriticalLinePhasor.FoliatedGlobalPolarization.feReflect_mem hρ
    have hre' : 1 / 2 <
        (CriticalLinePhasor.FoliatedPolarization.feReflect ρ).re := by
      have : (CriticalLinePhasor.FoliatedPolarization.feReflect ρ).re
          = 1 - ρ.re := by
        simp [CriticalLinePhasor.FoliatedPolarization.feReflect,
          Complex.sub_re, Complex.conj_re]
      rw [this]
      linarith
    have him' : (CriticalLinePhasor.FoliatedPolarization.feReflect ρ).im = ρ.im := by
      simp [CriticalLinePhasor.FoliatedPolarization.feReflect,
        Complex.sub_im, Complex.conj_im]
    obtain ⟨w, hwre, _, h1, h2, h3, h4⟩ :=
      exists_seat_energy_neg hmem' hre' 1 one_pos
    have hwband : |w.re| ≤ H := by rw [hwre, him']; exact hband
    exact absurd (hpos w hwband h1 h2 h3) (not_le.mpr h4)
  · obtain ⟨w, hwre, _, h1, h2, h3, h4⟩ :=
      exists_seat_energy_neg hρ hgt 1 one_pos
    have hwband : |w.re| ≤ H := by rw [hwre]; exact hband
    exact absurd (hpos w hwband h1 h2 h3) (not_le.mpr h4)

/-! ## The depth ladder

A zero can contribute negatively only at anchors strictly shallower than
itself: the term's product has real part
`(Im ρ − Re w)² + (Im w)² − (β−½)²`.  Stratifying the criterion by the depth
`d` interpolates between the proven exterior rung (`d = ½`,
`seat_energy_nonneg_of_outside_strip`) and RH (`d = 0`,
`seat_criterion_iff`). -/

/-- Zeros no deeper than the anchor contribute nonnegatively — exact. -/
theorem seat_term_nonneg_of_shallow {w : ℂ}
    (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros})
    (hsh : |ρ.val.re - 1 / 2| ≤ |w.im|) :
    0 ≤ ((ZD.xiOrderNat ρ.val : ℂ) *
        ((spectralCoord ρ.val - w)⁻¹ *
          (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re := by
  have hprod : (spectralCoord ρ.val - w)⁻¹ *
      (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹
      = ((spectralCoord ρ.val - w) *
          (spectralCoord ρ.val - (starRingEnd ℂ) w))⁻¹ := by
    rw [mul_inv]
  have hre_prod : (0:ℝ) ≤
      ((spectralCoord ρ.val - w) *
        (spectralCoord ρ.val - (starRingEnd ℂ) w)).re := by
    rw [Complex.mul_re]
    have hz1re : (spectralCoord ρ.val - w).re = ρ.val.im - w.re := by
      rw [Complex.sub_re, spectralCoord_re]
    have hz2re : (spectralCoord ρ.val - (starRingEnd ℂ) w).re
        = ρ.val.im - w.re := by
      rw [Complex.sub_re, spectralCoord_re, Complex.conj_re]
    have hsc_im : (spectralCoord ρ.val).im = 1 / 2 - ρ.val.re := by
      unfold spectralCoord
      simp [Complex.mul_im]
    have hz1im : (spectralCoord ρ.val - w).im = (1 / 2 - ρ.val.re) - w.im := by
      rw [Complex.sub_im, hsc_im]
    have hz2im : (spectralCoord ρ.val - (starRingEnd ℂ) w).im
        = (1 / 2 - ρ.val.re) + w.im := by
      rw [Complex.sub_im, Complex.conj_im, hsc_im]
      ring
    rw [hz1re, hz2re, hz1im, hz2im]
    have habs : |1 / 2 - ρ.val.re| ≤ |w.im| := by
      rw [abs_sub_comm]
      exact hsh
    nlinarith [sq_nonneg (ρ.val.im - w.re), sq_abs (1 / 2 - ρ.val.re),
      sq_abs w.im, mul_self_le_mul_self (abs_nonneg (1 / 2 - ρ.val.re)) habs]
  rw [hprod, Complex.mul_re]
  simp only [Complex.natCast_re, Complex.natCast_im, Complex.inv_re,
    Complex.inv_im]
  have hns := Complex.normSq_nonneg ((spectralCoord ρ.val - w) *
      (spectralCoord ρ.val - (starRingEnd ℂ) w))
  have hdivpos := div_nonneg hre_prod hns
  have hm : (0:ℝ) ≤ (ZD.xiOrderNat ρ.val : ℝ) := Nat.cast_nonneg _
  nlinarith [hdivpos, hm]

/-- **The ladder's forward rungs**: if every zero has depth at most `d`, the
seat energy is nonnegative at every admissible anchor of depth at least
`d`. -/
theorem seat_energy_nonneg_of_depth {d : ℝ}
    (hd : ∀ ρ ∈ ZD.NontrivialZeros, |ρ.re - 1 / 2| ≤ d)
    {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (him : w - (starRingEnd ℂ) w ≠ 0)
    (hdepth : d ≤ |w.im|) :
    0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re := by
  have hsumm := summable_seat_energy hw hw' him
  rw [Complex.re_tsum hsumm]
  refine tsum_nonneg fun ρ => ?_
  exact seat_term_nonneg_of_shallow ρ (le_trans (hd ρ.val ρ.2) hdepth)

/-- **The depth-quantified criterion**: for every `d ≥ 0`, confinement of the
zeros to depth `d` is *equivalent* to seat positivity at all admissible
anchors of depth at least `d`.  At `d = ½` the left side is the strip bound
(true) and the right side is the proven exterior positivity; at `d = 0` the
statement is `seat_criterion_iff`, i.e. RH.  The ladder is the compiled
interpolation between the proven and the open endpoint. -/
theorem depth_criterion_iff {d : ℝ} (hd0 : 0 ≤ d) :
    (∀ ρ ∈ ZD.NontrivialZeros, |ρ.re - 1 / 2| ≤ d)
      ↔ ∀ w : ℂ, d ≤ |w.im| →
          ((1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros) →
          ((1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros) →
          (w - (starRingEnd ℂ) w ≠ 0) →
          0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
              (ZD.xiOrderNat ρ.val : ℂ) *
                ((spectralCoord ρ.val - w)⁻¹ *
                  (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re := by
  constructor
  · intro hconf w hdepth hw hw' him
    exact seat_energy_nonneg_of_depth hconf hw hw' him hdepth
  · intro hpos ρ hρ
    by_contra hdeep
    push_neg at hdeep
    rcases le_or_gt ρ.re (1 / 2) with hside | hside
    · -- reflect to the right side; depth is preserved
      have hmem' := CriticalLinePhasor.FoliatedGlobalPolarization.feReflect_mem hρ
      have hre' : 1 / 2 <
          (CriticalLinePhasor.FoliatedPolarization.feReflect ρ).re := by
        have hval : (CriticalLinePhasor.FoliatedPolarization.feReflect ρ).re
            = 1 - ρ.re := by
          simp [CriticalLinePhasor.FoliatedPolarization.feReflect,
            Complex.sub_re, Complex.conj_re]
        rw [hval]
        have : |ρ.re - 1 / 2| = 1 / 2 - ρ.re := by
          rw [abs_of_nonpos (by linarith)]
          ring
        rw [this] at hdeep
        linarith
      have hδd : d < (CriticalLinePhasor.FoliatedPolarization.feReflect ρ).re
          - 1 / 2 := by
        have hval : (CriticalLinePhasor.FoliatedPolarization.feReflect ρ).re
            = 1 - ρ.re := by
          simp [CriticalLinePhasor.FoliatedPolarization.feReflect,
            Complex.sub_re, Complex.conj_re]
        have : |ρ.re - 1 / 2| = 1 / 2 - ρ.re := by
          rw [abs_of_nonpos (by linarith)]
          ring
        rw [hval]
        rw [this] at hdeep
        linarith
      obtain ⟨w, _, hwdepth, h1, h2, h3, h4⟩ :=
        exists_seat_energy_neg hmem' hre'
          ((CriticalLinePhasor.FoliatedPolarization.feReflect ρ).re - 1 / 2 - d)
          (by linarith)
      have hwd : d ≤ |w.im| := by linarith [hwdepth]
      exact absurd (hpos w hwd h1 h2 h3) (not_le.mpr h4)
    · have hδd : d < ρ.re - 1 / 2 := by
        have : |ρ.re - 1 / 2| = ρ.re - 1 / 2 := by
          rw [abs_of_pos (by linarith)]
        rw [this] at hdeep
        linarith
      obtain ⟨w, _, hwdepth, h1, h2, h3, h4⟩ :=
        exists_seat_energy_neg hρ hside (ρ.re - 1 / 2 - d) (by linarith)
      have hwd : d ≤ |w.im| := by linarith [hwdepth]
      exact absurd (hpos w hwd h1 h2 h3) (not_le.mpr h4)

/-! ## The local-resonance law

Sharpening the shallow-term positivity: a term can be negative only if its
zero is BOTH deeper than the anchor AND within the open horizontal window
`|Im ρ − Re w| < ½` — because otherwise `a² ≥ ¼ > (β−½)²` by the strip
bound.  Hence the seat energy dominates its finite window sum: the sign at
any anchor is decided by finitely many deep near zeros.  This is
`rem:crossings` of `hp_pencil` ("crossings are local resonances"), exact and
compiled. -/

/-- Terms of zeros outside the unit horizontal window are nonnegative,
unconditionally: the strip bound gives `a² ≥ ¼ > (β−½)²`. -/
theorem seat_term_nonneg_of_far {w : ℂ}
    (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros})
    (hfar : 1 / 2 ≤ |ρ.val.im - w.re|) :
    0 ≤ ((ZD.xiOrderNat ρ.val : ℂ) *
        ((spectralCoord ρ.val - w)⁻¹ *
          (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re := by
  have hprod : (spectralCoord ρ.val - w)⁻¹ *
      (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹
      = ((spectralCoord ρ.val - w) *
          (spectralCoord ρ.val - (starRingEnd ℂ) w))⁻¹ := by
    rw [mul_inv]
  have hre_prod : (0:ℝ) ≤
      ((spectralCoord ρ.val - w) *
        (spectralCoord ρ.val - (starRingEnd ℂ) w)).re := by
    rw [Complex.mul_re]
    have hz1re : (spectralCoord ρ.val - w).re = ρ.val.im - w.re := by
      rw [Complex.sub_re, spectralCoord_re]
    have hz2re : (spectralCoord ρ.val - (starRingEnd ℂ) w).re
        = ρ.val.im - w.re := by
      rw [Complex.sub_re, spectralCoord_re, Complex.conj_re]
    have hsc_im : (spectralCoord ρ.val).im = 1 / 2 - ρ.val.re := by
      unfold spectralCoord
      simp [Complex.mul_im]
    have hz1im : (spectralCoord ρ.val - w).im = (1 / 2 - ρ.val.re) - w.im := by
      rw [Complex.sub_im, hsc_im]
    have hz2im : (spectralCoord ρ.val - (starRingEnd ℂ) w).im
        = (1 / 2 - ρ.val.re) + w.im := by
      rw [Complex.sub_im, Complex.conj_im, hsc_im]
      ring
    rw [hz1re, hz2re, hz1im, hz2im]
    have hβ : |1 / 2 - ρ.val.re| < 1 / 2 := by
      have h1 := ρ.2.1
      have h2 := ρ.2.2.1
      rw [abs_lt]
      constructor <;> linarith
    nlinarith [sq_abs (ρ.val.im - w.re), sq_abs (1 / 2 - ρ.val.re),
      mul_self_le_mul_self (by norm_num : (0:ℝ) ≤ 1/2) hfar,
      mul_self_lt_mul_self (abs_nonneg (1 / 2 - ρ.val.re)) hβ,
      sq_nonneg w.im]
  rw [hprod, Complex.mul_re]
  simp only [Complex.natCast_re, Complex.natCast_im, Complex.inv_re,
    Complex.inv_im]
  have hns := Complex.normSq_nonneg ((spectralCoord ρ.val - w) *
      (spectralCoord ρ.val - (starRingEnd ℂ) w))
  have hdivpos := div_nonneg hre_prod hns
  have hm : (0:ℝ) ≤ (ZD.xiOrderNat ρ.val : ℝ) := Nat.cast_nonneg _
  nlinarith [hdivpos, hm]

/-- **The local-resonance law, compiled**: the seat energy dominates the sum
over its window — the zeros that are both within horizontal distance `½` of
the anchor height and deeper than the anchor.  Every other term is
nonnegative.  Negativity anywhere therefore requires a deep zero within the
unit window: crossings are local resonances. -/
theorem seat_energy_ge_window {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (him : w - (starRingEnd ℂ) w ≠ 0) :
    (∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
        |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|},
      (ZD.xiOrderNat x.val.val : ℂ) *
        ((spectralCoord x.val.val - w)⁻¹ *
          (spectralCoord x.val.val - (starRingEnd ℂ) w)⁻¹)).re
      ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
          (ZD.xiOrderNat ρ.val : ℂ) *
            ((spectralCoord ρ.val - w)⁻¹ *
              (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re := by
  classical
  set f : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} → ℂ := fun ρ =>
    (ZD.xiOrderNat ρ.val : ℂ) *
      ((spectralCoord ρ.val - w)⁻¹ *
        (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹) with hf
  have hsumm : Summable f := summable_seat_energy hw hw' him
  set s : Set {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} :=
    {ρ | |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|} with hs
  have hsum_s : Summable fun x : s => f x.val := hsumm.subtype _
  have hsum_sc : Summable fun x : ↑sᶜ => f x.val := hsumm.subtype _
  have hsplit : (∑' x : s, f x.val) + (∑' x : ↑sᶜ, f x.val) = ∑' x, f x :=
    hsum_s.tsum_add_tsum_compl hsum_sc
  have hcompl_nonneg : 0 ≤ (∑' x : ↑sᶜ, f x.val).re := by
    rw [Complex.re_tsum hsum_sc]
    refine tsum_nonneg fun x => ?_
    have hx := x.2
    simp only [hs, Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or, not_lt] at hx
    rcases hx with hfar | hshallow
    · exact seat_term_nonneg_of_far x.val hfar
    · exact seat_term_nonneg_of_shallow x.val (by
        rw [abs_sub_comm] at hshallow ⊢
        exact hshallow)
  have htot : (∑' x, f x).re
      = (∑' x : s, f x.val).re + (∑' x : ↑sᶜ, f x.val).re := by
    rw [← hsplit, Complex.add_re]
  have hconv : (∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
        |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|},
      (ZD.xiOrderNat x.val.val : ℂ) *
        ((spectralCoord x.val.val - w)⁻¹ *
          (spectralCoord x.val.val - (starRingEnd ℂ) w)⁻¹))
      = ∑' x : s, f x.val := rfl
  rw [hconv, htot]
  linarith [hcompl_nonneg]

end CriticalLinePhasor.SeatScalar

section AxiomAudit
#print axioms CriticalLinePhasor.SeatScalar.chart_conj_anchor
#print axioms CriticalLinePhasor.SeatScalar.summable_seat_energy
#print axioms CriticalLinePhasor.SeatScalar.seat_energy_identity
#print axioms CriticalLinePhasor.SeatScalar.seat_energy_nonneg_of_online
#print axioms CriticalLinePhasor.SeatScalar.seat_term_vertical
#print axioms CriticalLinePhasor.SeatScalar.seat_term_vertical_neg
#print axioms CriticalLinePhasor.SeatScalar.seat_term_vertical_partner
#print axioms CriticalLinePhasor.SeatScalar.seat_term_far_bound
#print axioms CriticalLinePhasor.SeatScalar.exists_clearance
#print axioms CriticalLinePhasor.SeatScalar.exists_seat_energy_neg
#print axioms CriticalLinePhasor.SeatScalar.seat_criterion_iff
#print axioms CriticalLinePhasor.SeatScalar.zeros_online_of_band_nonneg
#print axioms CriticalLinePhasor.SeatScalar.seat_tail_norm_le
#print axioms CriticalLinePhasor.SeatScalar.seat_tail_tsum_le
#print axioms CriticalLinePhasor.SeatScalar.seat_energy_ge_floor_of_band_online
#print axioms CriticalLinePhasor.SeatScalar.seat_energy_nonneg_of_outside_strip
#print axioms CriticalLinePhasor.SeatScalar.seat_term_nonneg_of_shallow
#print axioms CriticalLinePhasor.SeatScalar.seat_energy_nonneg_of_depth
#print axioms CriticalLinePhasor.SeatScalar.depth_criterion_iff
#print axioms CriticalLinePhasor.SeatScalar.seat_term_nonneg_of_far
#print axioms CriticalLinePhasor.SeatScalar.seat_energy_ge_window
end AxiomAudit
