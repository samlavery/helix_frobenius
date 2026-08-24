import RequestProject.FoliatedPolarization
import RequestProject.SeatScalarCriterion

/-!
# The resonance geometry of the seat term (conjunct-2 opening brick)

The seat energy's per-zero term at anchor `w` is, in exact closed form,
`[(γ − Re w)² + (Im w)² − (β − ½)²] / |·|²` for a zero `ρ = β + iγ` — so a
zero threatens negativity EXACTLY on the open disk of radius `|β − ½|`
centered at `(γ, 0)` in the anchor plane.  An on-line zero has an empty
threat disk; the shallow channel is the union of the hypothetical threat
disks.  "Crossings are local resonances", now with the resonance region
computed exactly.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.DVP

open CriticalLinePhasor.FoliatedPolarization

/-- Components of the spectral coordinate. -/
theorem spectralCoord_re (ρ : ℂ) : (spectralCoord ρ).re = ρ.im := by
  rw [spectralCoord]
  simp

theorem spectralCoord_im (ρ : ℂ) : (spectralCoord ρ).im = 1/2 - ρ.re := by
  rw [spectralCoord]
  simp

/-- **The exact seat-term real part.**  For any `ρ` and anchor `w` (with the
two factors nonzero),
`Re[(t_ρ − w)⁻¹ (t_ρ − w̄)⁻¹]
   = [(γ − Re w)² + (Im w)² − (β − ½)²] / |(t_ρ − w)(t_ρ − w̄)|²`. -/
theorem seat_term_re_eq (ρ w : ℂ)
    (h1 : spectralCoord ρ - w ≠ 0)
    (h2 : spectralCoord ρ - (starRingEnd ℂ) w ≠ 0) :
    ((spectralCoord ρ - w)⁻¹ * (spectralCoord ρ - (starRingEnd ℂ) w)⁻¹).re
      = ((ρ.im - w.re)^2 + w.im^2 - (ρ.re - 1/2)^2)
        / Complex.normSq ((spectralCoord ρ - w)
            * (spectralCoord ρ - (starRingEnd ℂ) w)) := by
  rw [← mul_inv, Complex.inv_re]
  congr 1
  -- the numerator: Re of the product
  have ha : (spectralCoord ρ - w).re = ρ.im - w.re := by
    rw [Complex.sub_re, spectralCoord_re]
  have hb : (spectralCoord ρ - w).im = 1/2 - ρ.re - w.im := by
    rw [Complex.sub_im, spectralCoord_im]
  have hc : (spectralCoord ρ - (starRingEnd ℂ) w).re = ρ.im - w.re := by
    rw [Complex.sub_re, spectralCoord_re, Complex.conj_re]
  have hd : (spectralCoord ρ - (starRingEnd ℂ) w).im
      = 1/2 - ρ.re + w.im := by
    rw [Complex.sub_im, spectralCoord_im, Complex.conj_im]
    ring
  rw [Complex.mul_re, ha, hb, hc, hd]
  ring

/-- **The threat disk.**  The seat term is negative at `w` iff the anchor
lies strictly inside the disk of radius `|β − ½|` centered at `(γ, 0)`:
`(γ − Re w)² + (Im w)² < (β − ½)²`.  On-line zeros (`β = ½`) threaten
nothing; a hypothetical off-line zero threatens exactly a disk whose radius
is its depth. -/
theorem seat_term_neg_iff (ρ w : ℂ)
    (h1 : spectralCoord ρ - w ≠ 0)
    (h2 : spectralCoord ρ - (starRingEnd ℂ) w ≠ 0) :
    ((spectralCoord ρ - w)⁻¹ * (spectralCoord ρ - (starRingEnd ℂ) w)⁻¹).re < 0
      ↔ (ρ.im - w.re)^2 + w.im^2 < (ρ.re - 1/2)^2 := by
  rw [seat_term_re_eq ρ w h1 h2]
  have hprod : (spectralCoord ρ - w)
      * (spectralCoord ρ - (starRingEnd ℂ) w) ≠ 0 := mul_ne_zero h1 h2
  have hden : 0 < Complex.normSq ((spectralCoord ρ - w)
      * (spectralCoord ρ - (starRingEnd ℂ) w)) := by
    rw [Complex.normSq_pos]
    exact hprod
  rw [div_neg_iff]
  constructor
  · rintro (⟨_, hdneg⟩ | ⟨hn, _⟩)
    · linarith
    · linarith
  · intro h
    right
    exact ⟨by linarith, hden⟩

/-- **On-line zeros have nonnegative terms, quantitatively**: for `β = ½`
the term equals `[(γ − Re w)² + (Im w)²]⁻¹ ≥ 0` — positivity with the
exact magnitude. -/
theorem seat_term_online_nonneg (ρ w : ℂ) (hρ : ρ.re = 1/2)
    (h1 : spectralCoord ρ - w ≠ 0)
    (h2 : spectralCoord ρ - (starRingEnd ℂ) w ≠ 0) :
    0 ≤ ((spectralCoord ρ - w)⁻¹
        * (spectralCoord ρ - (starRingEnd ℂ) w)⁻¹).re := by
  rw [seat_term_re_eq ρ w h1 h2, hρ]
  apply div_nonneg _ (Complex.normSq_nonneg _)
  nlinarith [sq_nonneg (ρ.im - w.re), sq_nonneg w.im]

/-- The seat-term denominator in closed form:
`|·|² = N² + 4A²B²` with `N` the numerator, `A = γ − Re w`, `B = β − ½`. -/
theorem seat_term_normSq_eq (ρ w : ℂ) :
    Complex.normSq ((spectralCoord ρ - w)
        * (spectralCoord ρ - (starRingEnd ℂ) w))
      = ((ρ.im - w.re)^2 + w.im^2 - (ρ.re - 1/2)^2)^2
        + 4 * (ρ.im - w.re)^2 * (ρ.re - 1/2)^2 := by
  have ha : (spectralCoord ρ - w).re = ρ.im - w.re := by
    rw [Complex.sub_re, spectralCoord_re]
  have hb : (spectralCoord ρ - w).im = 1/2 - ρ.re - w.im := by
    rw [Complex.sub_im, spectralCoord_im]
  have hc : (spectralCoord ρ - (starRingEnd ℂ) w).re = ρ.im - w.re := by
    rw [Complex.sub_re, spectralCoord_re, Complex.conj_re]
  have hd : (spectralCoord ρ - (starRingEnd ℂ) w).im
      = 1/2 - ρ.re + w.im := by
    rw [Complex.sub_im, spectralCoord_im, Complex.conj_im]
    ring
  rw [Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    ha, hb, hc, hd]
  ring

/-- **Negativity control I (off-height)**: every seat term is at least
`−1/(4·|γ − Re w|·|β − ½|)` — AM–GM on the exact denominator.  The only
blow-up channel is `Re w → γ`: anchors at the hypothetical zero's height. -/
theorem seat_term_lower_offheight (ρ w : ℂ)
    (hA : ρ.im ≠ w.re) (hB : ρ.re ≠ 1/2)
    (h1 : spectralCoord ρ - w ≠ 0)
    (h2 : spectralCoord ρ - (starRingEnd ℂ) w ≠ 0) :
    -(1/(4 * |ρ.im - w.re| * |ρ.re - 1/2|))
      ≤ ((spectralCoord ρ - w)⁻¹
          * (spectralCoord ρ - (starRingEnd ℂ) w)⁻¹).re := by
  set A : ℝ := ρ.im - w.re with hA'
  set B : ℝ := ρ.re - 1/2 with hB'
  have hA0 : A ≠ 0 := sub_ne_zero.mpr hA
  have hB0 : B ≠ 0 := sub_ne_zero.mpr hB
  have hAabs : 0 < |A| := abs_pos.mpr hA0
  have hBabs : 0 < |B| := abs_pos.mpr hB0
  rw [seat_term_re_eq ρ w h1 h2, seat_term_normSq_eq]
  set N : ℝ := A^2 + w.im^2 - B^2 with hN
  rcases le_or_gt 0 N with hpos | hneg
  · -- nonnegative numerator: the term is nonnegative
    have hterm : 0 ≤ N / (N^2 + 4*A^2*B^2) := by
      apply div_nonneg hpos
      positivity
    have hbound : (0:ℝ) < 1/(4 * |A| * |B|) := by positivity
    calc -(1/(4 * |A| * |B|)) ≤ 0 := by linarith
      _ ≤ N / (N^2 + 4*A^2*B^2) := hterm
  · -- negative numerator: AM–GM
    have hA2 : (0:ℝ) < A^2 := by
      nlinarith [mul_pos hAabs hAabs, sq_abs A]
    have hB2 : (0:ℝ) < B^2 := by
      nlinarith [mul_pos hBabs hBabs, sq_abs B]
    have hden : (0:ℝ) < N^2 + 4*A^2*B^2 := by
      nlinarith [sq_nonneg N, mul_pos hA2 hB2]
    rw [neg_le, ← neg_div]
    rw [div_le_div_iff₀ hden (by positivity : (0:ℝ) < 4 * |A| * |B|)]
    have hamgm : 2 * |N| * (2 * |A| * |B|) ≤ N^2 + 4*A^2*B^2 := by
      have h := sq_nonneg (|N| - 2 * |A| * |B|)
      have habs2 : |N|^2 = N^2 := sq_abs N
      have habsA : |A|^2 = A^2 := sq_abs A
      have habsB : |B|^2 = B^2 := sq_abs B
      nlinarith [habs2, habsA, habsB]
    have hNneg : |N| = -N := abs_of_neg hneg
    nlinarith [hamgm, hNneg, abs_nonneg N, hAabs, hBabs]

/-- **Negativity control II (interior)**: inside the threat disk the term is
at least `−1/(B² − A² − d²)` — the blow-up is confined to the disk
BOUNDARY. -/
theorem seat_term_lower_interior (ρ w : ℂ)
    (hin : (ρ.im - w.re)^2 + w.im^2 < (ρ.re - 1/2)^2)
    (h1 : spectralCoord ρ - w ≠ 0)
    (h2 : spectralCoord ρ - (starRingEnd ℂ) w ≠ 0) :
    -(1/((ρ.re - 1/2)^2 - (ρ.im - w.re)^2 - w.im^2))
      ≤ ((spectralCoord ρ - w)⁻¹
          * (spectralCoord ρ - (starRingEnd ℂ) w)⁻¹).re := by
  set A : ℝ := ρ.im - w.re with hA'
  set B : ℝ := ρ.re - 1/2 with hB'
  set X : ℝ := B^2 - A^2 - w.im^2 with hX
  have hX0 : 0 < X := by
    rw [hX]
    linarith
  rw [seat_term_re_eq ρ w h1 h2, seat_term_normSq_eq]
  have hnum : A^2 + w.im^2 - B^2 = -X := by
    rw [hX]
    ring
  rw [hnum]
  have hden : (0:ℝ) < (-X)^2 + 4*A^2*B^2 := by
    nlinarith [mul_pos hX0 hX0, sq_nonneg (A*B)]
  rw [neg_le, ← neg_div, neg_neg]
  rw [div_le_div_iff₀ hden hX0]
  have hXsq : X * X ≤ (-X)^2 + 4*A^2*B^2 := by
    nlinarith [sq_nonneg (A*B)]
  nlinarith [hXsq, hX0]

/-- **The FE-pair gives NO cancellation in the seat** — the partner's term
EQUALS the zero's own term (the resonance formula is even in the depth):
`term(1 − ρ̄, w) = term(ρ, w)`.  A deep zero's negativity is doubled by its
partner, never cancelled; the rescue at resonant anchors must be
inter-zero.  (Design law: the alley is closed by exact structure, not by
estimate.) -/
theorem seat_term_fe_pair_eq (ρ w : ℂ)
    (h1 : spectralCoord ρ - w ≠ 0)
    (h2 : spectralCoord ρ - (starRingEnd ℂ) w ≠ 0)
    (h1' : spectralCoord (1 - (starRingEnd ℂ) ρ) - w ≠ 0)
    (h2' : spectralCoord (1 - (starRingEnd ℂ) ρ) - (starRingEnd ℂ) w ≠ 0) :
    ((spectralCoord (1 - (starRingEnd ℂ) ρ) - w)⁻¹
        * (spectralCoord (1 - (starRingEnd ℂ) ρ) - (starRingEnd ℂ) w)⁻¹).re
      = ((spectralCoord ρ - w)⁻¹
        * (spectralCoord ρ - (starRingEnd ℂ) w)⁻¹).re := by
  rw [seat_term_re_eq _ w h1' h2', seat_term_re_eq _ w h1 h2,
    seat_term_normSq_eq, seat_term_normSq_eq]
  have hre : (1 - (starRingEnd ℂ) ρ).re = 1 - ρ.re := by
    simp
  have him : (1 - (starRingEnd ℂ) ρ).im = ρ.im := by
    simp
  rw [hre, him]
  have hsq : ((1 - ρ.re) - 1/2)^2 = (ρ.re - 1/2)^2 := by
    ring
  rw [hsq]

/-! ## The refined window law: keep a designated on-line population -/

open CriticalLinePhasor.SeatScalar

set_option maxHeartbeats 1600000

/-- **The refined local-resonance law**: the seat energy dominates a
designated finite ON-LINE population PLUS the deep window.  (On-line zeros
are automatically outside the deep window — their depth is zero — so the
three-way split is exact.) -/
theorem seat_energy_ge_online_plus_window {w : ℂ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (him : w - (starRingEnd ℂ) w ≠ 0)
    (W : Finset {ρ : ℂ // ρ ∈ ZD.NontrivialZeros})
    (hWon : ∀ ρ ∈ W, (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}).val.re = 1/2) :
    (∑ ρ ∈ W, ((ZD.xiOrderNat ρ.val : ℂ) *
        ((spectralCoord ρ.val - w)⁻¹ *
          (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re)
      + (∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
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
  set u : Set {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} := (↑W : Set _) ∪ s with hu
  -- W and s are disjoint: on-line zeros have zero depth
  have hdisj : Disjoint (↑W : Set _) s := by
    rw [Set.disjoint_left]
    intro ρ hρW hρs
    have hon := hWon ρ hρW
    rw [hs] at hρs
    have hdeep := hρs.2
    rw [hon] at hdeep
    simp at hdeep
    have := abs_nonneg w.im
    linarith
  have hsum_W : Summable fun x : (↑W : Set _) => f x.val := hsumm.subtype _
  have hsum_s : Summable fun x : s => f x.val := hsumm.subtype _
  have hsum_u : Summable fun x : u => f x.val := hsumm.subtype _
  have hsum_uc : Summable fun x : ↑uᶜ => f x.val := hsumm.subtype _
  -- total = u-part + complement
  have hsplit : (∑' x : u, f x.val) + (∑' x : ↑uᶜ, f x.val) = ∑' x, f x :=
    hsum_u.tsum_add_tsum_compl hsum_uc
  -- the complement is nonnegative (neither designated on-line nor deep)
  have hcompl_nonneg : 0 ≤ (∑' x : ↑uᶜ, f x.val).re := by
    rw [Complex.re_tsum hsum_uc]
    refine tsum_nonneg fun x => ?_
    have hx : (x : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) ∈ uᶜ := x.2
    have hxs : (x : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}) ∉ s := by
      intro hmem
      exact hx (Set.mem_union_right _ hmem)
    simp only [hs, Set.mem_setOf_eq, not_and_or, not_lt] at hxs
    rcases hxs with hfar | hshallow
    · exact seat_term_nonneg_of_far x.val hfar
    · exact seat_term_nonneg_of_shallow x.val (by
        rw [abs_sub_comm] at hshallow ⊢
        exact hshallow)
  -- the u-part splits into W and s
  have hu_split : (∑' x : u, f x.val)
      = (∑' x : (↑W : Set _), f x.val) + (∑' x : s, f x.val) := by
    rw [hu]
    exact Summable.tsum_union_disjoint hdisj hsum_W hsum_s
  have hW_eq : (∑' x : (↑W : Set _), f x.val) = ∑ ρ ∈ W, f ρ := by
    exact Finset.tsum_subtype W f
  -- assemble
  have htot : (∑' x, f x).re
      = (∑ ρ ∈ W, f ρ).re + (∑' x : s, f x.val).re
        + (∑' x : ↑uᶜ, f x.val).re := by
    rw [← hsplit, hu_split, hW_eq, Complex.add_re, Complex.add_re]
  have hWre : (∑ ρ ∈ W, f ρ).re = ∑ ρ ∈ W, (f ρ).re := by
    rw [Complex.re_sum]
  have hs_eq : (∑' x : s, f x.val)
      = ∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
          |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|},
        (ZD.xiOrderNat x.val.val : ℂ) *
          ((spectralCoord x.val.val - w)⁻¹ *
            (spectralCoord x.val.val - (starRingEnd ℂ) w)⁻¹) := rfl
  rw [show (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      (ZD.xiOrderNat ρ.val : ℂ) *
        ((spectralCoord ρ.val - w)⁻¹ *
          (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)) = ∑' x, f x from rfl,
    htot, ← hWre, ← hs_eq]
  linarith [hcompl_nonneg]

/-- **The on-line mass floor**: a designated on-line population within
horizontal distance `H` of the anchor contributes at least
`(Σ multiplicities)/(H² + d²)` — the compiled positive side of the
domination confrontation. -/
theorem online_mass_floor {w : ℂ} {H : ℝ} (hH : 0 < H)
    (W : Finset {ρ : ℂ // ρ ∈ ZD.NontrivialZeros})
    (hWon : ∀ ρ ∈ W, (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}).val.re = 1/2)
    (hWnear : ∀ ρ ∈ W,
      |(ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}).val.im - w.re| ≤ H)
    (hne : ∀ ρ ∈ W, spectralCoord
        (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}).val - w ≠ 0)
    (hne' : ∀ ρ ∈ W, spectralCoord
        (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}).val
          - (starRingEnd ℂ) w ≠ 0) :
    (∑ ρ ∈ W, (ZD.xiOrderNat ρ.val : ℝ)) / (H^2 + w.im^2)
      ≤ ∑ ρ ∈ W, ((ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re := by
  have hden : (0:ℝ) < H^2 + w.im^2 := by positivity
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro ρ hρ
  have hon := hWon ρ hρ
  have hnear := hWnear ρ hρ
  have h1 := hne ρ hρ
  have h2 := hne' ρ hρ
  have hterm_re : ((ZD.xiOrderNat ρ.val : ℂ) *
      ((spectralCoord ρ.val - w)⁻¹ *
        (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re
      = (ZD.xiOrderNat ρ.val : ℝ) *
        ((spectralCoord ρ.val - w)⁻¹ *
          (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹).re := by
    rw [show ((ZD.xiOrderNat ρ.val : ℕ) : ℂ) = (((ZD.xiOrderNat ρ.val : ℕ)
        : ℝ) : ℂ) from by push_cast; rfl,
      Complex.re_ofReal_mul]
  rw [hterm_re, seat_term_re_eq ρ.val w h1 h2, seat_term_normSq_eq, hon]
  have hzero : ((1:ℝ)/2 - 1/2)^2 = 0 := by norm_num
  have hA2 : (ρ.val.im - w.re)^2 ≤ H^2 := by
    have := sq_le_sq' (by linarith [abs_le.mp hnear] :
        -H ≤ ρ.val.im - w.re) (by linarith [abs_le.mp hnear])
    simpa using this
  have hm : (0:ℝ) ≤ (ZD.xiOrderNat ρ.val : ℝ) := Nat.cast_nonneg _
  simp only [hzero, mul_zero, add_zero, sub_zero]
  -- term = m·D/D² = m/D with D = A² + d² ≤ H² + d²
  set D : ℝ := (ρ.val.im - w.re)^2 + w.im^2 with hD
  rcases eq_or_lt_of_le (by positivity : (0:ℝ) ≤ D) with hD0 | hD0
  · -- D = 0 impossible: the factors were nonzero
    exfalso
    have hAz : ρ.val.im - w.re = 0 := by nlinarith [sq_nonneg (ρ.val.im - w.re), sq_nonneg w.im]
    have hIz : w.im = 0 := by nlinarith [sq_nonneg (ρ.val.im - w.re), sq_nonneg w.im]
    apply h1
    apply Complex.ext
    · rw [Complex.sub_re, spectralCoord_re, Complex.zero_re]
      linarith
    · rw [Complex.sub_im, spectralCoord_im, Complex.zero_im, hon, hIz]
      norm_num
  · have hstep : D / D^2 = 1/D := by
      field_simp
    rw [hstep]
    rw [div_eq_mul_one_div]
    apply mul_le_mul_of_nonneg_left _ hm
    apply one_div_le_one_div_of_le hD0
    rw [hD]
    linarith

/-- Per-term floor for a deep-window zero at a tube-avoiding anchor: the
term (with multiplicity) is at least `−m/(4δd)`.  Vanishing factors give a
zero term, which satisfies the bound vacuously. -/
theorem deep_term_floor {w : ℂ} {δ : ℝ} (hδ : 0 < δ) (hd : 0 < w.im)
    (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros})
    (hdeep : |w.im| < |ρ.val.re - 1/2|)
    (htube : δ ≤ |ρ.val.im - w.re|) :
    -((ZD.xiOrderNat ρ.val : ℝ)/(4*δ*w.im))
      ≤ ((ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re := by
  have hm : (0:ℝ) ≤ (ZD.xiOrderNat ρ.val : ℝ) := Nat.cast_nonneg _
  have hterm_re : ((ZD.xiOrderNat ρ.val : ℂ) *
      ((spectralCoord ρ.val - w)⁻¹ *
        (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re
      = (ZD.xiOrderNat ρ.val : ℝ) *
        ((spectralCoord ρ.val - w)⁻¹ *
          (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹).re := by
    rw [show ((ZD.xiOrderNat ρ.val : ℕ) : ℂ)
        = (((ZD.xiOrderNat ρ.val : ℕ) : ℝ) : ℂ) from by push_cast; rfl,
      Complex.re_ofReal_mul]
  rw [hterm_re]
  rcases eq_or_ne (spectralCoord ρ.val - w) 0 with h1 | h1
  · rw [h1]
    simp
    positivity
  rcases eq_or_ne (spectralCoord ρ.val - (starRingEnd ℂ) w) 0 with h2 | h2
  · rw [h2]
    simp
    positivity
  -- the genuine case: the off-height control
  have hA : ρ.val.im ≠ w.re := by
    intro hc
    rw [hc] at htube
    simp at htube
    linarith
  have hB : ρ.val.re ≠ 1/2 := by
    intro hc
    rw [hc] at hdeep
    simp at hdeep
    have := abs_nonneg w.im
    linarith
  have hlow := seat_term_lower_offheight ρ.val w hA hB h1 h2
  have hAabs : δ ≤ |ρ.val.im - w.re| := htube
  have hBabs : w.im ≤ |ρ.val.re - 1/2| := by
    have := hdeep
    rw [abs_of_pos hd] at this
    linarith
  have hfrac : (1:ℝ)/(4 * |ρ.val.im - w.re| * |ρ.val.re - 1/2|)
      ≤ 1/(4*δ*w.im) := by
    apply one_div_le_one_div_of_le (by positivity)
    have h4 : (0:ℝ) < 4 := by norm_num
    calc 4*δ*w.im ≤ 4*(|ρ.val.im - w.re|)*w.im := by
          have := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hAabs h4.le) hd.le
          linarith [this]
      _ ≤ 4*(|ρ.val.im - w.re|)*(|ρ.val.re - 1/2|) := by
          apply mul_le_mul_of_nonneg_left hBabs
          positivity
  calc -((ZD.xiOrderNat ρ.val : ℝ)/(4*δ*w.im))
      = (ZD.xiOrderNat ρ.val : ℝ) * (-(1/(4*δ*w.im))) := by ring
    _ ≤ (ZD.xiOrderNat ρ.val : ℝ)
        * (-(1/(4 * |ρ.val.im - w.re| * |ρ.val.re - 1/2|))) := by
        apply mul_le_mul_of_nonneg_left _ hm
        simp only [neg_le_neg_iff]
        exact hfrac
    _ ≤ (ZD.xiOrderNat ρ.val : ℝ)
        * ((spectralCoord ρ.val - w)⁻¹ *
          (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹).re :=
        mul_le_mul_of_nonneg_left hlow hm

set_option maxHeartbeats 1600000 in
/-- **THE CHANNEL OFF THE TUBES**: an admissible anchor (upper-half, in
anyone's channel) with a designated on-line mass `M` within `H`, whose deep
window avoids the anchor's height by `δ` and carries total multiplicity at
most `K`, has nonnegative seat energy as soon as
`K/(4δ·d) ≤ M/(H² + d²)`.  Conjunct (2) off the tubes is a BALANCE of
compiled quantities. -/
theorem seat_channel_off_tubes {w : ℂ} {H δ K M : ℝ}
    (hw : (1 / 2 + Complex.I * w) ∉ ZD.NontrivialZeros)
    (hw' : (1 / 2 + Complex.I * (starRingEnd ℂ) w) ∉ ZD.NontrivialZeros)
    (him : w - (starRingEnd ℂ) w ≠ 0)
    (hd : 0 < w.im) (hH : 0 < H) (hδ : 0 < δ)
    (W : Finset {ρ : ℂ // ρ ∈ ZD.NontrivialZeros})
    (hWon : ∀ ρ ∈ W, (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}).val.re = 1/2)
    (hWnear : ∀ ρ ∈ W,
      |(ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}).val.im - w.re| ≤ H)
    (hne : ∀ ρ ∈ W, spectralCoord
        (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}).val - w ≠ 0)
    (hne' : ∀ ρ ∈ W, spectralCoord
        (ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros}).val
          - (starRingEnd ℂ) w ≠ 0)
    (hM : M ≤ ∑ ρ ∈ W, (ZD.xiOrderNat ρ.val : ℝ))
    (htube : ∀ ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
      |ρ.val.im - w.re| < 1/2 → |w.im| < |ρ.val.re - 1/2| →
        δ ≤ |ρ.val.im - w.re|)
    (hsummult : Summable (fun x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
        |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|} =>
      (ZD.xiOrderNat x.val.val : ℝ)))
    (hK : (∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
        |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|},
      (ZD.xiOrderNat x.val.val : ℝ)) ≤ K)
    (hbal : K/(4*δ*w.im) ≤ M/(H^2 + w.im^2)) :
    0 ≤ (∑' ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros},
        (ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re := by
  have hrefined := seat_energy_ge_online_plus_window hw hw' him W hWon
  have hfloor := online_mass_floor hH W hWon hWnear hne hne'
  -- the deep window's floor
  have hdeep_sum : Summable (fun x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
      |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|} =>
    (ZD.xiOrderNat x.val.val : ℂ) *
      ((spectralCoord x.val.val - w)⁻¹ *
        (spectralCoord x.val.val - (starRingEnd ℂ) w)⁻¹)) :=
    (summable_seat_energy hw hw' him).subtype _
  have hdeep_floor : -(K/(4*δ*w.im))
      ≤ (∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
          |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|},
        (ZD.xiOrderNat x.val.val : ℂ) *
          ((spectralCoord x.val.val - w)⁻¹ *
            (spectralCoord x.val.val - (starRingEnd ℂ) w)⁻¹)).re := by
    rw [Complex.re_tsum hdeep_sum]
    have hterm : ∀ x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
        |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|},
        -((ZD.xiOrderNat x.val.val : ℝ)/(4*δ*w.im))
          ≤ ((ZD.xiOrderNat x.val.val : ℂ) *
            ((spectralCoord x.val.val - w)⁻¹ *
              (spectralCoord x.val.val - (starRingEnd ℂ) w)⁻¹)).re :=
      fun x => deep_term_floor hδ hd x.val x.2.2
        (htube x.val x.2.1 x.2.2)
    have hsum_re : Summable (fun x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
        |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|} =>
      ((ZD.xiOrderNat x.val.val : ℂ) *
        ((spectralCoord x.val.val - w)⁻¹ *
          (spectralCoord x.val.val - (starRingEnd ℂ) w)⁻¹)).re) :=
      (Complex.hasSum_re hdeep_sum.hasSum).summable
    calc -(K/(4*δ*w.im))
        ≤ -((∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
            |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|},
          (ZD.xiOrderNat x.val.val : ℝ))/(4*δ*w.im)) := by
          rw [neg_le_neg_iff]
          apply div_le_div_of_nonneg_right hK (by positivity)
      _ = ∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
            |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|},
          (-((ZD.xiOrderNat x.val.val : ℝ)/(4*δ*w.im))) := by
          rw [← tsum_div_const, ← tsum_neg]
      _ ≤ ∑' x : {ρ : {ρ : ℂ // ρ ∈ ZD.NontrivialZeros} //
            |ρ.val.im - w.re| < 1 / 2 ∧ |w.im| < |ρ.val.re - 1 / 2|},
          ((ZD.xiOrderNat x.val.val : ℂ) *
            ((spectralCoord x.val.val - w)⁻¹ *
              (spectralCoord x.val.val - (starRingEnd ℂ) w)⁻¹)).re := by
          apply Summable.tsum_le_tsum hterm _ hsum_re
          exact ((hsummult.div_const _).neg)
  -- balance
  have hmass : M/(H^2 + w.im^2)
      ≤ ∑ ρ ∈ W, ((ZD.xiOrderNat ρ.val : ℂ) *
          ((spectralCoord ρ.val - w)⁻¹ *
            (spectralCoord ρ.val - (starRingEnd ℂ) w)⁻¹)).re := by
    calc M/(H^2 + w.im^2)
        ≤ (∑ ρ ∈ W, (ZD.xiOrderNat ρ.val : ℝ))/(H^2 + w.im^2) := by
          apply div_le_div_of_nonneg_right hM (by positivity)
      _ ≤ _ := hfloor
  linarith [hrefined, hmass, hdeep_floor, hbal]

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.seat_term_re_eq
#print axioms CriticalLinePhasor.DVP.seat_term_neg_iff
#print axioms CriticalLinePhasor.DVP.seat_term_online_nonneg
#print axioms CriticalLinePhasor.DVP.seat_term_normSq_eq
#print axioms CriticalLinePhasor.DVP.seat_term_lower_offheight
#print axioms CriticalLinePhasor.DVP.seat_term_lower_interior
#print axioms CriticalLinePhasor.DVP.seat_energy_ge_online_plus_window
#print axioms CriticalLinePhasor.DVP.online_mass_floor
#print axioms CriticalLinePhasor.DVP.seat_term_fe_pair_eq
#print axioms CriticalLinePhasor.DVP.deep_term_floor
#print axioms CriticalLinePhasor.DVP.seat_channel_off_tubes
end AxiomAudit
