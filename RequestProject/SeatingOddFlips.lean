import RequestProject.SeatingDetector
import RequestProject.DVPWeightedCount
import Zeta23.Statement

/-!
# Odd multiplicity flips: the crossing survives any odd order

At an on-line zero of odd ζ-multiplicity `m`, the readout factors locally as
`XiLine (γ+h) = hᵐ·u h` with `u` continuous at `0` and `u 0 ≠ 0` — the
factorization unit is forced REAL on the line by the compiled reality of the
readout — so the sign still flips across the zero.  With this the
flip-invisible classes shrink to exactly: off-line zeros and EVEN-order
on-line zeros.

No `sorry`, no `axiom`.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.SeatingLedger

/-- **Odd order flips**: an on-line zero of odd multiplicity produces a sign
flip of the readout in every sufficiently small symmetric window. -/
theorem odd_mult_flips {γ : ℝ} (hγ : γ ≠ 0)
    (hmem : linePt γ ∈ ZD.NontrivialZeros)
    (hodd : Odd (Zeta23.zeroMult (linePt γ))) :
    ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε →
      XiLine (γ - δ) * XiLine (γ + δ) < 0 := by
  set m := Zeta23.zeroMult (linePt γ) with hm
  have him : (linePt γ).im ≠ 0 := by
    rw [linePt_im]
    exact hγ
  -- ξ-order = m
  have hζ : analyticOrderAt riemannZeta (linePt γ) = m := by
    have hne : analyticOrderAt riemannZeta (linePt γ) ≠ ⊤ := by
      intro htop
      have hz : m = 0 := by
        rw [hm]
        unfold Zeta23.zeroMult
        rw [htop]
        rfl
      rw [hz] at hodd
      simp [Nat.odd_iff] at hodd
    have hcoe := ENat.coe_toNat hne
    rw [hm]
    unfold Zeta23.zeroMult
    exact hcoe.symm
  have hξord : analyticOrderAt ZD.riemannXi (linePt γ) = m := by
    rw [CriticalLinePhasor.DVP.xi_order_eq_zeta_order him, hζ]
  have hDiff : Differentiable ℂ ZD.riemannXi := fun z => ZD.riemannXi_differentiable z
  have hA : AnalyticAt ℂ ZD.riemannXi (linePt γ) :=
    hDiff.differentiableOn.analyticAt
      (IsOpen.mem_nhds isOpen_univ (Set.mem_univ _))
  obtain ⟨g, hgA, hg0, hev⟩ := (hA.analyticOrderAt_eq_natCast).mp hξord
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨r, hr, hfac⟩ := hev
  -- the line moves at unit speed toward ρ
  have hline_sub : ∀ h : ℝ, linePt (γ + h) - linePt γ = (h : ℂ) * I := by
    intro h
    unfold linePt
    push_cast
    ring
  have hline_dist : ∀ h : ℝ, dist (linePt (γ + h)) (linePt γ) = |h| := by
    intro h
    rw [dist_eq_norm, hline_sub]
    simp [Complex.norm_mul]
  -- the real unit
  set u : ℝ → ℝ := fun h => (I^m * g (linePt (γ + h))).re with hu
  set v : ℝ → ℝ := fun h => (I^m * g (linePt (γ + h))).im with hv
  have hXi_eq : ∀ h : ℝ, |h| < r → XiLine (γ + h) = h^m * u h := by
    intro h hh
    have hfa := hfac (by rw [hline_dist]; exact hh)
    unfold XiLine
    rw [hfa, hline_sub, smul_eq_mul, mul_pow]
    have hre : (h:ℂ)^m * I^m * g (linePt (γ + h))
        = ((h^m : ℝ) : ℂ) * (I^m * g (linePt (γ + h))) := by
      push_cast
      ring
    rw [hre, Complex.re_ofReal_mul]
  have hXi_im : ∀ h : ℝ, |h| < r → 0 = h^m * v h := by
    intro h hh
    have hfa := hfac (by rw [hline_dist]; exact hh)
    have h0 := Xi_line_im (γ + h)
    rw [hfa, hline_sub, smul_eq_mul, mul_pow] at h0
    have hre : (h:ℂ)^m * I^m * g (linePt (γ + h))
        = ((h^m : ℝ) : ℂ) * (I^m * g (linePt (γ + h))) := by
      push_cast
      ring
    rw [hre] at h0
    rw [← h0, Complex.im_ofReal_mul]
  -- continuity at 0 of the unit and its imaginary part
  have hinner : Continuous (fun h : ℝ => linePt (γ + h)) := by
    unfold linePt
    exact continuous_const.add
      ((Complex.continuous_ofReal.comp
        (continuous_const.add continuous_id)).mul continuous_const)
  have hg_at : ContinuousAt (fun h : ℝ => g (linePt (γ + h))) 0 := by
    have h1 : ContinuousAt (fun h : ℝ => linePt (γ + h)) 0 := hinner.continuousAt
    have h2 : ContinuousAt g ((fun h : ℝ => linePt (γ + h)) 0) := by
      simp only [add_zero]
      exact hgA.continuousAt
    exact ContinuousAt.comp h2 h1
  have hu_at : ContinuousAt u 0 :=
    Complex.continuous_re.continuousAt.comp (continuousAt_const.mul hg_at)
  have hv_at : ContinuousAt v 0 :=
    Complex.continuous_im.continuousAt.comp (continuousAt_const.mul hg_at)
  -- the unit is real at 0: v 0 = 0 by limit uniqueness over the punctured line
  have hv0 : v 0 = 0 := by
    have hev0 : ∀ᶠ h in nhdsWithin (0:ℝ) {(0:ℝ)}ᶜ, v h = 0 := by
      rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
      refine ⟨r, hr, fun h hh hne => ?_⟩
      have hhr : |h| < r := by
        rw [Real.dist_eq, sub_zero] at hh
        exact hh
      have h0 := hXi_im h hhr
      have hm0 : h ≠ 0 := by
        simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hne
      have hpow : h^m ≠ 0 := pow_ne_zero _ hm0
      rcases mul_eq_zero.mp h0.symm with h1 | h1
      · exact absurd h1 hpow
      · exact h1
    have h1 : Filter.Tendsto v (nhdsWithin (0:ℝ) {(0:ℝ)}ᶜ) (nhds (v 0)) :=
      hv_at.continuousWithinAt.tendsto
    have hev0' : v =ᶠ[nhdsWithin (0:ℝ) {(0:ℝ)}ᶜ] fun _ => 0 := hev0
    have h2 : Filter.Tendsto v (nhdsWithin (0:ℝ) {(0:ℝ)}ᶜ) (nhds 0) :=
      Filter.Tendsto.congr' hev0'.symm tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  -- hence u 0 ≠ 0
  have hu0 : u 0 ≠ 0 := by
    intro h0
    apply hg0
    have hgval : I^m * g (linePt (γ + 0)) = 0 := by
      apply Complex.ext
      · exact h0
      · exact hv0
    rw [show γ + (0:ℝ) = γ from add_zero γ] at hgval
    have hI : (I:ℂ)^m ≠ 0 := pow_ne_zero _ I_ne_zero
    exact (mul_eq_zero.mp hgval).resolve_left hI
  -- the sign window
  obtain ⟨ε₁, hε₁, hus⟩ := Metric.continuousAt_iff.mp hu_at (|u 0|/2)
    (by positivity)
  refine ⟨min r ε₁, lt_min hr hε₁, fun δ hδ0 hδ => ?_⟩
  have hδr : δ < r := lt_of_lt_of_le hδ (min_le_left _ _)
  have hδε : δ < ε₁ := lt_of_lt_of_le hδ (min_le_right _ _)
  have hup : |u δ - u 0| < |u 0|/2 := by
    have := hus (by rw [Real.dist_eq, sub_zero, abs_of_pos hδ0]; exact hδε)
    rwa [Real.dist_eq] at this
  have hum : |u (-δ) - u 0| < |u 0|/2 := by
    have := hus (by
      rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hδ0]
      exact hδε : dist (-δ) 0 < ε₁)
    rwa [Real.dist_eq] at this
  have hXp : XiLine (γ + δ) = δ^m * u δ :=
    hXi_eq δ (by rw [abs_of_pos hδ0]; exact hδr)
  have hXm : XiLine (γ - δ) = (-δ)^m * u (-δ) := by
    have := hXi_eq (-δ) (by rw [abs_neg, abs_of_pos hδ0]; exact hδr)
    rw [show γ + -δ = γ - δ by ring] at this
    exact this
  have hoddm : Odd m := hodd
  have hnegpow : (-δ)^m = -(δ^m) := hoddm.neg_pow δ
  have hδm : (0:ℝ) < δ^m := pow_pos hδ0 m
  rw [hXp, hXm, hnegpow]
  -- u(δ), u(−δ) share the sign of u 0
  rcases lt_or_gt_of_ne hu0 with hneg | hpos
  · -- u 0 < 0: both < u0/2 < 0
    have h1 : u δ < u 0 / 2 := by
      have := abs_lt.mp hup
      have ha : |u 0| = -(u 0) := abs_of_neg hneg
      rw [ha] at this
      linarith [this.2]
    have h2 : u (-δ) < u 0 / 2 := by
      have := abs_lt.mp hum
      have ha : |u 0| = -(u 0) := abs_of_neg hneg
      rw [ha] at this
      linarith [this.2]
    have hupos : 0 < u δ * u (-δ) := by
      have hd1 : u δ < 0 := by linarith
      have hd2 : u (-δ) < 0 := by linarith
      exact mul_pos_of_neg_of_neg hd1 hd2
    nlinarith [mul_pos hδm hδm, hupos]
  · -- u 0 > 0: both > u0/2 > 0
    have h1 : u 0 / 2 < u δ := by
      have := abs_lt.mp hup
      have ha : |u 0| = u 0 := abs_of_pos hpos
      rw [ha] at this
      linarith [this.1]
    have h2 : u 0 / 2 < u (-δ) := by
      have := abs_lt.mp hum
      have ha : |u 0| = u 0 := abs_of_pos hpos
      rw [ha] at this
      linarith [this.1]
    have hupos : 0 < u δ * u (-δ) := by
      have hd1 : 0 < u δ := by linarith
      have hd2 : 0 < u (-δ) := by linarith
      exact mul_pos hd1 hd2
    nlinarith [mul_pos hδm hδm, hupos]

end CriticalLinePhasor.SeatingLedger

#print axioms CriticalLinePhasor.SeatingLedger.odd_mult_flips
