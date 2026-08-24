import RequestProject.XiOrder
import RequestProject.DVPTruncatedZeta
import PrimeNumberTheoremAnd.RectangleArgumentPrinciple

/-!
# The argument-principle campaign, brick A1: the box count as a contour

Opening brick of the Riemann–von Mangoldt (lower-density) campaign: for a
rectangle `[-1, 2] × [T₁, T₂]` whose border avoids the zeros, the number of
nontrivial zeros in the box — WITH ledger multiplicity `xiOrderNat` — equals
the rectangle contour integral of `ξ'/ξ`.  Instantiates PNT+'s
`rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt` (sorry-free, checked
at source) at `ξ`.  The remaining campaign content is the boundary
estimate (Backlund/Stirling) for the integral.
-/

open Complex

noncomputable section

namespace CriticalLinePhasor.DVP

/-- ξ is entire, hence meromorphic on any set. -/
theorem riemannXi_meromorphicOn (U : Set ℂ) :
    MeromorphicOn ZD.riemannXi U :=
  (ZD.ZeroCount.riemannXi_analyticOnNhd_univ.mono
    (Set.subset_univ U)).meromorphicOn

/-- `ξ'/ξ` is meromorphic on any set. -/
theorem logDeriv_riemannXi_meromorphicOn (U : Set ℂ) :
    MeromorphicOn (logDeriv ZD.riemannXi) U := by
  have hd : MeromorphicOn (deriv ZD.riemannXi) U := by
    apply AnalyticOnNhd.meromorphicOn
    intro z hz
    exact (ZD.ZeroCount.riemannXi_analyticOnNhd_univ z (Set.mem_univ z)).deriv
  have hx := riemannXi_meromorphicOn U
  have hdiv := hd.div hx
  exact hdiv

/-- Finite meromorphic order of ξ everywhere. -/
theorem riemannXi_meromorphicOrderAt_ne_top (p : ℂ) :
    meromorphicOrderAt ZD.riemannXi p ≠ ⊤ := by
  rw [(ZD.ZeroCount.riemannXi_analyticOnNhd_univ p
    (Set.mem_univ p)).meromorphicOrderAt_eq]
  intro htop
  exact ZD.riemannXi_analyticOrderAt_ne_top_everywhere p
    (ENat.map_eq_top_iff.mp htop)

set_option maxHeartbeats 1600000 in
/-- **A1: the box count as a contour integral.**  If the border of the
rectangle avoids the zeros, then
`∮ ξ'/ξ = Σ_{box zeros} xiOrderNat` — the window count of the RvM campaign,
exactly. -/
theorem xi_box_count_eq_contour {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (hbd : Disjoint (RectangleBorder z w)
      (MeromorphicOn.divisor ZD.riemannXi (Rectangle z w)).support) :
    RectangleIntegral' (logDeriv ZD.riemannXi) z w
      = ∑ p ∈ (divisor_support_rectangle_finite ZD.riemannXi z w).toFinset,
          (ZD.xiOrderNat p : ℂ) := by
  have hmain := rectangleIntegral_logDeriv_eq_sum_meromorphicOrderAt
    hre him (riemannXi_meromorphicOn _) (logDeriv_riemannXi_meromorphicOn _)
    (fun p _ => riemannXi_meromorphicOrderAt_ne_top p) hbd
  rw [hmain]
  apply Finset.sum_congr rfl
  intro p hp
  have hpR : p ∈ Rectangle z w := by
    have hpD := (divisor_support_rectangle_finite
      ZD.riemannXi z w).mem_toFinset.mp hp
    exact (MeromorphicOn.divisor ZD.riemannXi
      (Rectangle z w)).supportWithinDomain hpD
  have hanal : AnalyticAt ℂ ZD.riemannXi p :=
    ZD.ZeroCount.riemannXi_analyticOnNhd_univ p (Set.mem_univ p)
  rw [MeromorphicOn.divisor_apply (riemannXi_meromorphicOn _) hpR,
    hanal.meromorphicOrderAt_eq]
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℕ∞) = analyticOrderAt ZD.riemannXi p :=
    ENat.ne_top_iff_exists.mp
      (ZD.riemannXi_analyticOrderAt_ne_top_everywhere p)
  rw [← hn]
  have hnat : ZD.xiOrderNat p = n := by
    unfold ZD.xiOrderNat analyticOrderNatAt
    rw [← hn]
    rfl
  rw [hnat]
  simp

set_option maxHeartbeats 1600000 in
/-- **A2-support: the eta rearrangement** on `Re s > 1`:
`(1 − 2^{1−s})·ζ(s) = Σ (−1)ⁿ/(n+1)^s`.  Absolute convergence permits the
even/odd split; the odd half is `2^{−s}·ζ`.  Feeds the no-real-zeros brick
(alternating positivity on `(0,1)` + continuation). -/
theorem alternating_zeta_identity {s : ℂ} (hs : 1 < s.re) :
    (1 - 2 ^ ((1:ℂ) - s)) * riemannZeta s
      = ∑' n : ℕ, (-1)^n / ((n:ℂ) + 1) ^ s := by
  set a : ℕ → ℂ := fun n => 1 / ((n:ℂ) + 1) ^ s with ha
  have hζ : riemannZeta s = ∑' n, a n := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  have hsum_a : Summable a := by
    have h1 : Summable (fun n : ℕ => 1 / ((n:ℂ)) ^ s) :=
      Complex.summable_one_div_nat_cpow.mpr hs
    have h2 := (summable_nat_add_iff 1).mpr h1
    apply Summable.congr h2
    intro n
    rw [ha]
    push_cast
    rfl
  set f : ℕ → ℂ := fun n => (-1)^n / ((n:ℂ) + 1) ^ s with hf
  have hf_eq : ∀ n, f n = (-1)^n * a n := by
    intro n
    rw [hf, ha]
    dsimp only
    rw [div_eq_mul_inv, one_div]
  have hsum_f : Summable f := by
    apply Summable.of_norm
    have : ∀ n, ‖f n‖ = ‖a n‖ := by
      intro n
      rw [hf_eq n, norm_mul]
      simp
    rw [show (fun n => ‖f n‖) = fun n => ‖a n‖ from funext this]
    exact summable_norm_iff.mpr hsum_a
  -- even/odd split of both series
  have hsum_ae : Summable (fun k => a (2*k)) :=
    hsum_a.comp_injective (fun x y h => by omega)
  have hsum_ao : Summable (fun k => a (2*k+1)) :=
    hsum_a.comp_injective (fun x y h => by omega)
  have hsum_fe : Summable (fun k => f (2*k)) :=
    hsum_f.comp_injective (fun x y h => by omega)
  have hsum_fo : Summable (fun k => f (2*k+1)) :=
    hsum_f.comp_injective (fun x y h => by omega)
  have hsplit_a := tsum_even_add_odd hsum_ae hsum_ao
  have hsplit_f := tsum_even_add_odd hsum_fe hsum_fo
  -- identify the halves
  have hfe : ∀ k, f (2*k) = a (2*k) := by
    intro k
    rw [hf_eq]
    rw [pow_mul]
    norm_num
  have hfo : ∀ k, f (2*k+1) = -(a (2*k+1)) := by
    intro k
    rw [hf_eq]
    rw [pow_add, pow_mul]
    norm_num
  -- the odd half is 2^{−s}·ζ
  have hodd : (∑' k, a (2*k+1)) = 2 ^ (-s) * riemannZeta s := by
    have hterm : ∀ k : ℕ, a (2*k+1) = 2 ^ (-s) * a k := by
      intro k
      rw [ha]
      dsimp only
      have hcast : ((2*k+1 : ℕ):ℂ) + 1 = 2 * ((k:ℂ) + 1) := by
        push_cast
        ring
      rw [hcast]
      have hmul : ((2:ℂ) * ((k:ℂ) + 1)) ^ s
          = (2:ℂ) ^ s * ((k:ℂ) + 1) ^ s := by
        have key := Complex.mul_cpow_ofReal_nonneg
          (show (0:ℝ) ≤ 2 by norm_num)
          (show (0:ℝ) ≤ (k:ℝ)+1 by positivity) s
        push_cast at key
        exact key
      rw [hmul]
      rw [Complex.cpow_neg]
      have h2s : (2:ℂ) ^ s ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero (by norm_num : (2:ℂ) ≠ 0)]
        exact Complex.exp_ne_zero _
      field_simp
    rw [tsum_congr hterm, tsum_mul_left, ← hζ]
  -- assemble
  have hLHS : (∑' n, f n) = (∑' k, a (2*k)) - (∑' k, a (2*k+1)) := by
    rw [← hsplit_f, tsum_congr hfe, tsum_congr hfo, tsum_neg]
    ring
  have hRHS : (∑' k, a (2*k)) = riemannZeta s - (∑' k, a (2*k+1)) := by
    have := hsplit_a
    rw [← hζ] at this
    linear_combination this
  rw [show (∑' n : ℕ, (-1)^n / ((n:ℂ) + 1) ^ s) = ∑' n, f n from rfl,
    hLHS, hRHS, hodd]
  have h2pow : (2:ℂ) ^ ((1:ℂ) - s) = 2 * 2 ^ (-s) := by
    rw [show (1:ℂ) - s = 1 + (-s) by ring, Complex.cpow_add _ _ (by norm_num),
      Complex.cpow_one]
  rw [h2pow]
  ring

set_option maxHeartbeats 1600000 in
/-- **No real zeros in the strip**: `Re ζ(σ) < 0` for real `σ ∈ (0,1)`.
Route collapse: the compiled N=1 truncated representation gives
`ζ(σ) = 1 − 1/(1−σ) − σ·Tail` with `Tail ≥ 0` termwise (the fract-integrand
is a nonnegative real), so `Re ζ(σ) ≤ σ/(σ−1) < 0` — no eta continuation
needed. -/
theorem zeta_re_neg_of_real_unit {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    (riemannZeta ((σ:ℝ):ℂ)).re < 0 := by
  have hs1 : ((σ:ℝ):ℂ) ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hσre : (0:ℝ) < (((σ:ℝ):ℂ)).re := by
    simp
    linarith
  rw [truncated_zeta_pos_re (N := 1) le_rfl hσre hs1]
  unfold truncatedRep
  have hhead : (∑ n ∈ Finset.range (1 + 1), (((n : ℝ)) : ℂ) ^ (-((σ:ℝ):ℂ)))
      = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    have h00 : (((0 : ℕ) : ℝ) : ℂ) ^ (-((σ:ℝ):ℂ)) = 0 := by
      rw [Nat.cast_zero, Complex.ofReal_zero, zero_cpow]
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have h1' : (((1 : ℕ) : ℝ) : ℂ) ^ (-((σ:ℝ):ℂ)) = 1 := by
      rw [Nat.cast_one, Complex.ofReal_one, one_cpow]
    rw [h00, h1']
    ring
  have hbdry : (((1:ℕ) : ℝ) : ℂ) ^ (1 - ((σ:ℝ):ℂ)) / (((σ:ℝ):ℂ) - 1)
      = 1 / (((σ:ℝ):ℂ) - 1) := by
    rw [Nat.cast_one, Complex.ofReal_one, one_cpow]
  rw [hhead, hbdry]
  -- the tail has nonnegative real part, termwise
  have hσC : (0:ℝ) < (((σ:ℝ):ℂ)).re := hσre
  have hterm_re : ∀ k : ℕ, (0:ℝ)
      ≤ (∫ x : ℝ in ((1 + k : ℕ) : ℝ)..(((1 + k : ℕ) : ℝ) + 1),
          ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-((σ:ℝ):ℂ) - 1)).re := by
    intro k
    have hab : ((1 + k : ℕ) : ℝ) ≤ ((1 + k : ℕ) : ℝ) + 1 := by linarith
    have hcongr : ∀ x ∈ Set.uIcc ((1 + k : ℕ) : ℝ) (((1 + k : ℕ) : ℝ) + 1),
        ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-((σ:ℝ):ℂ) - 1)
        = ((Int.fract x * x ^ (-σ - 1) : ℝ) : ℂ) := by
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      have hxpos : (0:ℝ) < x := by
        have h1k : (1:ℝ) ≤ ((1 + k : ℕ) : ℝ) := by
          push_cast
          linarith [Nat.cast_nonneg' (α := ℝ) k]
        linarith [hx.1]
      have hexp : (-((σ:ℝ):ℂ) - 1) = ((-σ - 1 : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hexp, ← Complex.ofReal_cpow hxpos.le, ← Complex.ofReal_mul]
    rw [intervalIntegral.integral_congr hcongr,
      intervalIntegral.integral_ofReal]
    simp only [Complex.ofReal_re]
    apply intervalIntegral.integral_nonneg hab
    intro x hx
    have hxpos : (0:ℝ) < x := by
      have h1k : (1:ℝ) ≤ ((1 + k : ℕ) : ℝ) := by
        push_cast
        linarith [Nat.cast_nonneg' (α := ℝ) k]
      linarith [hx.1]
    have hfr : (0:ℝ) ≤ Int.fract x := Int.fract_nonneg x
    have hrp : (0:ℝ) ≤ x ^ (-σ - 1) := Real.rpow_nonneg hxpos.le _
    positivity
  have hsumI := summable_shift_integral (N := 1) le_rfl hσC
  have htail_re : (0:ℝ)
      ≤ (∑' k : ℕ, ∫ x : ℝ in ((1 + k : ℕ) : ℝ)..(((1 + k : ℕ) : ℝ) + 1),
          ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-((σ:ℝ):ℂ) - 1)).re := by
    rw [Complex.re_tsum hsumI]
    apply tsum_nonneg
    exact hterm_re
  -- assemble the real part
  have hre_bdry : (1 / (((σ:ℝ):ℂ) - 1)).re = 1/(σ - 1) := by
    rw [show ((σ:ℝ):ℂ) - 1 = (((σ - 1 : ℝ)):ℂ) by push_cast; ring,
      one_div, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  have hre_mul : ((((σ:ℝ):ℂ))
      * (∑' k : ℕ, ∫ x : ℝ in ((1 + k : ℕ) : ℝ)..(((1 + k : ℕ) : ℝ) + 1),
          ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-((σ:ℝ):ℂ) - 1))).re
      = σ * (∑' k : ℕ, ∫ x : ℝ in ((1 + k : ℕ) : ℝ)..(((1 + k : ℕ) : ℝ) + 1),
          ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-((σ:ℝ):ℂ) - 1)).re := by
    rw [Complex.mul_re]
    simp
  have hfinal : (1 + 1 / (((σ:ℝ):ℂ) - 1)
      - ((σ:ℝ):ℂ) * (∑' k : ℕ, ∫ x : ℝ
          in ((1 + k : ℕ) : ℝ)..(((1 + k : ℕ) : ℝ) + 1),
          ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-((σ:ℝ):ℂ) - 1))).re
      = 1 + 1/(σ - 1)
        - σ * (∑' k : ℕ, ∫ x : ℝ
            in ((1 + k : ℕ) : ℝ)..(((1 + k : ℕ) : ℝ) + 1),
            ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-((σ:ℝ):ℂ) - 1)).re := by
    rw [Complex.sub_re, Complex.add_re, hre_bdry, hre_mul]
    simp
  rw [hfinal]
  have hneg : 1 + 1/(σ - 1) < 0 := by
    have hσ1 : σ - 1 < 0 := by linarith
    have hne : σ - 1 ≠ 0 := by linarith
    have : 1 + 1/(σ - 1) = σ/(σ - 1) := by
      field_simp
      ring
    rw [this]
    exact div_neg_of_pos_of_neg h0 hσ1
  nlinarith [mul_nonneg h0.le htail_re]

/-- **No zeros on the real segment `(0,1)`.** -/
theorem zeta_ne_zero_of_real_unit {σ : ℝ} (h0 : 0 < σ) (h1 : σ < 1) :
    riemannZeta ((σ:ℝ):ℂ) ≠ 0 := by
  intro h
  have := zeta_re_neg_of_real_unit h0 h1
  rw [h] at this
  simp at this

/-- **Every nontrivial zero is off the real axis.** -/
theorem NontrivialZeros_im_ne_zero {ρ : ℂ} (hρ : ρ ∈ ZD.NontrivialZeros) :
    ρ.im ≠ 0 := by
  intro h0
  have hρre : ρ = ((ρ.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [h0]
  have := zeta_ne_zero_of_real_unit hρ.1 hρ.2.1
  rw [← hρre] at this
  exact this hρ.2.2

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.xi_box_count_eq_contour
#print axioms CriticalLinePhasor.DVP.alternating_zeta_identity
#print axioms CriticalLinePhasor.DVP.zeta_re_neg_of_real_unit
#print axioms CriticalLinePhasor.DVP.NontrivialZeros_im_ne_zero
end AxiomAudit
