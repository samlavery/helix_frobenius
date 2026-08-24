import RequestProject.DVPArctanEnclosure
import RequestProject.DVPThetaEnclosure
import RequestProject.DVPPilotStation

/-!
# The θ(30) head, block A: `Σ_{n<14} sTermT 30 n = 110.2862 − 14π ± 5·10⁻⁴`

Fourteen complement-side terms (arctan arguments > 1), each reduced exactly
to `π/2 − arctan yₙ` and the `yₙ` anchored at ½ (order 5).
-/

open Finset
open CriticalLinePhasor.CarrierScale

noncomputable section

namespace CriticalLinePhasor.DVP

set_option maxHeartbeats 12800000 in
/-- **Block A of the θ(30) head.** -/
theorem theta30_head_A :
    |(∑ n ∈ Finset.range 14, sTermT 30 n)
      - (1102862/10000 - 14 * Real.pi)| ≤ 5/10000 := by
  -- exact unfolds
  have e0 : sTermT 30 0 = 30 - 2 * Real.arctan 12 := by
    rw [sTermT]; norm_num
  have e1 : sTermT 30 1 = 15 - 2 * Real.arctan (20/3) := by
    rw [sTermT]; norm_num
  have e2 : sTermT 30 2 = 10 - 2 * Real.arctan (60/13) := by
    rw [sTermT]; norm_num
  have e3 : sTermT 30 3 = 30/4 - 2 * Real.arctan (60/17) := by
    rw [sTermT]; norm_num
  have e4 : sTermT 30 4 = 6 - 2 * Real.arctan (20/7) := by
    rw [sTermT]; norm_num
  have e5 : sTermT 30 5 = 5 - 2 * Real.arctan (12/5) := by
    rw [sTermT]; norm_num
  have e6 : sTermT 30 6 = 30/7 - 2 * Real.arctan (60/29) := by
    rw [sTermT]; norm_num
  have e7 : sTermT 30 7 = 30/8 - 2 * Real.arctan (20/11) := by
    rw [sTermT]; norm_num
  have e8 : sTermT 30 8 = 30/9 - 2 * Real.arctan (60/37) := by
    rw [sTermT]; norm_num
  have e9 : sTermT 30 9 = 3 - 2 * Real.arctan (60/41) := by
    rw [sTermT]; norm_num
  have e10 : sTermT 30 10 = 30/11 - 2 * Real.arctan (4/3) := by
    rw [sTermT]; norm_num
  have e11 : sTermT 30 11 = 30/12 - 2 * Real.arctan (60/49) := by
    rw [sTermT]; norm_num
  have e12 : sTermT 30 12 = 30/13 - 2 * Real.arctan (60/53) := by
    rw [sTermT]; norm_num
  have e13 : sTermT 30 13 = 30/14 - 2 * Real.arctan (20/19) := by
    rw [sTermT]; norm_num
  -- exact complements
  have hcomp : ∀ x : ℝ, 0 < x →
      Real.arctan x = Real.pi/2 - Real.arctan x⁻¹ := by
    intro x hx
    have := Real.arctan_inv_of_pos hx
    linarith
  have c0 := hcomp 12 (by norm_num)
  have c1 := hcomp (20/3) (by norm_num)
  have c2 := hcomp (60/13) (by norm_num)
  have c3 := hcomp (60/17) (by norm_num)
  have c4 := hcomp (20/7) (by norm_num)
  have c5 := hcomp (12/5) (by norm_num)
  have c6 := hcomp (60/29) (by norm_num)
  have c7 := hcomp (20/11) (by norm_num)
  have c8 := hcomp (60/37) (by norm_num)
  have c9 := hcomp (60/41) (by norm_num)
  have c10 := hcomp (4/3) (by norm_num)
  have c11 := hcomp (60/49) (by norm_num)
  have c12 := hcomp (60/53) (by norm_num)
  have c13 := hcomp (20/19) (by norm_num)
  norm_num at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13
  -- anchored bounds at the fourteen reciprocals
  have b0 := arctan_half_range (x := (1/12:ℝ)) (by norm_num) (by norm_num) 5
  have b1 := arctan_half_range (x := (3/20:ℝ)) (by norm_num) (by norm_num) 5
  have b2 := arctan_half_range (x := (13/60:ℝ)) (by norm_num) (by norm_num) 5
  have b3 := arctan_half_range (x := (17/60:ℝ)) (by norm_num) (by norm_num) 5
  have b4 := arctan_half_range (x := (7/20:ℝ)) (by norm_num) (by norm_num) 5
  have b5 := arctan_half_range (x := (5/12:ℝ)) (by norm_num) (by norm_num) 5
  have b6 := arctan_half_range (x := (29/60:ℝ)) (by norm_num) (by norm_num) 5
  have b7 := arctan_half_range (x := (11/20:ℝ)) (by norm_num) (by norm_num) 5
  have b8 := arctan_half_range (x := (37/60:ℝ)) (by norm_num) (by norm_num) 5
  have b9 := arctan_half_range (x := (41/60:ℝ)) (by norm_num) (by norm_num) 5
  have b10 := arctan_half_range (x := (3/4:ℝ)) (by norm_num) (by norm_num) 5
  have b11 := arctan_half_range (x := (49/60:ℝ)) (by norm_num) (by norm_num) 5
  have b12 := arctan_half_range (x := (53/60:ℝ)) (by norm_num) (by norm_num) 5
  have b13 := arctan_half_range (x := (19/20:ℝ)) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at b0 b1 b2 b3 b4 b5 b6
  norm_num [Finset.sum_range_succ] at b7 b8 b9 b10 b11 b12 b13
  obtain ⟨l0, u0⟩ := abs_le.mp b0
  obtain ⟨l1, u1⟩ := abs_le.mp b1
  obtain ⟨l2, u2⟩ := abs_le.mp b2
  obtain ⟨l3, u3⟩ := abs_le.mp b3
  obtain ⟨l4, u4⟩ := abs_le.mp b4
  obtain ⟨l5, u5⟩ := abs_le.mp b5
  obtain ⟨l6, u6⟩ := abs_le.mp b6
  obtain ⟨l7, u7⟩ := abs_le.mp b7
  obtain ⟨l8, u8⟩ := abs_le.mp b8
  obtain ⟨l9, u9⟩ := abs_le.mp b9
  obtain ⟨l10, u10⟩ := abs_le.mp b10
  obtain ⟨l11, u11⟩ := abs_le.mp b11
  obtain ⟨l12, u12⟩ := abs_le.mp b12
  obtain ⟨l13, u13⟩ := abs_le.mp b13
  -- assemble
  rw [show (14:ℕ) = 13+1 from rfl, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13,
    c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13]
  rw [abs_le]
  constructor
  · linarith [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13,
      u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13]
  · linarith [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, l13,
      u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12, u13]

set_option maxHeartbeats 25600000 in
/-- **Block B of the θ(30) head**: the 26 direct-side terms. -/
theorem theta30_head_B :
    |(∑ n ∈ Finset.range 26, sTermT 30 (14+n)) - 37426/10000|
      ≤ 6/10000 := by
  have e0 : sTermT 30 (14+0) = 2 - 2 * Real.arctan (60/61) := by
    rw [sTermT]; norm_num
  have e1 : sTermT 30 (14+1) = 30/16 - 2 * Real.arctan (12/13) := by
    rw [sTermT]; norm_num
  have e2 : sTermT 30 (14+2) = 30/17 - 2 * Real.arctan (20/23) := by
    rw [sTermT]; norm_num
  have e3 : sTermT 30 (14+3) = 30/18 - 2 * Real.arctan (60/73) := by
    rw [sTermT]; norm_num
  have e4 : sTermT 30 (14+4) = 30/19 - 2 * Real.arctan (60/77) := by
    rw [sTermT]; norm_num
  have e5 : sTermT 30 (14+5) = 30/20 - 2 * Real.arctan (20/27) := by
    rw [sTermT]; norm_num
  have e6 : sTermT 30 (14+6) = 30/21 - 2 * Real.arctan (12/17) := by
    rw [sTermT]; norm_num
  have e7 : sTermT 30 (14+7) = 30/22 - 2 * Real.arctan (60/89) := by
    rw [sTermT]; norm_num
  have e8 : sTermT 30 (14+8) = 30/23 - 2 * Real.arctan (20/31) := by
    rw [sTermT]; norm_num
  have e9 : sTermT 30 (14+9) = 30/24 - 2 * Real.arctan (60/97) := by
    rw [sTermT]; norm_num
  have e10 : sTermT 30 (14+10) = 30/25 - 2 * Real.arctan (60/101) := by
    rw [sTermT]; norm_num
  have e11 : sTermT 30 (14+11) = 30/26 - 2 * Real.arctan (4/7) := by
    rw [sTermT]; norm_num
  have e12 : sTermT 30 (14+12) = 30/27 - 2 * Real.arctan (60/109) := by
    rw [sTermT]; norm_num
  have e13 : sTermT 30 (14+13) = 30/28 - 2 * Real.arctan (60/113) := by
    rw [sTermT]; norm_num
  have e14 : sTermT 30 (14+14) = 30/29 - 2 * Real.arctan (20/39) := by
    rw [sTermT]; norm_num
  have e15 : sTermT 30 (14+15) = 1 - 2 * Real.arctan (60/121) := by
    rw [sTermT]; norm_num
  have e16 : sTermT 30 (14+16) = 30/31 - 2 * Real.arctan (12/25) := by
    rw [sTermT]; norm_num
  have e17 : sTermT 30 (14+17) = 30/32 - 2 * Real.arctan (20/43) := by
    rw [sTermT]; norm_num
  have e18 : sTermT 30 (14+18) = 30/33 - 2 * Real.arctan (60/133) := by
    rw [sTermT]; norm_num
  have e19 : sTermT 30 (14+19) = 30/34 - 2 * Real.arctan (60/137) := by
    rw [sTermT]; norm_num
  have e20 : sTermT 30 (14+20) = 30/35 - 2 * Real.arctan (20/47) := by
    rw [sTermT]; norm_num
  have e21 : sTermT 30 (14+21) = 30/36 - 2 * Real.arctan (12/29) := by
    rw [sTermT]; norm_num
  have e22 : sTermT 30 (14+22) = 30/37 - 2 * Real.arctan (60/149) := by
    rw [sTermT]; norm_num
  have e23 : sTermT 30 (14+23) = 30/38 - 2 * Real.arctan (20/51) := by
    rw [sTermT]; norm_num
  have e24 : sTermT 30 (14+24) = 30/39 - 2 * Real.arctan (60/157) := by
    rw [sTermT]; norm_num
  have e25 : sTermT 30 (14+25) = 30/40 - 2 * Real.arctan (60/161) := by
    rw [sTermT]; norm_num
  -- anchored bounds
  have b0 := arctan_half_range (x := (60/61:ℝ)) (by norm_num) (by norm_num) 5
  have b1 := arctan_half_range (x := (12/13:ℝ)) (by norm_num) (by norm_num) 5
  have b2 := arctan_half_range (x := (20/23:ℝ)) (by norm_num) (by norm_num) 5
  have b3 := arctan_half_range (x := (60/73:ℝ)) (by norm_num) (by norm_num) 5
  have b4 := arctan_half_range (x := (60/77:ℝ)) (by norm_num) (by norm_num) 5
  have b5 := arctan_half_range (x := (20/27:ℝ)) (by norm_num) (by norm_num) 5
  have b6 := arctan_half_range (x := (12/17:ℝ)) (by norm_num) (by norm_num) 5
  have b7 := arctan_half_range (x := (60/89:ℝ)) (by norm_num) (by norm_num) 5
  have b8 := arctan_half_range (x := (20/31:ℝ)) (by norm_num) (by norm_num) 5
  have b9 := arctan_half_range (x := (60/97:ℝ)) (by norm_num) (by norm_num) 5
  have b10 := arctan_half_range (x := (60/101:ℝ)) (by norm_num) (by norm_num) 5
  have b11 := arctan_half_range (x := (4/7:ℝ)) (by norm_num) (by norm_num) 5
  have b12 := arctan_half_range (x := (60/109:ℝ)) (by norm_num) (by norm_num) 5
  have b13 := arctan_half_range (x := (60/113:ℝ)) (by norm_num) (by norm_num) 5
  have b14 := arctan_half_range (x := (20/39:ℝ)) (by norm_num) (by norm_num) 5
  have b15 := arctan_half_range (x := (60/121:ℝ)) (by norm_num) (by norm_num) 5
  have b16 := arctan_half_range (x := (12/25:ℝ)) (by norm_num) (by norm_num) 5
  have b17 := arctan_half_range (x := (20/43:ℝ)) (by norm_num) (by norm_num) 5
  have b18 := arctan_half_range (x := (60/133:ℝ)) (by norm_num) (by norm_num) 5
  have b19 := arctan_half_range (x := (60/137:ℝ)) (by norm_num) (by norm_num) 5
  have b20 := arctan_half_range (x := (20/47:ℝ)) (by norm_num) (by norm_num) 5
  have b21 := arctan_half_range (x := (12/29:ℝ)) (by norm_num) (by norm_num) 5
  have b22 := arctan_half_range (x := (60/149:ℝ)) (by norm_num) (by norm_num) 5
  have b23 := arctan_half_range (x := (20/51:ℝ)) (by norm_num) (by norm_num) 5
  have b24 := arctan_half_range (x := (60/157:ℝ)) (by norm_num) (by norm_num) 5
  have b25 := arctan_half_range (x := (60/161:ℝ)) (by norm_num) (by norm_num) 5
  norm_num [Finset.sum_range_succ] at b0 b1 b2 b3 b4 b5 b6
  norm_num [Finset.sum_range_succ] at b7 b8 b9 b10 b11 b12 b13
  norm_num [Finset.sum_range_succ] at b14 b15 b16 b17 b18 b19 b20
  norm_num [Finset.sum_range_succ] at b21 b22 b23 b24 b25
  obtain ⟨l0, u0⟩ := abs_le.mp b0
  obtain ⟨l1, u1⟩ := abs_le.mp b1
  obtain ⟨l2, u2⟩ := abs_le.mp b2
  obtain ⟨l3, u3⟩ := abs_le.mp b3
  obtain ⟨l4, u4⟩ := abs_le.mp b4
  obtain ⟨l5, u5⟩ := abs_le.mp b5
  obtain ⟨l6, u6⟩ := abs_le.mp b6
  obtain ⟨l7, u7⟩ := abs_le.mp b7
  obtain ⟨l8, u8⟩ := abs_le.mp b8
  obtain ⟨l9, u9⟩ := abs_le.mp b9
  obtain ⟨l10, u10⟩ := abs_le.mp b10
  obtain ⟨l11, u11⟩ := abs_le.mp b11
  obtain ⟨l12, u12⟩ := abs_le.mp b12
  obtain ⟨l13, u13⟩ := abs_le.mp b13
  obtain ⟨l14, u14⟩ := abs_le.mp b14
  obtain ⟨l15, u15⟩ := abs_le.mp b15
  obtain ⟨l16, u16⟩ := abs_le.mp b16
  obtain ⟨l17, u17⟩ := abs_le.mp b17
  obtain ⟨l18, u18⟩ := abs_le.mp b18
  obtain ⟨l19, u19⟩ := abs_le.mp b19
  obtain ⟨l20, u20⟩ := abs_le.mp b20
  obtain ⟨l21, u21⟩ := abs_le.mp b21
  obtain ⟨l22, u22⟩ := abs_le.mp b22
  obtain ⟨l23, u23⟩ := abs_le.mp b23
  obtain ⟨l24, u24⟩ := abs_le.mp b24
  obtain ⟨l25, u25⟩ := abs_le.mp b25
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rw [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14,
    e15, e16, e17, e18, e19, e20, e21, e22, e23, e24, e25]
  rw [abs_le]
  constructor
  · linarith [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12,
      l13, l14, l15, l16, l17, l18, l19, l20, l21, l22, l23, l24, l25,
      u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12,
      u13, u14, u15, u16, u17, u18, u19, u20, u21, u22, u23, u24, u25]
  · linarith [l0, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12,
      l13, l14, l15, l16, l17, l18, l19, l20, l21, l22, l23, l24, l25,
      u0, u1, u2, u3, u4, u5, u6, u7, u8, u9, u10, u11, u12,
      u13, u14, u15, u16, u17, u18, u19, u20, u21, u22, u23, u24, u25]

/-- **THE θ(30) ENCLOSURE**: `|θ(30) + (15/2)π − 31.6323| ≤ 0.105` —
the census-clock anchor as a certified number (true value 8.0578;
the window is dominated by γ's ±0.16). -/
theorem theta30_enclosure :
    |theta 30 + (15/2) * Real.pi - 316323/10000| ≤ 105/1000 := by
  -- summability of the T = 30 series
  have hsummable : Summable (sTermT 30) := by
    have hbase : Summable (fun n : ℕ => 1/((n:ℝ))^2) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    have hmaj : Summable (fun n : ℕ => (306008:ℝ) * (1/((n:ℝ)+1)^2)) := by
      apply Summable.mul_left
      have hshift : Summable (fun n : ℕ => 1/(((n+1:ℕ)):ℝ)^2) :=
        hbase.comp_injective (fun a b h => by omega)
      apply hshift.congr
      intro n
      push_cast
      ring
    apply Summable.of_norm_bounded hmaj
    intro n
    rw [Real.norm_eq_abs]
    have hc := sTermT_control (T := (30:ℝ)) (by norm_num) n
    have habs := abs_le.mp hc
    have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have ha1 : (1:ℝ) ≤ (n:ℝ) + 1 := by linarith
    have haa : ((n:ℝ)+1) ≤ ((n:ℝ)+5/4) := by linarith
    have hDC : (30/4)/(((n:ℝ)+1)*((n:ℝ)+5/4))
        ≤ (30/4) * (1/((n:ℝ)+1)^2) := by
      rw [mul_one_div]
      refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
      nlinarith
    have hC : (30:ℝ)^3/(12*((n:ℝ)+5/4)^3)
        ≤ 2250 * (1/((n:ℝ)+1)^2) := by
      rw [mul_one_div,
        show (30:ℝ)^3/(12*((n:ℝ)+5/4)^3) = 2250/((n:ℝ)+5/4)^3 from by
          rw [div_eq_div_iff (by positivity) (by positivity)]
          ring]
      refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
      have hp3 : ((n:ℝ)+1)^3 ≤ ((n:ℝ)+5/4)^3 :=
        pow_le_pow_left₀ (by positivity) haa 3
      nlinarith [sq_nonneg ((n:ℝ)+1)]
    have hQ : (30:ℝ)^5/(80*((n:ℝ)+5/4)^5)
        ≤ 303750 * (1/((n:ℝ)+1)^2) := by
      rw [mul_one_div,
        show (30:ℝ)^5/(80*((n:ℝ)+5/4)^5) = 303750/((n:ℝ)+5/4)^5 from by
          rw [div_eq_div_iff (by positivity) (by positivity)]
          ring]
      refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
      have hp5 : ((n:ℝ)+1)^5 ≤ ((n:ℝ)+5/4)^5 :=
        pow_le_pow_left₀ (by positivity) haa 5
      have hp25 : ((n:ℝ)+1)^2 ≤ ((n:ℝ)+1)^5 :=
        pow_le_pow_right₀ ha1 (by norm_num)
      linarith
    have hDC0 : (0:ℝ) ≤ (30/4)/(((n:ℝ)+1)*((n:ℝ)+5/4)) := by positivity
    have hC0 : (0:ℝ) ≤ (30:ℝ)^3/(12*((n:ℝ)+5/4)^3) := by positivity
    have hQ0 : (0:ℝ) ≤ (30:ℝ)^5/(80*((n:ℝ)+5/4)^5) := by positivity
    rw [sTermT, abs_le]
    constructor
    · nlinarith [habs.1, hDC0, hC0, hQ, hQ0,
        mul_nonneg (by norm_num : (0:ℝ) ≤ 306008)
          (by positivity : (0:ℝ) ≤ 1/((n:ℝ)+1)^2)]
    · nlinarith [habs.2, hDC, hC, hQ]
  -- split: Σ' = A-head + B-head + tail
  have hsplit1 := hsummable.sum_add_tsum_nat_add 14
  have hsum14 : Summable (fun i : ℕ => sTermT 30 (i+14)) :=
    (summable_nat_add_iff 14).mpr hsummable
  have hsplit2 := hsum14.sum_add_tsum_nat_add 26
  have hB_align : ∑ i ∈ Finset.range 26, sTermT 30 (i+14)
      = ∑ i ∈ Finset.range 26, sTermT 30 (14+i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.add_comm]
  have hT_align : (∑' i : ℕ, sTermT 30 (i+26+14))
      = ∑' i : ℕ, sTermT 30 (i+40) := by
    apply tsum_congr
    intro i
    congr 1
  -- the certified windows
  have hA := theta30_head_A
  have hB := theta30_head_B
  have hTail := theta30_tail_bracket
  have hγ := gamma_enclosure_tight
  have hlogπ := log_pi_enclosure
  push_cast at hlogπ
  -- arctan 60
  have h60 : |Real.arctan 60 - (Real.pi/2 - 10799/648000)| ≤ 1/10^6 := by
    have hcomp : Real.arctan 60 = Real.pi/2 - Real.arctan (1/60) := by
      have := Real.arctan_inv_of_pos (show (0:ℝ) < 60 by norm_num)
      rw [show (60:ℝ)⁻¹ = 1/60 by norm_num] at this
      linarith
    rw [hcomp]
    have henc := arctan_enclosure (x := (1/60:ℝ)) (by norm_num) 2
    have hP : ∑ k ∈ Finset.range 2,
        (-1 : ℝ) ^ k * (1/60) ^ (2 * k + 1) / (2 * k + 1)
        = 10799/648000 := by
      norm_num [Finset.sum_range_succ]
    rw [hP] at henc
    have htl : ((1:ℝ)/60) ^ (2 * 2 + 1) / (2 * (2:ℕ) + 1) ≤ 1/10^6 := by
      norm_num
    calc |Real.pi/2 - Real.arctan (1/60)
          - (Real.pi/2 - 10799/648000)|
        = |Real.arctan (1/60) - 10799/648000| := by
          rw [show Real.pi/2 - Real.arctan (1/60)
              - (Real.pi/2 - 10799/648000)
              = -(Real.arctan (1/60) - 10799/648000) from by ring,
            abs_neg]
      _ ≤ ((1:ℝ)/60) ^ (2 * 2 + 1) / (2 * (2:ℕ) + 1) := henc
      _ ≤ 1/10^6 := htl
  -- theta_eq at 30
  have hθ := theta_eq (T := (30:ℝ)) (by norm_num)
  have hseries : (∑' n : ℕ,
      ((30:ℝ)/((n:ℝ)+1) - 2 * Real.arctan (30/(2*((n:ℝ)+5/4)))))
      = ∑' n : ℕ, sTermT 30 n := by
    apply tsum_congr
    intro n
    rw [sTermT]
  rw [hseries] at hθ
  have h2T : (2:ℝ) * 30 = 60 := by norm_num
  rw [h2T] at hθ
  -- assemble
  obtain ⟨hAl, hAu⟩ := abs_le.mp hA
  obtain ⟨hBl, hBu⟩ := abs_le.mp hB
  obtain ⟨hTl, hTu⟩ := hTail
  obtain ⟨hγl, hγu⟩ := hγ
  obtain ⟨hπl, hπu⟩ := hlogπ
  obtain ⟨h60l, h60u⟩ := abs_le.mp h60
  rw [hB_align, hT_align] at hsplit2
  rw [abs_le]
  constructor
  · nlinarith [hθ, hsplit1, hsplit2, hAl, hBl, hTl, hγu, hπu, h60u, h60l]
  · nlinarith [hθ, hsplit1, hsplit2, hAu, hBu, hTu, hγl, hπl, h60l, h60u]

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.theta30_head_A
#print axioms CriticalLinePhasor.DVP.theta30_head_B
#print axioms CriticalLinePhasor.DVP.theta30_enclosure
end AxiomAudit
