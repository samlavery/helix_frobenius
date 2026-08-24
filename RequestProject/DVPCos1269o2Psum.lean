import RequestProject.DVPCos1269o2Table

/-!
# The cosine partial-sum floor, `t = 1269/2` (N = 1000)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 1269/2` segment certificate. -/
def cos1269o2c (n : ℕ) : ℝ := Real.cos (((1269:ℕ):ℝ) * (Real.log n / 2))

theorem psum1269o2_11 : ((1189541/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos1269o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 11 - ((1189741/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum1269o2_12 : ((605313/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos1269o2c k) + cos1269o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_11
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 12 - ((229653/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_13 : ((501307/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos1269o2c k) + cos1269o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_12
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 13 - ((397341/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_14 : ((3766299/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos1269o2c k) + cos1269o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_13
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 14 - ((-4999577/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_15 : ((1050087/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos1269o2c k) + cos1269o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_14
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 15 - ((-9813761/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_16 : ((15213903/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos1269o2c k) + cos1269o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_15
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 16 - ((2491117/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_17 : ((4594107/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos1269o2c k) + cos1269o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_16
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 17 - ((121213/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_18 : ((30291641/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos1269o2c k) + cos1269o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_17
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 18 - ((3661053/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_19 : ((6224251/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos1269o2c k) + cos1269o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_18
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 19 - ((-5393637/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_20 : ((599141/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos1269o2c k) + cos1269o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_19
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 20 - ((-9917479/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_21 : ((5517061/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos1269o2c k) + cos1269o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_20
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 21 - ((-591279/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_22 : ((11632823/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos1269o2c k) + cos1269o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_21
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 22 - ((3058381/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_23 : ((995841/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos1269o2c k) + cos1269o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_22
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 23 - ((-3326309/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_24 : ((703951/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos1269o2c k) + cos1269o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_23
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 24 - ((1820163/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_25 : ((23500547/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos1269o2c k) + cos1269o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_24
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 25 - ((9422527/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_26 : ((16727561/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos1269o2c k) + cos1269o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_25
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 26 - ((398223/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_27 : ((9514807/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos1269o2c k) + cos1269o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_26
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 27 - ((2302553/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_28 : ((14029277/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos1269o2c k) + cos1269o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_27
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 28 - ((-4999837/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_29 : ((37705297/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos1269o2c k) + cos1269o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_28
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 29 - ((9647743/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_30 : ((1745833/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos1269o2c k) + cos1269o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_29
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 30 - ((-9770969/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_31 : ((29628141/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos1269o2c k) + cos1269o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_30
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 31 - ((1695813/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_32 : ((791433/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos1269o2c k) + cos1269o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_31
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 32 - ((9944509/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_33 : ((5998959/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos1269o2c k) + cos1269o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_32
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 33 - ((4210511/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_34 : ((13969887/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos1269o2c k) + cos1269o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_33
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 34 - ((1972219/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_35 : ((65669539/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos1269o2c k) + cos1269o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_34
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 35 - ((9790991/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_36 : ((14569101/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos1269o2c k) + cos1269o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_35
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 36 - ((3588483/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_37 : ((2083707/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos1269o2c k) + cos1269o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_36
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 37 - ((-6165881/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_38 : ((61462623/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos1269o2c k) + cos1269o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_37
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 38 - ((-5215001/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_39 : ((71153963/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos1269o2c k) + cos1269o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_38
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 39 - ((484617/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_40 : ((3825667/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos1269o2c k) + cos1269o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_39
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 40 - ((-9942291/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_41 : ((17796813/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos1269o2c k) + cos1269o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_40
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 41 - ((498879/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_42 : ((61796167/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos1269o2c k) + cos1269o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_41
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 42 - ((-1878017/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_43 : ((16517879/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos1269o2c k) + cos1269o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_42
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 43 - ((4276349/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_44 : ((36176309/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos1269o2c k) + cos1269o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_43
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 44 - ((3141051/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_45 : ((63865423/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos1269o2c k) + cos1269o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_44
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 45 - ((-1697239/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_46 : ((11411099/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos1269o2c k) + cos1269o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_45
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 46 - ((-212779/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_47 : ((60298669/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos1269o2c k) + cos1269o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_46
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 47 - ((1622087/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_48 : ((4331821/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos1269o2c k) + cos1269o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_47
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 48 - ((9011467/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_49 : ((79284941/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos1269o2c k) + cos1269o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_48
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 49 - ((1995361/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_50 : ((17754989/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos1269o2c k) + cos1269o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_49
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 50 - ((2372751/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_51 : ((49135021/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos1269o2c k) + cos1269o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_50
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 51 - ((9496097/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_52 : ((108242247/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos1269o2c k) + cos1269o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_51
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 52 - ((1994641/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_53 : ((117424111/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos1269o2c k) + cos1269o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_52
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 53 - ((573929/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_54 : ((15230019/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos1269o2c k) + cos1269o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_53
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 54 - ((4417041/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_55 : ((3666959/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos1269o2c k) + cos1269o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_54
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 55 - ((-281029/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_56 : ((3354561/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos1269o2c k) + cos1269o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_55
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 56 - ((-1249467/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_57 : ((21060649/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos1269o2c k) + cos1269o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_56
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 57 - ((-2041707/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_58 : ((1437541/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos1269o2c k) + cos1269o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_57
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 58 - ((1940207/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_59 : ((57980213/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos1269o2c k) + cos1269o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_58
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 59 - ((479073/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_60 : ((53117733/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos1269o2c k) + cos1269o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_59
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 60 - ((-243099/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_61 : ((113001243/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos1269o2c k) + cos1269o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_60
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 61 - ((6766777/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_62 : ((114487389/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos1269o2c k) + cos1269o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_61
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 62 - ((743573/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_63 : ((53399893/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos1269o2c k) + cos1269o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_62
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 63 - ((-7686603/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_64 : ((116718839/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos1269o2c k) + cos1269o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_63
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 64 - ((9920053/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_65 : ((10712433/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos1269o2c k) + cos1269o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_64
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 65 - ((-9593509/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_66 : ((925249/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos1269o2c k) + cos1269o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_65
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 66 - ((1706559/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_67 : ((53893977/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos1269o2c k) + cos1269o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_66
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 67 - ((-7867171/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_68 : ((115803571/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos1269o2c k) + cos1269o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_67
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 68 - ((8016617/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_69 : ((835371/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos1269o2c k) + cos1269o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_68
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 69 - ((-8875083/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_70 : ((58379081/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos1269o2c k) + cos1269o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_69
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 70 - ((4915837/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_71 : ((107045949/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos1269o2c k) + cos1269o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_70
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 71 - ((-9711213/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_72 : ((114073589/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos1269o2c k) + cos1269o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_71
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 72 - ((43929/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_73 : ((56504867/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos1269o2c k) + cos1269o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_72
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 73 - ((-212571/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_74 : ((53338919/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos1269o2c k) + cos1269o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_73
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 74 - ((-395681/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_75 : ((116674293/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos1269o2c k) + cos1269o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_74
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 75 - ((1999491/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_76 : ((111639243/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos1269o2c k) + cos1269o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_75
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 76 - ((-100681/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_77 : ((105967121/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos1269o2c k) + cos1269o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_76
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 77 - ((-2835561/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_78 : ((28901111/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos1269o2c k) + cos1269o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_77
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 78 - ((9638323/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_79 : ((11601189/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos1269o2c k) + cos1269o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_78
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 79 - ((204223/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_80 : ((106048201/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos1269o2c k) + cos1269o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_79
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 80 - ((-9962689/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_81 : ((26797439/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos1269o2c k) + cos1269o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_80
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 81 - ((228511/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_82 : ((117178223/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos1269o2c k) + cos1269o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_81
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 82 - ((9989467/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_83 : ((118345061/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos1269o2c k) + cos1269o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_82
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 83 - ((583919/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_84 : ((681429/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos1269o2c k) + cos1269o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_83
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 84 - ((-9315421/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_85 : ((102454957/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos1269o2c k) + cos1269o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_84
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 85 - ((-6572683/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_86 : ((106538301/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos1269o2c k) + cos1269o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_85
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 86 - ((510543/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_87 : ((14561183/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos1269o2c k) + cos1269o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_86
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 87 - ((9952163/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_88 : ((122933117/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos1269o2c k) + cos1269o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_87
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 88 - ((6444653/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_89 : ((121082591/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos1269o2c k) + cos1269o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_88
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 89 - ((-924763/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_90 : ((112708749/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos1269o2c k) + cos1269o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_89
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 90 - ((-4186421/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_91 : ((102819211/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos1269o2c k) + cos1269o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_90
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 91 - ((-4944269/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_92 : ((9585647/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos1269o2c k) + cos1269o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_91
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 92 - ((-6961741/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_93 : ((93930331/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos1269o2c k) + cos1269o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_92
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 93 - ((-1925139/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_94 : ((48486431/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos1269o2c k) + cos1269o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_93
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 94 - ((3043531/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_95 : ((20743563/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos1269o2c k) + cos1269o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_94
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 95 - ((6745953/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_96 : ((56317323/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos1269o2c k) + cos1269o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_95
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 96 - ((8917831/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_97 : ((122476503/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos1269o2c k) + cos1269o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_96
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 97 - ((9842857/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_98 : ((132464437/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos1269o2c k) + cos1269o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_97
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 98 - ((4994467/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_99 : ((142252901/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos1269o2c k) + cos1269o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_98
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 99 - ((1223683/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_100 : ((30361471/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos1269o2c k) + cos1269o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_99
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 100 - ((4777727/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_101 : ((80633979/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos1269o2c k) + cos1269o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_100
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 101 - ((9461603/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_102 : ((10676687/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos1269o2c k) + cos1269o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_101
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 102 - ((4780017/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_103 : ((180617019/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos1269o2c k) + cos1269o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_102
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 103 - ((9791027/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_104 : ((95301229/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos1269o2c k) + cos1269o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_103
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 104 - ((9986439/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_105 : ((200474919/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos1269o2c k) + cos1269o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_104
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 105 - ((9873461/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_106 : ((41914211/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos1269o2c k) + cos1269o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_105
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 106 - ((568571/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_107 : ((216862633/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos1269o2c k) + cos1269o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_106
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 107 - ((3646289/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_108 : ((27636081/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos1269o2c k) + cos1269o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_107
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 108 - ((845403/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_109 : ((55274841/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos1269o2c k) + cos1269o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_108
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 109 - ((2929/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_110 : ((108207343/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos1269o2c k) + cos1269o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_109
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 110 - ((-2341839/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_111 : ((103924301/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos1269o2c k) + cos1269o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_110
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 111 - ((-2141271/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_112 : ((197860239/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos1269o2c k) + cos1269o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_111
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 112 - ((-9987363/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_113 : ((190168423/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos1269o2c k) + cos1269o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_112
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 113 - ((-120169/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_114 : ((94166223/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos1269o2c k) + cos1269o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_113
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 114 - ((-1834977/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_115 : ((96809397/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos1269o2c k) + cos1269o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_114
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 115 - ((1321837/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_116 : ((40673591/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos1269o2c k) + cos1269o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_115
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 116 - ((9750161/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_117 : ((3305431/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos1269o2c k) + cos1269o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_116
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 117 - ((8180629/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_118 : ((212294771/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos1269o2c k) + cos1269o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_117
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 118 - ((748187/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_119 : ((204755429/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos1269o2c k) + cos1269o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_118
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 119 - ((-3769171/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_120 : ((39016359/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos1269o2c k) + cos1269o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_119
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 120 - ((-4836317/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_121 : ((19215791/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos1269o2c k) + cos1269o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_120
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 121 - ((-584577/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_122 : ((19907733/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos1269o2c k) + cos1269o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_121
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 122 - ((346021/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_123 : ((13039891/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos1269o2c k) + cos1269o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_122
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 123 - ((4780963/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_124 : ((2099157/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos1269o2c k) + cos1269o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_123
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 124 - ((319611/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_125 : ((100599099/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos1269o2c k) + cos1269o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_124
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 125 - ((-4358251/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_126 : ((193647087/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos1269o2c k) + cos1269o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_125
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 126 - ((-7550111/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_127 : ((7905921/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos1269o2c k) + cos1269o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_126
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 127 - ((2000969/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_128 : ((51884571/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos1269o2c k) + cos1269o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_127
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 128 - ((9891259/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_129 : ((208314599/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos1269o2c k) + cos1269o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_128
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 129 - ((155463/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_130 : ((198662753/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos1269o2c k) + cos1269o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_129
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 130 - ((-4825423/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_131 : ((194632131/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos1269o2c k) + cos1269o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_130
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 131 - ((-2014811/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_132 : ((20327191/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos1269o2c k) + cos1269o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_131
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 132 - ((8640779/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_133 : ((6529643/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos1269o2c k) + cos1269o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_132
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 133 - ((2838833/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_134 : ((50237971/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos1269o2c k) + cos1269o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_133
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 134 - ((-1998923/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_135 : ((3898091/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos1269o2c k) + cos1269o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_134
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 135 - ((-3023167/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_136 : ((50761179/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos1269o2c k) + cos1269o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_135
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 136 - ((4070583/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_137 : ((41663669/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos1269o2c k) + cos1269o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_136
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 137 - ((5274629/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_138 : ((199346857/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos1269o2c k) + cos1269o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_137
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 138 - ((-1121311/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_139 : ((196137213/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos1269o2c k) + cos1269o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_138
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 139 - ((-802161/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_140 : ((206004203/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos1269o2c k) + cos1269o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_139
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 140 - ((986799/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_141 : ((205665943/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos1269o2c k) + cos1269o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_140
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 141 - ((-16863/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_142 : ((2450077/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos1269o2c k) + cos1269o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_141
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 142 - ((-9658783/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_143 : ((200988749/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos1269o2c k) + cos1269o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_142
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 143 - ((4983589/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_144 : ((207864481/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos1269o2c k) + cos1269o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_143
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 144 - ((1719183/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_145 : ((39760601/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos1269o2c k) + cos1269o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_144
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 145 - ((-2265119/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_146 : ((197948907/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos1269o2c k) + cos1269o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_145
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 146 - ((-426549/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_147 : ((103756593/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos1269o2c k) + cos1269o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_146
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 147 - ((9565279/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_148 : ((40203917/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos1269o2c k) + cos1269o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_147
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 148 - ((-6492601/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_149 : ((9844959/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos1269o2c k) + cos1269o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_148
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 149 - ((-823881/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_150 : ((206888633/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos1269o2c k) + cos1269o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_149
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 150 - ((9990453/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_151 : ((40349101/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos1269o2c k) + cos1269o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_150
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 151 - ((-321383/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_152 : ((196893641/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos1269o2c k) + cos1269o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_151
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 152 - ((-303179/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_153 : ((103441201/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos1269o2c k) + cos1269o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_152
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 153 - ((9989761/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_154 : ((40207597/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos1269o2c k) + cos1269o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_153
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 154 - ((-5843417/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_155 : ((197691369/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos1269o2c k) + cos1269o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_154
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 155 - ((-209101/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_156 : ((103635197/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos1269o2c k) + cos1269o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_155
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 156 - ((383201/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_157 : ((9957081/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos1269o2c k) + cos1269o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_156
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 157 - ((-4063887/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_158 : ((39951903/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos1269o2c k) + cos1269o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_157
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 158 - ((123779/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_159 : ((103464873/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos1269o2c k) + cos1269o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_158
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 159 - ((7171231/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_160 : ((49237521/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos1269o2c k) + cos1269o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_159
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 160 - ((-4989331/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_161 : ((50835927/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos1269o2c k) + cos1269o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_160
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 161 - ((49958/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_162 : ((102137837/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos1269o2c k) + cos1269o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_161
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 162 - ((466483/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_163 : ((245899/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos1269o2c k) + cos1269o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_162
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 163 - ((-3777737/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_164 : ((103357559/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos1269o2c k) + cos1269o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_163
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 164 - ((4998459/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_165 : ((318931/16000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos1269o2c k) + cos1269o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_164
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 165 - ((-7382243/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_166 : ((50177089/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos1269o2c k) + cos1269o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_165
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 166 - ((1377481/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_167 : ((102886047/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos1269o2c k) + cos1269o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_166
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 167 - ((2532369/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_168 : ((98267243/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos1269o2c k) + cos1269o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_167
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 168 - ((-72161/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_169 : ((206268397/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos1269o2c k) + cos1269o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_168
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 169 - ((9734911/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_170 : ((99768683/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos1269o2c k) + cos1269o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_169
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 170 - ((-6730031/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_171 : ((201114227/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos1269o2c k) + cos1269o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_170
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 171 - ((1577861/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_172 : ((102502163/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos1269o2c k) + cos1269o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_171
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 172 - ((3891099/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_173 : ((19694943/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos1269o2c k) + cos1269o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_172
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 173 - ((-1006737/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_174 : ((103438861/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos1269o2c k) + cos1269o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_173
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 174 - ((2482323/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_175 : ((197573653/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos1269o2c k) + cos1269o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_174
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 175 - ((-9303069/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_176 : ((3190273/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos1269o2c k) + cos1269o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_175
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 176 - ((6604819/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_177 : ((100763723/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos1269o2c k) + cos1269o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_176
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 177 - ((-1324513/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_178 : ((199884411/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos1269o2c k) + cos1269o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_177
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 178 - ((-328407/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_179 : ((102673527/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos1269o2c k) + cos1269o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_178
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 179 - ((5463643/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_180 : ((49272571/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos1269o2c k) + cos1269o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_179
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 180 - ((-825577/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_181 : ((41367039/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos1269o2c k) + cos1269o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_180
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 181 - ((9745911/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_182 : ((98458219/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos1269o2c k) + cos1269o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_181
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 182 - ((-9917757/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_183 : ((51465103/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos1269o2c k) + cos1269o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_182
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 183 - ((4472487/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_184 : ((3974959/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos1269o2c k) + cos1269o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_183
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 184 - ((-3555731/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_185 : ((203485527/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos1269o2c k) + cos1269o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_184
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 185 - ((4738577/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_186 : ((100676521/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos1269o2c k) + cos1269o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_185
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 186 - ((-426297/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_187 : ((200894203/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos1269o2c k) + cos1269o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_186
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 187 - ((-457839/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_188 : ((203735339/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos1269o2c k) + cos1269o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_187
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 188 - ((355267/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_189 : ((497073/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos1269o2c k) + cos1269o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_188
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 189 - ((-4905139/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_190 : ((51354277/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos1269o2c k) + cos1269o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_189
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 190 - ((1647227/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_191 : ((197530317/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos1269o2c k) + cos1269o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_190
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 191 - ((-7885791/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_192 : ((206349827/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos1269o2c k) + cos1269o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_191
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 192 - ((882051/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_193 : ((39381663/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos1269o2c k) + cos1269o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_192
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 193 - ((-73754/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_194 : ((103355389/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos1269o2c k) + cos1269o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_193
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 194 - ((9803463/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_195 : ((196740153/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos1269o2c k) + cos1269o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_194
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 195 - ((-79757/80000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_196 : ((206735779/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos1269o2c k) + cos1269o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_195
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 196 - ((4998313/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_197 : ((49199757/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos1269o2c k) + cos1269o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_196
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 197 - ((-9935751/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_198 : ((206628329/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos1269o2c k) + cos1269o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_197
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 198 - ((9830301/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_199 : ((196912479/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos1269o2c k) + cos1269o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_198
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 199 - ((-194297/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_200 : ((206526939/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos1269o2c k) + cos1269o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_199
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 200 - ((480773/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_201 : ((98488151/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos1269o2c k) + cos1269o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_200
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 201 - ((-9549637/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_202 : ((41300641/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos1269o2c k) + cos1269o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_201
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 202 - ((9527903/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_203 : ((196949603/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos1269o2c k) + cos1269o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_202
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 203 - ((-4776301/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_204 : ((103284251/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos1269o2c k) + cos1269o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_203
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 204 - ((9619899/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_205 : ((98424353/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos1269o2c k) + cos1269o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_204
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 205 - ((-2429699/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_206 : ((206679411/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos1269o2c k) + cos1269o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_205
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 206 - ((1966341/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_207 : ((196744187/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos1269o2c k) + cos1269o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_206
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 207 - ((-620889/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_208 : ((206738379/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos1269o2c k) + cos1269o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_207
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 208 - ((1249399/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_209 : ((196760079/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos1269o2c k) + cos1269o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_208
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 209 - ((-99773/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_210 : ((206596933/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos1269o2c k) + cos1269o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_209
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 210 - ((4918927/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_211 : ((49266373/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos1269o2c k) + cos1269o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_210
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 211 - ((-9530441/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_212 : ((12879507/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos1269o2c k) + cos1269o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_211
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 212 - ((450381/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_213 : ((197845947/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos1269o2c k) + cos1269o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_212
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 213 - ((-1645033/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_214 : ((102495863/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos1269o2c k) + cos1269o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_213
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 214 - ((7146779/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_215 : ((199240679/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos1269o2c k) + cos1269o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_214
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 215 - ((-5750047/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_216 : ((203274791/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos1269o2c k) + cos1269o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_215
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 216 - ((504389/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_217 : ((402487/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos1269o2c k) + cos1269o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_216
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 217 - ((-2030291/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_218 : ((100521749/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos1269o2c k) + cos1269o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_217
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 218 - ((-99501/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_219 : ((20358989/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos1269o2c k) + cos1269o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_218
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 219 - ((39803/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_220 : ((99360039/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos1269o2c k) + cos1269o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_219
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 220 - ((-1217203/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_221 : ((205698527/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos1269o2c k) + cos1269o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_220
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 221 - ((6979449/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_222 : ((24628159/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos1269o2c k) + cos1269o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_221
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 222 - ((-1734451/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_223 : ((206757969/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos1269o2c k) + cos1269o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_222
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 223 - ((9733697/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_224 : ((196782413/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos1269o2c k) + cos1269o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_223
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 224 - ((-2493639/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_225 : ((206043273/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos1269o2c k) + cos1269o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_224
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 225 - ((463093/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_226 : ((198488051/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos1269o2c k) + cos1269o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_225
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 226 - ((-3777111/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_227 : ((25427697/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos1269o2c k) + cos1269o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_226
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 227 - ((197381/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_228 : ((25224143/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos1269o2c k) + cos1269o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_227
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 228 - ((-203429/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_229 : ((39958549/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos1269o2c k) + cos1269o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_228
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 229 - ((-1999399/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_230 : ((51314193/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos1269o2c k) + cos1269o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_229
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 230 - ((5465027/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_231 : ((197023569/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos1269o2c k) + cos1269o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_230
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 231 - ((-8232203/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_232 : ((51704343/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos1269o2c k) + cos1269o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_231
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 232 - ((9794803/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_233 : ((197035261/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos1269o2c k) + cos1269o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_232
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 233 - ((-9781111/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_234 : ((41018377/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos1269o2c k) + cos1269o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_233
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 234 - ((1007203/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_235 : ((50071677/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos1269o2c k) + cos1269o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_234
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 235 - ((-4804177/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_236 : ((50205901/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos1269o2c k) + cos1269o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_235
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 236 - ((67237/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_237 : ((204762063/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos1269o2c k) + cos1269o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_236
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 237 - ((3939459/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_238 : ((197085941/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos1269o2c k) + cos1269o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_237
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 238 - ((-3837561/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_239 : ((6464233/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos1269o2c k) + cos1269o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_238
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 239 - ((1954103/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_240 : ((49309361/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos1269o2c k) + cos1269o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_239
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 240 - ((-2404253/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_241 : ((8173543/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos1269o2c k) + cos1269o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_240
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 241 - ((7102131/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_242 : ((50404213/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos1269o2c k) + cos1269o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_241
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 242 - ((-2720723/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_243 : ((49786521/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos1269o2c k) + cos1269o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_242
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 243 - ((-308721/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_244 : ((103108037/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos1269o2c k) + cos1269o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_243
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 244 - ((707099/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_245 : ((196499061/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos1269o2c k) + cos1269o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_244
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 245 - ((-9716013/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_246 : ((10299809/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos1269o2c k) + cos1269o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_245
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 246 - ((9498119/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_247 : ((199667823/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos1269o2c k) + cos1269o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_246
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 247 - ((-6327357/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_248 : ((50183999/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos1269o2c k) + cos1269o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_247
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 248 - ((1069173/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_249 : ((205363243/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos1269o2c k) + cos1269o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_248
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 249 - ((4628247/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_250 : ((196544399/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos1269o2c k) + cos1269o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_249
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 250 - ((-2204461/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_251 : ((103237221/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 251, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 251, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 250, cos1269o2c k) + cos1269o2c 251 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 250) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_250
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 251 - ((9931043/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_251).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_252 : ((99531801/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 252, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 252, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 251, cos1269o2c k) + cos1269o2c 252 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 251) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_251
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 252 - ((-92623/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_252).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_253 : ((201106259/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 253, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 253, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 252, cos1269o2c k) + cos1269o2c 253 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 252) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_252
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 253 - ((2043657/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_253).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_254 : ((102649707/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 254, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 254, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 253, cos1269o2c k) + cos1269o2c 254 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 253) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_253
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 254 - ((838831/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_254).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_255 : ((24559117/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 255, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 255, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 254, cos1269o2c k) + cos1269o2c 255 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 254) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_254
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 255 - ((-4412739/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_255).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_256 : ((25791251/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 256, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 256, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 255, cos1269o2c k) + cos1269o2c 256 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 255) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_255
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 256 - ((1232259/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_256).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_257 : ((99814591/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 257, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 257, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 256, cos1269o2c k) + cos1269o2c 257 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 256) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_256
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 257 - ((-3349913/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_257).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_258 : ((100097307/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 258, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 258, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 257, cos1269o2c k) + cos1269o2c 258 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 257) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_257
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 258 - ((17701/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_258).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_259 : ((206087937/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 259, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 259, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 258, cos1269o2c k) + cos1269o2c 259 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 258) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_258
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 259 - ((5894323/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_259).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_260 : ((196383039/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 260, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 260, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 259, cos1269o2c k) + cos1269o2c 260 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 259) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_259
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 260 - ((-4851949/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_260).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_261 : ((51333509/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 261, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 261, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 260, cos1269o2c k) + cos1269o2c 261 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 260) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_260
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 261 - ((8951997/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_261).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_262 : ((201497159/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 262, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 262, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 261, cos1269o2c k) + cos1269o2c 262 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 261) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_261
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 262 - ((-3835877/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_262).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_263 : ((99124143/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 263, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 263, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 262, cos1269o2c k) + cos1269o2c 263 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 262) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_262
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 263 - ((-3247873/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_263).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_264 : ((206992211/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 264, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 264, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 263, cos1269o2c k) + cos1269o2c 264 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 263) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_263
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 264 - ((349797/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_264).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_265 : ((7890767/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 265, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 265, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 264, cos1269o2c k) + cos1269o2c 265 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 264) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_264
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 265 - ((-2430509/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_265).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_266 : ((101385561/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 266, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 266, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 265, cos1269o2c k) + cos1269o2c 266 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 265) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_265
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 266 - ((5502947/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_266).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_267 : ((102270571/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 267, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 267, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 266, cos1269o2c k) + cos1269o2c 267 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 266) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_266
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 267 - ((88551/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_267).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_268 : ((196419489/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 268, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 268, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 267, cos1269o2c k) + cos1269o2c 268 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 267) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_267
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 268 - ((-8120653/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_268).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_269 : ((51574517/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 269, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 269, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 268, cos1269o2c k) + cos1269o2c 269 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 268) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_268
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 269 - ((9879579/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_269).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_270 : ((25052489/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 270, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 270, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 269, cos1269o2c k) + cos1269o2c 270 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 269) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_269
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 270 - ((-1469289/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_270).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_271 : ((99374993/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 271, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 271, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 270, cos1269o2c k) + cos1269o2c 271 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 270) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_270
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 271 - ((-834463/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_271).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_272 : ((207010707/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 272, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 272, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 271, cos1269o2c k) + cos1269o2c 272 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 271) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_271
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 272 - ((8261721/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_272).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_273 : ((197239199/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 273, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 273, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 272, cos1269o2c k) + cos1269o2c 273 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 272) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_272
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 273 - ((-2442627/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_273).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_274 : ((202332637/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 274, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 274, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 273, cos1269o2c k) + cos1269o2c 274 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 273) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_273
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 274 - ((2547219/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_274).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_275 : ((12827819/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 275, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 275, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 274, cos1269o2c k) + cos1269o2c 275 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 274) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_274
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 275 - ((2913467/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_275).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_276 : ((39236497/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 276, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 276, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 275, cos1269o2c k) + cos1269o2c 276 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 275) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_275
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 276 - ((-9061619/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_276).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_277 : ((205352219/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 277, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 277, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 276, cos1269o2c k) + cos1269o2c 277 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 276) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_276
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 277 - ((4585367/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_277).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_278 : ((101171431/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 278, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 278, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 277, cos1269o2c k) + cos1269o2c 278 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 277) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_277
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 278 - ((-3008357/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_278).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_279 : ((98524377/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 279, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 279, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 278, cos1269o2c k) + cos1269o2c 279 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 278) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_278
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 279 - ((-1323277/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_279).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_280 : ((103473839/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 280, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 280, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 279, cos1269o2c k) + cos1269o2c 280 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 279) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_279
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 280 - ((2474981/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_280).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_281 : ((199548569/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 281, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 281, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 280, cos1269o2c k) + cos1269o2c 281 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 280) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_280
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 281 - ((-7398109/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_281).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_282 : ((49749947/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 282, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 282, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 281, cos1269o2c k) + cos1269o2c 282 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 281) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_281
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 282 - ((-547781/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_282).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_283 : ((207135241/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 283, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 283, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 282, cos1269o2c k) + cos1269o2c 283 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 282) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_282
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 283 - ((8136453/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_283).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_284 : ((197532177/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 284, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 284, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 283, cos1269o2c k) + cos1269o2c 284 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 283) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_283
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 284 - ((-600129/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_284).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_285 : ((50301619/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 285, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 285, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 284, cos1269o2c k) + cos1269o2c 285 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 284) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_284
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 285 - ((3675299/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_285).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_286 : ((103185321/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 286, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 286, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 285, cos1269o2c k) + cos1269o2c 286 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 285) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_285
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 286 - ((2582583/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_286).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_287 : ((196420689/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 287, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 287, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 286, cos1269o2c k) + cos1269o2c 287 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 286) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_286
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 287 - ((-9948953/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_287).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_288 : ((20314191/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 288, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 288, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 287, cos1269o2c k) + cos1269o2c 288 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 287) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_287
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 288 - ((6722221/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_288).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_289 : ((20517739/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 289, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 289, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 288, cos1269o2c k) + cos1269o2c 289 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 288) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_288
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 289 - ((3182/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_289).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_290 : ((49007189/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 290, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 290, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 289, cos1269o2c k) + cos1269o2c 290 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 289) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_289
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 290 - ((-4573817/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_290).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_291 : ((40919343/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 291, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 291, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 290, cos1269o2c k) + cos1269o2c 291 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 290) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_290
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 291 - ((8568959/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_291).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_292 : ((101976377/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 292, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 292, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 291, cos1269o2c k) + cos1269o2c 292 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 291) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_291
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 292 - ((-642961/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_292).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_293 : ((98034431/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 293, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 293, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 292, cos1269o2c k) + cos1269o2c 293 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 292) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_292
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 293 - ((-1970723/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_293).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_294 : ((51392391/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 294, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 294, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 293, cos1269o2c k) + cos1269o2c 294 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 293) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_293
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 294 - ((4750851/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_294).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_295 : ((101466549/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 295, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 295, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 294, cos1269o2c k) + cos1269o2c 295 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 294) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_294
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 295 - ((-1317733/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_295).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_296 : ((49070169/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 296, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 296, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 295, cos1269o2c k) + cos1269o2c 296 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 295) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_295
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 296 - ((-3325711/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_296).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_297 : ((51538581/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 297, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 297, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 296, cos1269o2c k) + cos1269o2c 297 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 296) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_296
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 297 - ((1234331/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_297).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_298 : ((202227423/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 298, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 298, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 297, cos1269o2c k) + cos1269o2c 298 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 297) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_297
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 298 - ((-3925901/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_298).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_299 : ((24559651/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 299, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 299, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 298, cos1269o2c k) + cos1269o2c 299 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 298) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_298
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 299 - ((-1149843/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_299).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_300 : ((103227619/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 300, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 300, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 299, cos1269o2c k) + cos1269o2c 300 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 299) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_299
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 300 - ((997903/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_300).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_301 : ((201872671/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 301, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 301, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 300, cos1269o2c k) + cos1269o2c 301 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 300) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_300
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 301 - ((-4581567/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_301).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_302 : ((98274981/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 302, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 302, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 301, cos1269o2c k) + cos1269o2c 302 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 301) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_301
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 302 - ((-5321709/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_302).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_303 : ((51635759/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 303, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 303, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 302, cos1269o2c k) + cos1269o2c 303 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 302) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_302
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 303 - ((4997037/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_303).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_304 : ((201876513/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 304, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 304, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 303, cos1269o2c k) + cos1269o2c 304 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 303) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_303
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 304 - ((-4665523/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_304).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_305 : ((196458113/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 305, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 305, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 304, cos1269o2c k) + cos1269o2c 305 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 304) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_304
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 305 - ((-27087/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_305).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_306 : ((206435123/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 306, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 306, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 305, cos1269o2c k) + cos1269o2c 306 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 305) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_305
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 306 - ((997801/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_306).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_307 : ((12639889/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 307, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 307, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 306, cos1269o2c k) + cos1269o2c 307 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 306) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_306
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 307 - ((-4195899/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_307).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_308 : ((490559/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 308, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 308, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 307, cos1269o2c k) + cos1269o2c 308 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 307) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_307
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 308 - ((-751703/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_308).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_309 : ((103048017/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 309, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 309, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 308, cos1269o2c k) + cos1269o2c 309 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 308) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_308
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 309 - ((4936717/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_309).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_310 : ((25368667/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 310, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 310, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 309, cos1269o2c k) + cos1269o2c 310 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 309) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_309
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 310 - ((-1572849/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_310).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_311 : ((97964691/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 311, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 311, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 310, cos1269o2c k) + cos1269o2c 311 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 310) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_310
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 311 - ((-3509477/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_311).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_312 : ((10272283/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 312, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 312, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 311, cos1269o2c k) + cos1269o2c 312 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 311) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_311
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 312 - ((4758639/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_312).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_313 : ((101986887/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 313, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 313, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 312, cos1269o2c k) + cos1269o2c 313 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 312) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_312
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 313 - ((-735443/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_313).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_314 : ((195723689/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 314, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 314, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 313, cos1269o2c k) + cos1269o2c 314 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 313) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_313
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 314 - ((-1649817/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_314).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_315 : ((204384351/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 315, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 315, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 314, cos1269o2c k) + cos1269o2c 315 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 314) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_314
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 315 - ((4330831/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_315).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_316 : ((10260621/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 316, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 316, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 315, cos1269o2c k) + cos1269o2c 316 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 315) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_315
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 316 - ((829069/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_316).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_317 : ((195820797/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 317, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 317, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 316, cos1269o2c k) + cos1269o2c 317 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 316) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_316
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 317 - ((-9390623/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_317).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_318 : ((202842127/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 318, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 318, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 317, cos1269o2c k) + cos1269o2c 318 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 317) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_317
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 318 - ((702233/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_318).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_319 : ((103232651/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 319, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 319, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 318, cos1269o2c k) + cos1269o2c 319 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 318) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_318
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 319 - ((144967/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_319).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_320 : ((196474069/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 320, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 320, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 319, cos1269o2c k) + cos1269o2c 320 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 319) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_319
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 320 - ((-9990233/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_320).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_321 : ((3138301/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 321, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 321, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 320, cos1269o2c k) + cos1269o2c 321 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 320) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_320
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 321 - ((875639/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_321).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_322 : ((207405471/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 322, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 322, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 321, cos1269o2c k) + cos1269o2c 322 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 321) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_321
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 322 - ((6555207/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_322).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_323 : ((197906503/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 323, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 323, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 322, cos1269o2c k) + cos1269o2c 323 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 322) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_322
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 323 - ((-593623/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_323).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_324 : ((99314233/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 324, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 324, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 323, cos1269o2c k) + cos1269o2c 324 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 323) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_323
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 324 - ((722963/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_324).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_325 : ((207601983/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 325, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 325, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 324, cos1269o2c k) + cos1269o2c 325 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 324) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_324
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 325 - ((8974517/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_325).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_326 : ((4003713/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 326, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 326, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 325, cos1269o2c k) + cos1269o2c 326 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 325) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_325
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 326 - ((-7415333/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_326).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_327 : ((39326969/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 327, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 327, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 326, cos1269o2c k) + cos1269o2c 327 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 326) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_326
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 327 - ((-709961/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_327).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_328 : ((103316887/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 328, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 328, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 327, cos1269o2c k) + cos1269o2c 328 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 327) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_327
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 328 - ((9999929/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_328).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_329 : ((406137/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 329, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 329, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 328, cos1269o2c k) + cos1269o2c 329 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 328) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_328
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 329 - ((-1782137/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_329).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_330 : ((195544757/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 330, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 330, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 329, cos1269o2c k) + cos1269o2c 330 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 329) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_329
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 330 - ((-7522743/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_330).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_331 : ((1596153/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 331, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 331, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 330, cos1269o2c k) + cos1269o2c 331 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 330) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_330
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 331 - ((8763827/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_331).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_332 : ((102946233/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 332, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 332, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 331, cos1269o2c k) + cos1269o2c 332 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 331) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_331
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 332 - ((792941/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_332).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_333 : ((98024913/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 333, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 333, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 332, cos1269o2c k) + cos1269o2c 333 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 332) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_332
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 333 - ((-246041/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_333).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_334 : ((40186039/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 334, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 334, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 333, cos1269o2c k) + cos1269o2c 334 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 333) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_333
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 334 - ((4881369/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_334).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_335 : ((1297707/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 335, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 335, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 334, cos1269o2c k) + cos1269o2c 335 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 334) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_334
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 335 - ((268157/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_335).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_336 : ((198478311/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 336, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 336, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 335, cos1269o2c k) + cos1269o2c 336 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 335) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_335
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 336 - ((-9153809/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_336).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_337 : ((49370907/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 337, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 337, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 336, cos1269o2c k) + cos1269o2c 337 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 336) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_336
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 337 - ((-993683/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_337).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_338 : ((41452741/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 338, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 338, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 337, cos1269o2c k) + cos1269o2c 338 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 337) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_337
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 338 - ((9781077/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_338).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_339 : ((101175913/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 339, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 339, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 338, cos1269o2c k) + cos1269o2c 339 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 338) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_338
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 339 - ((-4910879/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_339).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_340 : ((48866609/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 340, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 340, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 339, cos1269o2c k) + cos1269o2c 340 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 339) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_339
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 340 - ((-688439/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_340).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_341 : ((102197937/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 341, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 341, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 340, cos1269o2c k) + cos1269o2c 341 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 340) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_340
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 341 - ((4465219/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_341).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_342 : ((206180461/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 342, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 342, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 341, cos1269o2c k) + cos1269o2c 342 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 341) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_341
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 342 - ((1785587/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_342).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_343 : ((24528959/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 343, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 343, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 342, cos1269o2c k) + cos1269o2c 343 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 342) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_342
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 343 - ((-9947789/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_343).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_344 : ((199926797/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 344, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 344, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 343, cos1269o2c k) + cos1269o2c 344 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 343) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_343
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 344 - ((29569/80000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_344).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_345 : ((5197223/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 345, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 345, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 344, cos1269o2c k) + cos1269o2c 345 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 344) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_344
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 345 - ((7963123/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_345).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_346 : ((199960713/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 346, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 346, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 345, cos1269o2c k) + cos1269o2c 346 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 345) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_345
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 346 - ((-7927207/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_346).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_347 : ((12256881/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 347, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 347, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 346, cos1269o2c k) + cos1269o2c 347 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 346) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_346
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 347 - ((-3849617/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_347).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_348 : ((206011169/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 348, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 348, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 347, cos1269o2c k) + cos1269o2c 348 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 347) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_347
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 348 - ((9902073/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_348).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_349 : ((102456991/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 349, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 349, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 348, cos1269o2c k) + cos1269o2c 349 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 348) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_348
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 349 - ((-1096187/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_349).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_350 : ((48883673/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 350, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 350, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 349, cos1269o2c k) + cos1269o2c 350 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 349) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_349
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 350 - ((-937829/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_350).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_351 : ((201130247/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 351, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 351, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 350, cos1269o2c k) + cos1269o2c 351 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 350) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_350
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 351 - ((1119311/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_351).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_352 : ((207890813/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 352, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 352, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 351, cos1269o2c k) + cos1269o2c 352 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 351) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_351
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 352 - ((3380783/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_352).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_353 : ((12448663/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 353, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 353, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 352, cos1269o2c k) + cos1269o2c 353 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 352) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_352
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 353 - ((-1742241/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_353).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_354 : ((98162991/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 354, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 354, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 353, cos1269o2c k) + cos1269o2c 354 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 353) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_353
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 354 - ((-1425813/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_354).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_355 : ((20630037/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 355, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 355, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 354, cos1269o2c k) + cos1269o2c 355 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 354) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_354
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 355 - ((2493847/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_355).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_356 : ((40973111/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 356, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 356, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 355, cos1269o2c k) + cos1269o2c 356 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 355) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_355
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 356 - ((-286763/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_356).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_357 : ((195480651/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 357, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 357, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 356, cos1269o2c k) + cos1269o2c 357 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 356) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_356
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 357 - ((-293247/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_357).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_358 : ((100382529/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 358, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 358, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 357, cos1269o2c k) + cos1269o2c 358 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 357) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_357
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 358 - ((5285407/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_358).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_359 : ((208040201/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 359, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 359, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 358, cos1269o2c k) + cos1269o2c 359 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 358) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_358
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 359 - ((7276143/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_359).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_360 : ((24988021/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 360, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 360, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 359, cos1269o2c k) + cos1269o2c 360 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 359) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_359
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 360 - ((-8135033/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_360).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_361 : ((195721719/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 361, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 361, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 360, cos1269o2c k) + cos1269o2c 361 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 360) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_360
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 361 - ((-4181449/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_361).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_362 : ((51354317/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 362, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 362, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 361, cos1269o2c k) + cos1269o2c 362 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 361) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_361
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 362 - ((9696549/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_362).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_363 : ((103045107/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 363, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 363, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 362, cos1269o2c k) + cos1269o2c 363 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 362) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_362
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 363 - ((336973/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_363).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_364 : ((19614669/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 364, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 364, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 363, cos1269o2c k) + cos1269o2c 364 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 363) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_363
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 364 - ((-2485631/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_364).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_365 : ((24860317/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 365, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 365, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 364, cos1269o2c k) + cos1269o2c 365 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 364) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_364
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 365 - ((1368423/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_365).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_366 : ((207918729/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 366, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 366, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 365, cos1269o2c k) + cos1269o2c 366 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 365) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_365
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 366 - ((9037193/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_366).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_367 : ((202247769/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 367, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 367, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 366, cos1269o2c k) + cos1269o2c 367 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 366) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_366
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 367 - ((-141749/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_367).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_368 : ((24373593/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 368, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 368, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 367, cos1269o2c k) + cos1269o2c 368 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 367) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_367
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 368 - ((-290321/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_368).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_369 : ((101440293/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 369, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 369, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 368, cos1269o2c k) + cos1269o2c 369 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 368) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_368
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 369 - ((3946421/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_369).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_370 : ((207802667/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 370, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 370, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 369, cos1269o2c k) + cos1269o2c 370 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 369) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_369
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 370 - ((4923081/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_370).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_371 : ((99244679/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 371, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 371, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 370, cos1269o2c k) + cos1269o2c 371 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 370) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_370
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 371 - ((-9312309/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_371).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_372 : ((12259467/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 372, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 372, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 371, cos1269o2c k) + cos1269o2c 372 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 371) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_371
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 372 - ((-1168443/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_372).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_373 : ((103048589/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 373, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 373, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 372, cos1269o2c k) + cos1269o2c 373 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 372) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_372
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 373 - ((4973353/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_373).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_374 : ((205849569/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 374, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 374, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 373, cos1269o2c k) + cos1269o2c 374 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 373) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_373
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 374 - ((-246609/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_374).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_375 : ((1530923/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 375, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 375, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 374, cos1269o2c k) + cos1269o2c 375 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 374) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_374
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 375 - ((-395617/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_375).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_376 : ((198596623/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 376, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 376, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 375, cos1269o2c k) + cos1269o2c 376 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 375) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_375
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 376 - ((2639479/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_376).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_377 : ((103938257/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 377, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 377, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 376, cos1269o2c k) + cos1269o2c 377 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 376) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_376
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 377 - ((9280891/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_377).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_378 : ((3174307/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 378, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 378, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 377, cos1269o2c k) + cos1269o2c 378 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 377) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_377
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 378 - ((-2359933/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_378).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_379 : ((48721321/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 379, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 379, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 378, cos1269o2c k) + cos1269o2c 379 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 378) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_378
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 379 - ((-2067341/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_379).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_380 : ((10065661/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 380, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 380, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 379, cos1269o2c k) + cos1269o2c 380 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 379) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_379
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 380 - ((803617/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_380).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_381 : ((52078761/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 381, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 381, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 380, cos1269o2c k) + cos1269o2c 381 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 380) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_380
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 381 - ((875353/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_381).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_382 : ((10027979/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 382, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 382, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 381, cos1269o2c k) + cos1269o2c 382 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 381) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_381
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 382 - ((-242327/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_382).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_383 : ((194950201/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 383, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 383, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 382, cos1269o2c k) + cos1269o2c 383 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 382) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_382
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 383 - ((-5608379/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_383).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_384 : ((203668473/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 384, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 384, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 383, cos1269o2c k) + cos1269o2c 384 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 383) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_383
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 384 - ((1089909/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_384).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_385 : ((51964179/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 385, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 385, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 384, cos1269o2c k) + cos1269o2c 385 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 384) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_384
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 385 - ((4189243/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_385).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_386 : ((99243397/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 386, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 386, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 385, cos1269o2c k) + cos1269o2c 386 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 385) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_385
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 386 - ((-4684461/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_386).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_387 : ((48915393/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 387, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 387, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 386, cos1269o2c k) + cos1269o2c 387 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 386) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_386
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 387 - ((-1412111/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_387).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_388 : ((205420287/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 388, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 388, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 387, cos1269o2c k) + cos1269o2c 388 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 387) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_387
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 388 - ((1951943/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_388).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_389 : ((206985351/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 389, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 389, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 388, cos1269o2c k) + cos1269o2c 389 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 388) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_388
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 389 - ((97879/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_389).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_390 : ((3940667/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 390, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 390, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 389, cos1269o2c k) + cos1269o2c 390 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 389) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_389
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 390 - ((-9951001/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_390).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_391 : ((49145617/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 391, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 391, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 390, cos1269o2c k) + cos1269o2c 391 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 390) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_390
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 391 - ((-224941/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_391).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_392 : ((51645337/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 392, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 392, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 391, cos1269o2c k) + cos1269o2c 392 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 391) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_391
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 392 - ((249997/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_392).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_393 : ((206073701/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 393, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 393, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 392, cos1269o2c k) + cos1269o2c 393 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 392) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_392
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 393 - ((-506647/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_393).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_394 : ((196115309/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 394, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 394, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 393, cos1269o2c k) + cos1269o2c 394 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 393) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_393
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 394 - ((-622337/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_394).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_395 : ((49352363/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 395, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 395, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 394, cos1269o2c k) + cos1269o2c 395 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 394) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_394
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 395 - ((1295143/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_395).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_396 : ((8291009/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 396, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 396, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 395, cos1269o2c k) + cos1269o2c 396 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 395) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_395
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 396 - ((9866773/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_396).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_397 : ((41071573/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 397, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 397, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 396, cos1269o2c k) + cos1269o2c 397 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 396) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_396
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 397 - ((-47909/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_397).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_398 : ((195594211/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 398, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 398, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 397, cos1269o2c k) + cos1269o2c 398 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 397) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_397
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 398 - ((-4881327/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_398).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_399 : ((197967571/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 399, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 399, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 398, cos1269o2c k) + cos1269o2c 399 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 398) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_398
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 399 - ((59359/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_399).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_400 : ((25954721/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 400, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 400, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 399, cos1269o2c k) + cos1269o2c 400 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 399) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_399
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 400 - ((9671197/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_400).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_401 : ((40992671/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 401, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 401, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 400, cos1269o2c k) + cos1269o2c 401 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 400) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_400
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 401 - ((-2673413/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_401).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_402 : ((97676069/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 402, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 402, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 401, cos1269o2c k) + cos1269o2c 402 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 401) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_401
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 402 - ((-9610217/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_402).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_403 : ((6192807/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 403, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 403, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 402, cos1269o2c k) + cos1269o2c 403 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 402) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_402
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 403 - ((1409343/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_403).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_404 : ((207758591/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 404, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 404, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 403, cos1269o2c k) + cos1269o2c 404 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 403) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_403
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 404 - ((9589767/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_404).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_405 : ((102471853/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 405, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 405, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 404, cos1269o2c k) + cos1269o2c 405 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 404) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_404
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 405 - ((-562777/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_405).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_406 : ((97664951/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 406, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 406, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 405, cos1269o2c k) + cos1269o2c 406 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 405) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_405
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 406 - ((-2403201/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_406).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_407 : ((19798907/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 407, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 407, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 406, cos1269o2c k) + cos1269o2c 407 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 406) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_406
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 407 - ((332521/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_407).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_408 : ((207663377/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 408, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 408, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 407, cos1269o2c k) + cos1269o2c 408 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 407) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_407
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 408 - ((9675307/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_408).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_409 : ((205304929/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 409, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 409, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 408, cos1269o2c k) + cos1269o2c 409 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 408) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_408
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 409 - ((-294681/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_409).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_410 : ((24442209/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 410, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 410, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 409, cos1269o2c k) + cos1269o2c 410 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 409) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_409
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 410 - ((-9766257/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_410).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_411 : ((197440447/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 411, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 411, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 410, cos1269o2c k) + cos1269o2c 411 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 410) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_410
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 411 - ((76151/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_411).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_412 : ((41461493/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 412, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 412, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 411, cos1269o2c k) + cos1269o2c 412 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 411) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_411
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 412 - ((4934009/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_412).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_413 : ((4120201/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 413, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 413, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 412, cos1269o2c k) + cos1269o2c 413 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 412) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_412
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 413 - ((-259283/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_413).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_414 : ((196052903/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 414, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 414, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 413, cos1269o2c k) + cos1269o2c 414 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 413) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_413
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 414 - ((-9956147/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_414).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_415 : ((24573561/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 415, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 415, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 414, cos1269o2c k) + cos1269o2c 415 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 414) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_414
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 415 - ((107317/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_415).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_416 : ((103293497/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 416, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 416, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 415, cos1269o2c k) + cos1269o2c 416 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 415) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_415
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 416 - ((4999753/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_416).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_417 : ((103480067/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 417, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 417, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 416, cos1269o2c k) + cos1269o2c 417 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 416) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_416
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 417 - ((18707/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_417).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_418 : ((98499119/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 418, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 418, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 417, cos1269o2c k) + cos1269o2c 418 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 417) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_417
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 418 - ((-155639/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_418).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_419 : ((195570887/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 419, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 419, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 418, cos1269o2c k) + cos1269o2c 419 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 418) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_418
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 419 - ((-1426351/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_419).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_420 : ((41073553/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 420, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 420, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 419, cos1269o2c k) + cos1269o2c 420 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 419) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_419
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 420 - ((4898939/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_420).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_421 : ((103984677/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 421, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 421, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 420, cos1269o2c k) + cos1269o2c 421 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 420) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_420
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 421 - ((2602589/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_421).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_422 : ((1240649/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 422, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 422, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 421, cos1269o2c k) + cos1269o2c 422 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 421) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_421
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 422 - ((-4732257/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_422).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_423 : ((38925791/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 423, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 423, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 422, cos1269o2c k) + cos1269o2c 423 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 422) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_422
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 423 - ((-774777/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_423).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_424 : ((101771029/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 424, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 424, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 423, cos1269o2c k) + cos1269o2c 424 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 423) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_423
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 424 - ((8914103/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_424).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_425 : ((208737661/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 425, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 425, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 424, cos1269o2c k) + cos1269o2c 425 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 424) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_424
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 425 - ((5196603/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_425).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_426 : ((40126633/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 426, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 426, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 425, cos1269o2c k) + cos1269o2c 426 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 425) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_425
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 426 - ((-1012937/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_426).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_427 : ((194120413/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 427, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 427, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 426, cos1269o2c k) + cos1269o2c 427 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 426) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_426
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 427 - ((-813969/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_427).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_428 : ((201116767/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 428, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 428, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 427, cos1269o2c k) + cos1269o2c 428 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 427) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_427
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 428 - ((3498677/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_428).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_429 : ((52214947/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 429, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 429, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 428, cos1269o2c k) + cos1269o2c 429 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 428) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_428
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 429 - ((7744021/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_429).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_430 : ((40656483/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 430, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 430, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 429, cos1269o2c k) + cos1269o2c 430 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 429) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_429
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 430 - ((-5576373/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_430).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_431 : ((1555837/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 431, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 431, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 430, cos1269o2c k) + cos1269o2c 431 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 430) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_430
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 431 - ((-880179/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_431).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_432 : ((39663891/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 432, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 432, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 431, cos1269o2c k) + cos1269o2c 432 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 431) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_431
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 432 - ((384083/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_432).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_433 : ((207899437/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 433, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 433, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 432, cos1269o2c k) + cos1269o2c 433 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 432) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_432
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 433 - ((4790491/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_433).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_434 : ((51518731/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 434, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 434, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 433, cos1269o2c k) + cos1269o2c 434 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 433) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_433
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 434 - ((-1823513/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_434).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_435 : ((24512559/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 435, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 435, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 434, cos1269o2c k) + cos1269o2c 435 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 434) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_434
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 435 - ((-2493363/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_435).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_436 : ((2446123/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 436, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 436, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 435, cos1269o2c k) + cos1269o2c 436 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 435) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_435
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 436 - ((-12801/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_436).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_437 : ((205563973/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 437, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 437, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 436, cos1269o2c k) + cos1269o2c 437 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 436) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_436
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 437 - ((9875133/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_437).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_438 : ((52078391/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 438, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 438, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 437, cos1269o2c k) + cos1269o2c 438 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 437) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_437
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 438 - ((2750591/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_438).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_439 : ((99555801/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 439, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 439, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 438, cos1269o2c k) + cos1269o2c 439 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 438) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_438
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 439 - ((-4600481/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_439).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_440 : ((97029409/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 440, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 440, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 439, cos1269o2c k) + cos1269o2c 440 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 439) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_439
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 440 - ((-631473/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_440).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_441 : ((2019577/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 441, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 441, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 440, cos1269o2c k) + cos1269o2c 441 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 440) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_440
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 441 - ((3949941/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_441).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_442 : ((209085949/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 442, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 442, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 441, cos1269o2c k) + cos1269o2c 442 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 441) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_441
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 442 - ((7129249/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_442).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_443 : ((203111021/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 443, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 443, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 442, cos1269o2c k) + cos1269o2c 443 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 442) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_442
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 443 - ((-746741/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_443).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_444 : ((194334773/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 444, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 444, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 443, cos1269o2c k) + cos1269o2c 444 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 443) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_443
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 444 - ((-548453/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_444).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_445 : ((98913081/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 445, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 445, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 444, cos1269o2c k) + cos1269o2c 445 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 444) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_444
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 445 - ((3492389/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_445).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_446 : ((207605003/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 446, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 446, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 445, cos1269o2c k) + cos1269o2c 446 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 445) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_445
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 446 - ((9779841/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_446).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_447 : ((206999827/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 447, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 447, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 446, cos1269o2c k) + cos1269o2c 447 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 446) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_446
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 447 - ((-37761/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_447).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_448 : ((49260377/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 448, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 448, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 447, cos1269o2c k) + cos1269o2c 448 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 447) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_447
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 448 - ((-9957319/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_448).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_449 : ((97290309/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 449, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 449, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 448, cos1269o2c k) + cos1269o2c 449 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 448) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_448
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 449 - ((-245989/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_449).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_450 : ((50939929/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 450, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 450, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 449, cos1269o2c k) + cos1269o2c 450 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 449) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_449
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 450 - ((4590049/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_450).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_451 : ((13072241/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 451, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 451, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 450, cos1269o2c k) + cos1269o2c 451 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 450) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_450
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 451 - ((269857/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_451).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_452 : ((100870297/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 452, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 452, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 451, cos1269o2c k) + cos1269o2c 452 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 451) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_451
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 452 - ((-3707131/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_452).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_453 : ((193880569/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 453, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 453, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 452, cos1269o2c k) + cos1269o2c 453 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 452) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_452
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 453 - ((-314361/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_453).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_454 : ((39725833/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 454, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 454, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 453, cos1269o2c k) + cos1269o2c 454 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 453) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_453
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 454 - ((1187399/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_454).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_455 : ((208119851/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 455, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 455, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 454, cos1269o2c k) + cos1269o2c 455 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 454) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_454
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 455 - ((4745843/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_455).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_456 : ((206699687/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 456, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 456, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 455, cos1269o2c k) + cos1269o2c 456 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 455) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_455
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 456 - ((-354791/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_456).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_457 : ((49176527/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 457, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 457, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 456, cos1269o2c k) + cos1269o2c 457 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 456) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_456
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 457 - ((-9992579/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_457).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_458 : ((194499073/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 458, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 458, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 457, cos1269o2c k) + cos1269o2c 458 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 457) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_457
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 458 - ((-441207/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_458).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_459 : ((12729499/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 459, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 459, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 458, cos1269o2c k) + cos1269o2c 459 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 458) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_458
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 459 - ((9173911/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_459).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_460 : ((104655893/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 460, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 460, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 459, cos1269o2c k) + cos1269o2c 460 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 459) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_459
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 460 - ((2820401/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_460).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_461 : ((202288227/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 461, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 461, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 460, cos1269o2c k) + cos1269o2c 461 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 460) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_460
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 461 - ((-7022559/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_461).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_462 : ((310299/16000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 462, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 462, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 461, cos1269o2c k) + cos1269o2c 462 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 461) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_461
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 462 - ((-521897/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_462).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_463 : ((24709949/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 463, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 463, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 462, cos1269o2c k) + cos1269o2c 463 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 462) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_462
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 463 - ((3743717/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_463).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_464 : ((25939211/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 464, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 464, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 463, cos1269o2c k) + cos1269o2c 464 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 463) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_463
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 464 - ((1229387/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_464).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_465 : ((51935479/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 465, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 465, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 464, cos1269o2c k) + cos1269o2c 465 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 464) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_464
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 465 - ((57307/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_465).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_466 : ((198005823/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 466, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 466, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 465, cos1269o2c k) + cos1269o2c 466 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 465) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_465
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 466 - ((-9735093/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_466).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_467 : ((96866517/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 467, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 467, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 466, cos1269o2c k) + cos1269o2c 467 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 466) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_466
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 467 - ((-4271789/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_467).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_468 : ((201662689/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 468, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 468, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 467, cos1269o2c k) + cos1269o2c 468 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 467) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_467
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 468 - ((1586131/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_468).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_469 : ((104657087/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 469, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 469, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 468, cos1269o2c k) + cos1269o2c 469 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 468) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_468
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 469 - ((1530497/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_469).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_470 : ((25586929/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 470, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 470, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 469, cos1269o2c k) + cos1269o2c 470 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 469) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_469
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 470 - ((-2308871/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_470).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_471 : ((195024809/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 471, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 471, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 470, cos1269o2c k) + cos1269o2c 471 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 470) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_470
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 471 - ((-9669623/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_471).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_472 : ((195350541/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 472, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 472, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 471, cos1269o2c k) + cos1269o2c 472 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 471) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_471
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 472 - ((81683/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_472).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_473 : ((205159511/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 473, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 473, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 472, cos1269o2c k) + cos1269o2c 473 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 472) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_472
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 473 - ((980997/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_473).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_474 : ((209290771/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 474, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 474, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 473, cos1269o2c k) + cos1269o2c 474 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 473) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_473
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 474 - ((206613/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_474).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_475 : ((201387283/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 475, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 475, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 474, cos1269o2c k) + cos1269o2c 475 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 474) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_474
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 475 - ((-987811/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_475).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_476 : ((19357779/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 476, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 476, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 475, cos1269o2c k) + cos1269o2c 476 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 475) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_475
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 476 - ((-7808493/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_476).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_477 : ((24724471/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 477, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 477, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 476, cos1269o2c k) + cos1269o2c 477 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 476) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_476
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 477 - ((2109489/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_477).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_478 : ((207607997/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 478, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 478, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 477, cos1269o2c k) + cos1269o2c 478 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 477) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_477
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 478 - ((9813229/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_478).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_479 : ((20811921/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 479, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 479, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 478, cos1269o2c k) + cos1269o2c 479 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 478) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_478
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 479 - ((512213/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_479).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_480 : ((19856109/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 480, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 480, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 479, cos1269o2c k) + cos1269o2c 480 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 479) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_479
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 480 - ((-14933/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_480).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_481 : ((193341189/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 481, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 481, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 480, cos1269o2c k) + cos1269o2c 481 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 480) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_480
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 481 - ((-5218901/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_481).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_482 : ((200292403/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 482, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 482, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 481, cos1269o2c k) + cos1269o2c 482 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 481) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_481
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 482 - ((3476107/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_482).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_483 : ((209004493/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 483, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 483, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 482, cos1269o2c k) + cos1269o2c 483 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 482) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_482
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 483 - ((871309/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_483).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_484 : ((206486141/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 484, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 484, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 483, cos1269o2c k) + cos1269o2c 484 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 483) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_483
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 484 - ((-314669/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_484).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_485 : ((196485371/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 485, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 485, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 484, cos1269o2c k) + cos1269o2c 485 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 484) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_484
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 485 - ((-999977/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_485).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_486 : ((48452741/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 486, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 486, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 485, cos1269o2c k) + cos1269o2c 486 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 485) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_485
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 486 - ((-2673407/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_486).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_487 : ((101200671/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 487, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 487, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 486, cos1269o2c k) + cos1269o2c 487 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 486) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_486
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 487 - ((4295689/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_487).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_488 : ((104809381/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 488, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 488, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 487, cos1269o2c k) + cos1269o2c 488 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 487) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_487
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 488 - ((360921/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_488).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_489 : ((204890683/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 489, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 489, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 488, cos1269o2c k) + cos1269o2c 489 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 488) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_488
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 489 - ((-4727079/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_489).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_490 : ((195125899/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 490, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 490, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 489, cos1269o2c k) + cos1269o2c 490 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 489) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_489
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 490 - ((-1220473/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_490).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_491 : ((4863283/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 491, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 491, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 490, cos1269o2c k) + cos1269o2c 491 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 490) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_490
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 491 - ((-593579/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_491).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_492 : ((101980207/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 492, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 492, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 491, cos1269o2c k) + cos1269o2c 492 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 491) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_491
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 492 - ((4715047/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_492).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_493 : ((104891971/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 493, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 493, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 492, cos1269o2c k) + cos1269o2c 493 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 492) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_492
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 493 - ((364033/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_493).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_494 : ((203620161/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 494, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 494, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 493, cos1269o2c k) + cos1269o2c 494 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 493) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_493
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 494 - ((-6162781/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_494).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_495 : ((38863769/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 495, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 495, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 494, cos1269o2c k) + cos1269o2c 495 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 494) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_494
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 495 - ((-2325079/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_495).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_496 : ((97588637/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 496, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 496, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 495, cos1269o2c k) + cos1269o2c 496 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 495) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_495
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 496 - ((859429/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_496).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_497 : ((102481601/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 497, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 497, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 496, cos1269o2c k) + cos1269o2c 497 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 496) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_496
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 497 - ((611683/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_497).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_498 : ((20977621/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 498, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 498, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 497, cos1269o2c k) + cos1269o2c 498 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 497) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_497
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 498 - ((601751/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_498).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_499 : ((50702469/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 499, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 499, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 498, cos1269o2c k) + cos1269o2c 499 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 498) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_498
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 499 - ((-3482667/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_499).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_500 : ((193893317/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 500, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 500, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 499, cos1269o2c k) + cos1269o2c 500 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 499) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_499
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 500 - ((-8915559/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_500).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_501 : ((97777409/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 501, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 501, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 500, cos1269o2c k) + cos1269o2c 501 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 500) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_500
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 501 - ((1662501/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_501).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_502 : ((205457953/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 502, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 502, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 501, cos1269o2c k) + cos1269o2c 502 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 501) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_501
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 502 - ((1980827/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_502).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_503 : ((104888521/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 503, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 503, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 502, cos1269o2c k) + cos1269o2c 503 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 502) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_502
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 503 - ((4320089/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_503).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_504 : ((202509347/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 504, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 504, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 503, cos1269o2c k) + cos1269o2c 504 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 503) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_503
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 504 - ((-1453339/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_504).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_505 : ((193734301/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 505, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 505, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 504, cos1269o2c k) + cos1269o2c 505 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 504) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_504
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 505 - ((-4387023/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_505).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_506 : ((39114047/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 506, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 506, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 505, cos1269o2c k) + cos1269o2c 506 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 505) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_505
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 506 - ((918467/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_506).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_507 : ((102740263/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 507, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 507, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 506, cos1269o2c k) + cos1269o2c 507 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 506) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_506
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 507 - ((9911291/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_507).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_508 : ((209864037/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 508, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 508, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 507, cos1269o2c k) + cos1269o2c 508 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 507) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_507
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 508 - ((4384511/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_508).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_509 : ((50682969/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 509, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 509, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 508, cos1269o2c k) + cos1269o2c 509 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 508) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_508
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 509 - ((-7131161/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_509).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_510 : ((96904137/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 510, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 510, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 509, cos1269o2c k) + cos1269o2c 510 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 509) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_509
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 510 - ((-4461301/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_510).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_511 : ((24400997/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 511, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 511, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 510, cos1269o2c k) + cos1269o2c 511 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 510) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_510
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 511 - ((700351/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_511).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_512 : ((51256871/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 512, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 512, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 511, cos1269o2c k) + cos1269o2c 512 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 511) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_511
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 512 - ((2455127/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_512).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_513 : ((105008539/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 513, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 513, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 512, cos1269o2c k) + cos1269o2c 513 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 512) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_512
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 513 - ((2495297/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_513).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_514 : ((20347417/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 514, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 514, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 513, cos1269o2c k) + cos1269o2c 514 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 513) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_513
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 514 - ((-1635477/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_514).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_515 : ((19417027/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 515, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 515, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 514, cos1269o2c k) + cos1269o2c 515 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 514) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_514
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 515 - ((-93029/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_515).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_516 : ((97262599/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 516, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 516, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 515, cos1269o2c k) + cos1269o2c 516 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 515) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_515
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 516 - ((44491/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_516).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_517 : ((102028713/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 517, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 517, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 516, cos1269o2c k) + cos1269o2c 517 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 516) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_516
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 517 - ((2383307/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_517).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_518 : ((10505983/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 518, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 518, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 517, cos1269o2c k) + cos1269o2c 518 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 517) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_517
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 518 - ((3031617/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_518).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_519 : ((102351631/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 519, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 519, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 518, cos1269o2c k) + cos1269o2c 519 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 518) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_518
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 519 - ((-2707699/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_519).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_520 : ((194949621/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 520, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 520, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 519, cos1269o2c k) + cos1269o2c 520 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 519) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_519
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 520 - ((-9752641/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_520).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_521 : ((96831539/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 521, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 521, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 520, cos1269o2c k) + cos1269o2c 521 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 520) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_520
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 521 - ((-1285543/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_521).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_522 : ((40503577/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 522, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 522, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 521, cos1269o2c k) + cos1269o2c 522 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 521) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_521
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 522 - ((8855807/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_522).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_523 : ((209959847/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 523, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 523, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 522, cos1269o2c k) + cos1269o2c 523 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 522) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_522
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 523 - ((3721481/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_523).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_524 : ((20631901/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 524, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 524, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 523, cos1269o2c k) + cos1269o2c 524 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 523) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_523
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 524 - ((-3639837/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_524).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_525 : ((196318669/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 525, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 525, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 524, cos1269o2c k) + cos1269o2c 525 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 524) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_524
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 525 - ((-9999341/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_525).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_526 : ((7714849/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 526, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 526, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 525, cos1269o2c k) + cos1269o2c 526 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 525) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_525
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 526 - ((-861611/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_526).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_527 : ((200404411/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 527, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 527, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 526, cos1269o2c k) + cos1269o2c 527 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 526) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_526
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 527 - ((3767093/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_527).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_528 : ((1634757/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 528, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 528, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 527, cos1269o2c k) + cos1269o2c 528 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 527) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_527
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 528 - ((1769097/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_528).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_529 : ((208099677/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 529, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 529, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 528, cos1269o2c k) + cos1269o2c 529 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 528) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_528
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 529 - ((-1148219/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_529).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_530 : ((24803517/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 530, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 530, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 529, cos1269o2c k) + cos1269o2c 530 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 529) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_529
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 530 - ((-9670541/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_530).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_531 : ((192518187/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 531, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 531, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 530, cos1269o2c k) + cos1269o2c 531 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 530) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_530
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 531 - ((-5908949/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_531).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_532 : ((98921217/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 532, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 532, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 531, cos1269o2c k) + cos1269o2c 532 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 531) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_531
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 532 - ((5325247/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_532).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_533 : ((207675591/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 533, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 533, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 532, cos1269o2c k) + cos1269o2c 533 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 532) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_532
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 533 - ((9834157/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_533).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_534 : ((209652603/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 534, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 534, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 533, cos1269o2c k) + cos1269o2c 534 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 533) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_533
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 534 - ((494503/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_534).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_535 : ((201302489/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 535, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 535, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 534, cos1269o2c k) + cos1269o2c 535 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 534) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_534
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 535 - ((-4174557/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_535).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_536 : ((193059673/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 536, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 536, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 535, cos1269o2c k) + cos1269o2c 536 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 535) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_535
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 536 - ((-1030227/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_536).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_537 : ((48795323/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 537, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 537, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 536, cos1269o2c k) + cos1269o2c 537 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 536) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_536
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 537 - ((2122619/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_537).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_538 : ((8201003/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 538, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 538, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 537, cos1269o2c k) + cos1269o2c 538 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 537) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_537
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 538 - ((9844783/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_538).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_539 : ((6575361/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 539, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 539, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 538, cos1269o2c k) + cos1269o2c 539 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 538) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_538
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 539 - ((5387477/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_539).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_540 : ((6397037/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 540, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 540, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 539, cos1269o2c k) + cos1269o2c 540 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 539) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_539
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 540 - ((-713171/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_540).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_541 : ((194924399/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 541, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 541, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 540, cos1269o2c k) + cos1269o2c 541 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 540) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_540
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 541 - ((-1955957/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_541).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_542 : ((193047083/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 542, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 542, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 541, cos1269o2c k) + cos1269o2c 542 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 541) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_541
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 542 - ((-469079/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_542).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_543 : ((201355641/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 543, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 543, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 542, cos1269o2c k) + cos1269o2c 543 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 542) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_542
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 543 - ((4154779/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_543).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_544 : ((209733249/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 544, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 544, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 543, cos1269o2c k) + cos1269o2c 544 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 543) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_543
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 544 - ((523663/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_544).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_545 : ((208021637/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 545, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 545, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 544, cos1269o2c k) + cos1269o2c 545 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 544) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_544
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 545 - ((-427653/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_545).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_546 : ((198297183/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 546, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 546, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 545, cos1269o2c k) + cos1269o2c 546 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 545) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_545
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 546 - ((-4861727/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_546).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_547 : ((192280611/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 547, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 547, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 546, cos1269o2c k) + cos1269o2c 547 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 546) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_546
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 547 - ((-1503893/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_547).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_548 : ((49297761/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 548, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 548, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 547, cos1269o2c k) + cos1269o2c 548 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 547) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_547
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 548 - ((4911433/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_548).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_549 : ((207140657/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 549, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 549, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 548, cos1269o2c k) + cos1269o2c 549 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 548) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_548
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 549 - ((9950613/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_549).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_550 : ((210254051/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 550, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 550, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 549, cos1269o2c k) + cos1269o2c 550 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 549) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_549
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 550 - ((1557197/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_550).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_551 : ((202833879/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 551, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 551, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 550, cos1269o2c k) + cos1269o2c 551 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 550) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_550
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 551 - ((-1854793/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_551).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_552 : ((96842077/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 552, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 552, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 551, cos1269o2c k) + cos1269o2c 552 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 551) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_551
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 552 - ((-365949/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_552).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_553 : ((38723137/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 553, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 553, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 552, cos1269o2c k) + cos1269o2c 553 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 552) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_552
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 553 - ((-67469/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_553).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_554 : ((202699101/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 554, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 554, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 553, cos1269o2c k) + cos1269o2c 554 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 553) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_553
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 554 - ((70972/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_554).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_555 : ((26282713/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 555, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 555, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 554, cos1269o2c k) + cos1269o2c 555 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 554) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_554
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 555 - ((7563603/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_555).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_556 : ((103727289/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 556, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 556, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 555, cos1269o2c k) + cos1269o2c 556 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 555) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_555
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 556 - ((-1403063/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_556).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_557 : ((197560213/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 557, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 557, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 556, cos1269o2c k) + cos1269o2c 557 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 556) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_556
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 557 - ((-1978673/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_557).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_558 : ((192088503/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 558, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 558, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 557, cos1269o2c k) + cos1269o2c 558 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 557) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_557
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 558 - ((-547071/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_558).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_559 : ((39475143/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 559, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 559, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 558, cos1269o2c k) + cos1269o2c 559 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 558) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_558
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 559 - ((1322053/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_559).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_560 : ((103651127/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 560, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 560, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 559, cos1269o2c k) + cos1269o2c 560 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 559) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_559
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 560 - ((9927539/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_560).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_561 : ((52607611/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 561, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 561, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 560, cos1269o2c k) + cos1269o2c 561 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 560) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_560
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 561 - ((312919/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_561).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_562 : ((812699/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 562, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 562, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 561, cos1269o2c k) + cos1269o2c 562 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 561) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_561
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 562 - ((-3627347/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_562).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_563 : ((193846627/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 563, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 563, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 562, cos1269o2c k) + cos1269o2c 563 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 562) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_562
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 563 - ((-9327123/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_563).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_564 : ((193087569/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 564, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 564, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 563, cos1269o2c k) + cos1269o2c 564 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 563) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_563
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 564 - ((-379029/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_564).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_565 : ((100875761/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 565, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 565, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 564, cos1269o2c k) + cos1269o2c 565 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 564) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_564
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 565 - ((8664953/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_565).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_566 : ((21000767/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 566, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 566, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 565, cos1269o2c k) + cos1269o2c 566 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 565) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_565
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 566 - ((2064287/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_566).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_567 : ((52131497/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 567, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 567, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 566, cos1269o2c k) + cos1269o2c 567 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 566) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_566
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 567 - ((-740341/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_567).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_568 : ((198983907/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 568, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 568, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 567, cos1269o2c k) + cos1269o2c 568 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 567) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_567
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 568 - ((-9541081/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_568).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_569 : ((38420421/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 569, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 569, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 568, cos1269o2c k) + cos1269o2c 569 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 568) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_568
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 569 - ((-3440401/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_569).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_570 : ((9778981/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 570, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 570, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 569, cos1269o2c k) + cos1269o2c 570 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 569) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_569
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 570 - ((695703/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_570).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_571 : ((20552531/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 571, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 571, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 570, cos1269o2c k) + cos1269o2c 571 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 570) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_570
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 571 - ((994669/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_571).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_572 : ((210869297/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 572, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 572, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 571, cos1269o2c k) + cos1269o2c 572 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 571) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_571
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 572 - ((5344987/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_572).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_573 : ((20568899/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 573, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 573, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 572, cos1269o2c k) + cos1269o2c 573 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 572) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_572
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 573 - ((-5179307/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_573).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_574 : ((195719931/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 574, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 574, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 573, cos1269o2c k) + cos1269o2c 574 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 573) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_573
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 574 - ((-9968059/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_574).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_575 : ((11996913/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 575, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 575, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 574, cos1269o2c k) + cos1269o2c 575 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 574) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_574
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 575 - ((-3768323/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_575).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_576 : ((99257167/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 576, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 576, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 575, cos1269o2c k) + cos1269o2c 576 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 575) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_575
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 576 - ((3282363/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_576).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_577 : ((104106211/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 577, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 577, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 576, cos1269o2c k) + cos1269o2c 577 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 576) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_576
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 577 - ((606193/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_577).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_578 : ((168363/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 578, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 578, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 577, cos1269o2c k) + cos1269o2c 578 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 577) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_577
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 578 - ((280291/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_578).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_579 : ((202805329/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 579, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 579, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 578, cos1269o2c k) + cos1269o2c 579 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 578) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_578
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 579 - ((-7647421/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_579).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_580 : ((193573599/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 580, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 580, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 579, cos1269o2c k) + cos1269o2c 580 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 579) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_579
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 580 - ((-923073/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_580).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_581 : ((192743499/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 581, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 581, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 580, cos1269o2c k) + cos1269o2c 581 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 580) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_580
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 581 - ((-8291/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_581).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_582 : ((201200933/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 582, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 582, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 581, cos1269o2c k) + cos1269o2c 582 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 581) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_581
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 582 - ((4229217/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_582).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_583 : ((209845171/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 583, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 583, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 582, cos1269o2c k) + cos1269o2c 583 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 582) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_582
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 583 - ((4322619/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_583).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_584 : ((104706133/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 584, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 584, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 583, cos1269o2c k) + cos1269o2c 584 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 583) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_583
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 584 - ((-86381/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_584).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_585 : ((200372399/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 585, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 585, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 584, cos1269o2c k) + cos1269o2c 585 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 584) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_584
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 585 - ((-9038867/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_585).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_586 : ((6011257/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 586, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 586, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 585, cos1269o2c k) + cos1269o2c 586 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 585) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_585
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 586 - ((-320447/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_586).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_587 : ((24235069/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 587, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 587, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 586, cos1269o2c k) + cos1269o2c 587 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 586) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_586
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 587 - ((95083/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_587).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_588 : ((101656729/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 588, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 588, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 587, cos1269o2c k) + cos1269o2c 588 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 587) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_587
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 588 - ((4716953/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_588).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_589 : ((210696777/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 589, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 589, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 588, cos1269o2c k) + cos1269o2c 589 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 588) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_588
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 589 - ((7384319/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_589).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_590 : ((104132081/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 590, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 590, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 589, cos1269o2c k) + cos1269o2c 590 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 589) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_589
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 590 - ((-486323/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_590).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_591 : ((4964391/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 591, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 591, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 590, cos1269o2c k) + cos1269o2c 591 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 590) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_590
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 591 - ((-4843761/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_591).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_592 : ((3835347/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 592, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 592, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 591, cos1269o2c k) + cos1269o2c 592 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 591) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_591
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 592 - ((-680729/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_592).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_593 : ((194931831/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 593, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 593, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 592, cos1269o2c k) + cos1269o2c 593 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 592) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_592
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 593 - ((3165481/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_593).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_594 : ((204770027/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 594, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 594, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 593, cos1269o2c k) + cos1269o2c 594 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 593) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_593
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 594 - ((2459799/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_594).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_595 : ((26385109/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 595, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 595, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 594, cos1269o2c k) + cos1269o2c 595 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 594) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_594
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 595 - ((1262369/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_595).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_596 : ((207348641/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 596, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 596, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 595, cos1269o2c k) + cos1269o2c 596 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 595) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_595
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 596 - ((-3731231/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_596).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_597 : ((197425271/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 597, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 597, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 596, cos1269o2c k) + cos1269o2c 597 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 596) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_596
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 597 - ((-992237/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_597).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_598 : ((47875981/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 598, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 598, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 597, cos1269o2c k) + cos1269o2c 598 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 597) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_597
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 598 - ((-5920347/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_598).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_599 : ((195640169/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 599, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 599, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 598, cos1269o2c k) + cos1269o2c 599 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 598) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_598
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 599 - ((827449/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_599).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_600 : ((25700293/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 600, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 600, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 599, cos1269o2c k) + cos1269o2c 600 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 599) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_599
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 600 - ((398527/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_600).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_601 : ((211247843/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 601, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 601, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 600, cos1269o2c k) + cos1269o2c 601 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 600) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_600
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 601 - ((5646499/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_601).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_602 : ((25856699/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 602, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 602, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 601, cos1269o2c k) + cos1269o2c 602 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 601) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_601
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 602 - ((-4393251/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_602).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_603 : ((49218087/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 603, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 603, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 602, cos1269o2c k) + cos1269o2c 603 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 602) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_602
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 603 - ((-2495061/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_603).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_604 : ((191371891/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 604, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 604, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 603, cos1269o2c k) + cos1269o2c 604 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 603) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_603
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 604 - ((-5499457/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_604).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_605 : ((48969037/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 605, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 605, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 604, cos1269o2c k) + cos1269o2c 605 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 604) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_604
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 605 - ((4505257/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_605).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_606 : ((102929857/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 606, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 606, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 605, cos1269o2c k) + cos1269o2c 606 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 605) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_605
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 606 - ((4992283/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_606).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_607 : ((211340611/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 607, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 607, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 606, cos1269o2c k) + cos1269o2c 607 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 606) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_606
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 607 - ((5481897/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_607).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_608 : ((51715517/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 608, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 608, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 607, cos1269o2c k) + cos1269o2c 608 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 607) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_607
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 608 - ((-4477543/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_608).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_609 : ((98440709/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 609, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 609, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 608, cos1269o2c k) + cos1269o2c 609 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 608) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_608
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 609 - ((-199593/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_609).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_610 : ((2988861/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 610, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 610, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 609, cos1269o2c k) + cos1269o2c 610 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 609) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_609
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 610 - ((-2796657/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_610).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_611 : ((195597289/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 611, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 611, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 610, cos1269o2c k) + cos1269o2c 611 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 610) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_610
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 611 - ((862237/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_611).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_612 : ((205558061/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 612, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 612, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 611, cos1269o2c k) + cos1269o2c 612 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 611) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_611
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 612 - ((2490443/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_612).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_613 : ((42277247/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 613, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 613, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 612, cos1269o2c k) + cos1269o2c 613 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 612) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_612
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 613 - ((2914587/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_613).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_614 : ((207381537/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 614, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 614, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 613, cos1269o2c k) + cos1269o2c 614 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 613) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_613
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 614 - ((-2001849/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_614).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_615 : ((98730129/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 615, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 615, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 614, cos1269o2c k) + cos1269o2c 615 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 614) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_614
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 615 - ((-9920279/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_615).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_616 : ((191278613/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 616, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 616, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 615, cos1269o2c k) + cos1269o2c 616 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 615) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_615
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 616 - ((-1236129/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_616).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_617 : ((38965579/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 617, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 617, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 616, cos1269o2c k) + cos1269o2c 617 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 616) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_616
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 617 - ((1775141/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_617).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_618 : ((102332359/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 618, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 618, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 617, cos1269o2c k) + cos1269o2c 618 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 617) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_617
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 618 - ((9837823/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_618).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_619 : ((42259433/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 619, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 619, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 618, cos1269o2c k) + cos1269o2c 619 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 618) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_618
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 619 - ((6633447/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_619).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_620 : ((208351183/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 620, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 620, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 619, cos1269o2c k) + cos1269o2c 620 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 619) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_619
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 620 - ((-1472491/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_620).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_621 : ((12416209/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 621, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 621, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 620, cos1269o2c k) + cos1269o2c 621 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 620) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_620
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 621 - ((-9690839/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_621).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_622 : ((191490417/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 622, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 622, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 621, cos1269o2c k) + cos1269o2c 622 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 621) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_621
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 622 - ((-7167927/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_622).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_623 : ((12104563/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 623, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 623, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 622, cos1269o2c k) + cos1269o2c 623 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 622) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_622
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 623 - ((2183591/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_623).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_624 : ((3173789/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 624, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 624, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 623, cos1269o2c k) + cos1269o2c 624 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 623) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_623
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 624 - ((1181311/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_624).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_625 : ((421757/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 625, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 625, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 624, cos1269o2c k) + cos1269o2c 625 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 624) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_624
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 625 - ((1939251/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_625).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_626 : ((52403841/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 626, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 626, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 625, cos1269o2c k) + cos1269o2c 626 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 625) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_625
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 626 - ((-157767/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_626).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_627 : ((200530787/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 627, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 627, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 626, cos1269o2c k) + cos1269o2c 627 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 626) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_626
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 627 - ((-9083577/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_627).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_628 : ((192163423/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 628, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 628, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 627, cos1269o2c k) + cos1269o2c 628 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 627) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_627
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 628 - ((-2091591/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_628).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_629 : ((192346807/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 629, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 629, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 628, cos1269o2c k) + cos1269o2c 629 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 628) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_628
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 629 - ((2881/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_629).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_630 : ((2511253/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 630, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 630, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 629, cos1269o2c k) + cos1269o2c 630 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 629) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_629
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 630 - ((8554433/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_630).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_631 : ((104925597/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 631, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 631, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 630, cos1269o2c k) + cos1269o2c 631 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 630) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_630
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 631 - ((4475977/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_631).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_632 : ((2108897/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 632, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 632, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 631, cos1269o2c k) + cos1269o2c 632 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 631) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_631
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 632 - ((519753/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_632).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_633 : ((10153061/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 633, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 633, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 632, cos1269o2c k) + cos1269o2c 633 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 632) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_632
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 633 - ((-195687/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_633).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_634 : ((193599249/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 634, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 634, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 633, cos1269o2c k) + cos1269o2c 634 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 633) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_633
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 634 - ((-9460971/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_634).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_635 : ((191211577/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 635, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 635, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 634, cos1269o2c k) + cos1269o2c 635 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 634) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_634
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 635 - ((-149167/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_635).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_636 : ((198081329/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 636, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 636, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 635, cos1269o2c k) + cos1269o2c 636 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 635) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_635
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 636 - ((214711/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_636).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_637 : ((103956199/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 637, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 637, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 636, cos1269o2c k) + cos1269o2c 637 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 636) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_636
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 637 - ((9832069/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_637).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_638 : ((42346349/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 638, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 638, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 637, cos1269o2c k) + cos1269o2c 638 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 637) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_637
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 638 - ((3820347/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_638).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_639 : ((206069829/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 639, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 639, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 638, cos1269o2c k) + cos1269o2c 639 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 638) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_638
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 639 - ((-1415229/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_639).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_640 : ((196071503/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 640, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 640, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 639, cos1269o2c k) + cos1269o2c 640 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 639) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_639
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 640 - ((-4998663/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_640).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_641 : ((38156777/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 641, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 641, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 640, cos1269o2c k) + cos1269o2c 641 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 640) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_640
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 641 - ((-2643309/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_641).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_642 : ((194970661/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 642, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 642, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 641, cos1269o2c k) + cos1269o2c 642 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 641) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_641
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 642 - ((32717/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_642).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_643 : ((204855629/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 643, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 643, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 642, cos1269o2c k) + cos1269o2c 643 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 642) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_642
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 643 - ((617873/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_643).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_644 : ((52891877/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 644, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 644, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 643, cos1269o2c k) + cos1269o2c 644 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 643) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_643
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 644 - ((6712879/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_644).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_645 : ((209106567/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 645, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 645, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 644, cos1269o2c k) + cos1269o2c 645 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 644) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_644
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 645 - ((-2459941/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_645).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_646 : ((99837817/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 646, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 646, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 645, cos1269o2c k) + cos1269o2c 646 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 645) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_645
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 646 - ((-9429933/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_646).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_647 : ((191666219/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 647, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 647, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 646, cos1269o2c k) + cos1269o2c 647 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 646) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_646
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 647 - ((-1601683/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_647).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_648 : ((24022153/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 648, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 648, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 647, cos1269o2c k) + cos1269o2c 648 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 647) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_647
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 648 - ((102401/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_648).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_649 : ((200747593/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 649, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 649, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 648, cos1269o2c k) + cos1269o2c 649 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 648) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_648
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 649 - ((8571369/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_649).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_650 : ((104906033/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 650, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 650, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 649, cos1269o2c k) + cos1269o2c 650 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 649) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_649
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 650 - ((9065473/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_650).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_651 : ((5285011/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 651, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 651, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 650, cos1269o2c k) + cos1269o2c 651 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 650) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_650
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 651 - ((794687/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_651).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_652 : ((102063563/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 652, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 652, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 651, cos1269o2c k) + cos1269o2c 652 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 651) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_651
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 652 - ((-3636157/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_652).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_653 : ((7774333/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 653, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 653, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 652, cos1269o2c k) + cos1269o2c 653 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 652) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_652
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 653 - ((-9767801/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_653).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_654 : ((47652829/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 654, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 654, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 653, cos1269o2c k) + cos1269o2c 654 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 653) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_653
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 654 - ((-3746009/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_654).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_655 : ((196136363/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 655, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 655, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 654, cos1269o2c k) + cos1269o2c 655 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 654) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_654
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 655 - ((5526047/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_655).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_656 : ((206133853/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 656, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 656, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 655, cos1269o2c k) + cos1269o2c 656 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 655) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_655
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 656 - ((999849/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_656).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_657 : ((211956567/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 657, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 657, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 656, cos1269o2c k) + cos1269o2c 657 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 656) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_656
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 657 - ((2911857/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_657).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_658 : ((208588961/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 658, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 658, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 657, cos1269o2c k) + cos1269o2c 658 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 657) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_657
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 658 - ((-1683303/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_658).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_659 : ((198934099/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 659, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 659, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 658, cos1269o2c k) + cos1269o2c 659 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 658) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_658
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 659 - ((-4826931/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_659).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_660 : ((47818299/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 660, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 660, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 659, cos1269o2c k) + cos1269o2c 660 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 659) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_659
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 660 - ((-7659903/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_660).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_661 : ((38430317/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 661, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 661, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 660, cos1269o2c k) + cos1269o2c 661 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 660) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_660
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 661 - ((879389/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_661).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_662 : ((200810983/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 662, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 662, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 661, cos1269o2c k) + cos1269o2c 662 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 661) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_661
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 662 - ((4330199/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_662).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_663 : ((104941143/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 663, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 663, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 662, cos1269o2c k) + cos1269o2c 663 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 662) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_662
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 663 - ((9072303/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_663).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_664 : ((13229679/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 664, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 664, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 663, cos1269o2c k) + cos1269o2c 664 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 663) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_663
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 664 - ((896789/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_664).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_665 : ((40936019/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 665, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 665, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 664, cos1269o2c k) + cos1269o2c 665 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 664) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_664
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 665 - ((-6993769/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_665).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_666 : ((12175143/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 666, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 666, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 665, cos1269o2c k) + cos1269o2c 666 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 665) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_665
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 666 - ((-9876807/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_666).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_667 : ((38069381/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 667, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 667, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 666, cos1269o2c k) + cos1269o2c 667 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 666) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_666
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 667 - ((-4454383/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_667).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_668 : ((39008457/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 668, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 668, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 667, cos1269o2c k) + cos1269o2c 668 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 667) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_667
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 668 - ((234819/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_668).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_669 : ((204953279/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 669, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 669, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 668, cos1269o2c k) + cos1269o2c 669 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 668) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_668
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 669 - ((4955997/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_669).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_670 : ((52952767/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 670, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 670, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 669, cos1269o2c k) + cos1269o2c 670 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 669) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_669
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 670 - ((6858789/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_670).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_671 : ((209916741/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 671, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 671, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 670, cos1269o2c k) + cos1269o2c 671 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 670) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_670
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 671 - ((-1893327/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_671).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_672 : ((50212199/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 672, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 672, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 671, cos1269o2c k) + cos1269o2c 672 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 671) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_671
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 672 - ((-1813389/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_672).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_673 : ((192111019/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 673, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 673, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 672, cos1269o2c k) + cos1269o2c 673 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 672) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_672
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 673 - ((-8736777/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_673).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_674 : ((47726721/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 674, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 674, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 673, cos1269o2c k) + cos1269o2c 674 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 673) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_673
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 674 - ((-240627/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_674).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_675 : ((9910881/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 675, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 675, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 674, cos1269o2c k) + cos1269o2c 675 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 674) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_674
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 675 - ((913967/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_675).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_676 : ((332863/16000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 676, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 676, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 675, cos1269o2c k) + cos1269o2c 676 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 675) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_675
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 676 - ((1964551/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_676).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_677 : ((106168409/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 677, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 677, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 676, cos1269o2c k) + cos1269o2c 677 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 676) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_676
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 677 - ((4298443/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_677).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_678 : ((6487817/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 678, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 678, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 677, cos1269o2c k) + cos1269o2c 678 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 677) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_677
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 678 - ((-2362837/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_678).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_679 : ((197711793/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 679, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 679, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 678, cos1269o2c k) + cos1269o2c 679 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 678) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_678
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 679 - ((-9897351/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_679).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_680 : ((3813493/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 680, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 680, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 679, cos1269o2c k) + cos1269o2c 680 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 679) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_679
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 680 - ((-7036143/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_680).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_681 : ((38437541/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 681, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 681, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 680, cos1269o2c k) + cos1269o2c 681 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 680) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_680
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 681 - ((302811/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_681).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_682 : ((40204069/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 682, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 682, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 681, cos1269o2c k) + cos1269o2c 682 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 681) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_681
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 682 - ((220841/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_682).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_683 : ((210058903/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 683, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 683, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 682, cos1269o2c k) + cos1269o2c 683 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 682) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_682
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 683 - ((4519779/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_683).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_684 : ((106025211/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 684, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 684, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 683, cos1269o2c k) + cos1269o2c 684 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 683) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_683
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 684 - ((1992519/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_684).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_685 : ((41081599/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 685, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 685, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 684, cos1269o2c k) + cos1269o2c 685 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 684) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_684
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 685 - ((-6641427/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_685).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_686 : ((195439911/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 686, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 686, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 685, cos1269o2c k) + cos1269o2c 686 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 685) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_685
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 686 - ((-2491771/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_686).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_687 : ((95040583/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 687, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 687, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 686, cos1269o2c k) + cos1269o2c 687 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 686) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_686
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 687 - ((-1071549/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_687).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_688 : ((193579677/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 688, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 688, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 687, cos1269o2c k) + cos1269o2c 688 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 687) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_687
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 688 - ((3499511/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_688).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_689 : ((50789039/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 689, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 689, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 688, cos1269o2c k) + cos1269o2c 689 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 688) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_688
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 689 - ((9577479/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_689).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_690 : ((211244343/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 690, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 690, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 689, cos1269o2c k) + cos1269o2c 690 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 689) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_689
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 690 - ((8089187/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_690).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_691 : ((52869241/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 691, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 691, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 690, cos1269o2c k) + cos1269o2c 691 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 690) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_690
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 691 - ((233621/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_691).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_692 : ((101839483/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 692, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 692, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 691, cos1269o2c k) + cos1269o2c 692 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 691) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_691
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 692 - ((-3898499/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_692).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_693 : ((38792731/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 693, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 693, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 692, cos1269o2c k) + cos1269o2c 693 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 692) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_692
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 693 - ((-9714311/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_693).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_694 : ((189919417/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 694, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 694, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 693, cos1269o2c k) + cos1269o2c 694 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 693) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_693
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 694 - ((-2021619/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_694).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_695 : ((97344819/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 695, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 695, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 694, cos1269o2c k) + cos1269o2c 695 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 694) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_694
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 695 - ((4771221/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_695).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_696 : ((25569887/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 696, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 696, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 695, cos1269o2c k) + cos1269o2c 696 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 695) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_695
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 696 - ((4935229/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_696).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_697 : ((211875803/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 697, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 697, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 696, cos1269o2c k) + cos1269o2c 697 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 696) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_696
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 697 - ((7317707/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_697).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_698 : ((42197661/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 698, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 698, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 697, cos1269o2c k) + cos1269o2c 698 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 697) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_697
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 698 - ((-443249/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_698).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_699 : ((20258821/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 699, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 699, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 698, cos1269o2c k) + cos1269o2c 699 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 698) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_698
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 699 - ((-1679819/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_699).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_700 : ((193137863/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 700, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 700, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 699, cos1269o2c k) + cos1269o2c 700 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 699) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_699
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 700 - ((-9449347/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_700).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_701 : ((189880863/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 701, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 701, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 700, cos1269o2c k) + cos1269o2c 701 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 700) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_700
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 701 - ((-407/1250 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_701).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_702 : ((195300551/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 702, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 702, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 701, cos1269o2c k) + cos1269o2c 702 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 701) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_701
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 702 - ((338793/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_702).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_703 : ((41050939/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 703, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 703, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 702, cos1269o2c k) + cos1269o2c 703 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 702) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_702
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 703 - ((1244393/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_703).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_704 : ((212169007/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 704, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 704, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 703, cos1269o2c k) + cos1269o2c 704 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 703) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_703
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 704 - ((432207/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_704).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_705 : ((210801633/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 705, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 705, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 704, cos1269o2c k) + cos1269o2c 705 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 704) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_704
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 705 - ((-683187/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_705).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_706 : ((101097419/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 706, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 706, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 705, cos1269o2c k) + cos1269o2c 706 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 705) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_705
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 706 - ((-1721159/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_706).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_707 : ((96423951/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 707, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 707, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 706, cos1269o2c k) + cos1269o2c 707 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 706) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_706
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 707 - ((-584121/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_707).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_708 : ((189793339/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 708, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 708, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 707, cos1269o2c k) + cos1269o2c 708 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 707) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_707
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 708 - ((-3053563/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_708).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_709 : ((195316701/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 709, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 709, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 708, cos1269o2c k) + cos1269o2c 709 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 708) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_708
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 709 - ((2762181/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_709).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_710 : ((205274099/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 710, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 710, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 709, cos1269o2c k) + cos1269o2c 710 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 709) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_709
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 710 - ((4979199/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_710).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_711 : ((53056791/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 711, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 711, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 710, cos1269o2c k) + cos1269o2c 711 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 710) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_710
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 711 - ((1390813/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_711).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_712 : ((105500603/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 712, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 712, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 711, cos1269o2c k) + cos1269o2c 712 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 711) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_711
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 712 - ((-612479/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_712).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_713 : ((810057/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 713, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 713, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 712, cos1269o2c k) + cos1269o2c 713 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 712) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_712
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 713 - ((-2121489/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_713).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_714 : ((193058611/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 714, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 714, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 713, cos1269o2c k) + cos1269o2c 714 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 713) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_713
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 714 - ((-9454639/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_714).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_715 : ((94809763/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 715, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 715, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 714, cos1269o2c k) + cos1269o2c 715 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 714) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_714
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 715 - ((-687617/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_715).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_716 : ((97361941/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 716, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 716, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 715, cos1269o2c k) + cos1269o2c 716 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 715) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_715
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 716 - ((1276339/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_716).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_717 : ((102305731/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 717, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 717, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 716, cos1269o2c k) + cos1269o2c 717 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 716) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_716
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 717 - ((494429/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_717).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_718 : ((212029537/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 718, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 718, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 717, cos1269o2c k) + cos1269o2c 718 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 717) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_717
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 718 - ((296763/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_718).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_719 : ((211556849/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 719, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 719, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 718, cos1269o2c k) + cos1269o2c 719 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 718) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_718
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 719 - ((-58961/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_719).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_720 : ((101772583/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 720, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 720, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 719, cos1269o2c k) + cos1269o2c 720 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 719) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_719
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 720 - ((-8010683/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_720).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_721 : ((193828187/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 721, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 721, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 720, cos1269o2c k) + cos1269o2c 721 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 720) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_720
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 721 - ((-9715979/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_721).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_722 : ((23681907/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 722, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 722, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 721, cos1269o2c k) + cos1269o2c 722 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 721) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_721
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 722 - ((-4371931/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_722).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_723 : ((193584169/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 723, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 723, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 722, cos1269o2c k) + cos1269o2c 723 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 722) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_722
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 723 - ((4129913/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_723).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_724 : ((101612941/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 724, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 724, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 723, cos1269o2c k) + cos1269o2c 724 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 723) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_723
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 724 - ((9642713/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_724).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_725 : ((26429327/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 725, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 725, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 724, cos1269o2c k) + cos1269o2c 725 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 724) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_724
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 725 - ((4104867/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_725).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_726 : ((212317649/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 726, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 726, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 725, cos1269o2c k) + cos1269o2c 726 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 725) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_725
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 726 - ((884033/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_726).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_727 : ((205249763/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 727, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 727, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 726, cos1269o2c k) + cos1269o2c 727 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 726) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_726
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 727 - ((-3533443/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_727).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_728 : ((195285887/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 728, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 728, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 727, cos1269o2c k) + cos1269o2c 728 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 727) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_727
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 728 - ((-2490719/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_728).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_729 : ((189526547/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 729, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 729, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 728, cos1269o2c k) + cos1269o2c 729 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 728) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_728
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 729 - ((-287917/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_729).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_730 : ((38411823/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 730, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 730, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 729, cos1269o2c k) + cos1269o2c 730 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 729) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_729
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 730 - ((39587/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_730).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_731 : ((40215913/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 731, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 731, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 730, cos1269o2c k) + cos1269o2c 731 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 730) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_730
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 731 - ((180429/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_731).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_732 : ((52550991/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 732, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 732, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 731, cos1269o2c k) + cos1269o2c 732 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 731) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_731
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 732 - ((9125399/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_732).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_733 : ((53249393/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 733, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 733, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 732, cos1269o2c k) + cos1269o2c 733 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 732) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_732
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 733 - ((174663/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_733).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_734 : ((207501441/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 734, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 734, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 733, cos1269o2c k) + cos1269o2c 734 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 733) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_733
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 734 - ((-5495131/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_734).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_735 : ((98789361/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 735, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 735, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 734, cos1269o2c k) + cos1269o2c 735 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 734) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_734
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 735 - ((-9921719/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_735).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_736 : ((190176357/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 736, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 736, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 735, cos1269o2c k) + cos1269o2c 736 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 735) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_735
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 736 - ((-1480273/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_736).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_737 : ((23807149/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 737, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 737, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 736, cos1269o2c k) + cos1269o2c 737 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 736) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_736
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 737 - ((56367/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_737).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_738 : ((24777237/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 738, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 738, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 737, cos1269o2c k) + cos1269o2c 738 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 737) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_737
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 738 - ((970213/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_738).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_739 : ((208060749/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 739, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 739, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 738, cos1269o2c k) + cos1269o2c 739 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 738) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_738
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 739 - ((9843853/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_739).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_740 : ((106582847/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 740, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 740, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 739, cos1269o2c k) + cos1269o2c 740 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 739) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_739
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 740 - ((1021189/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_740).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_741 : ((26251173/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 741, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 741, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 740, cos1269o2c k) + cos1269o2c 741 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 740) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_740
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 741 - ((-315531/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_741).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_742 : ((100387467/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 742, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 742, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 741, cos1269o2c k) + cos1269o2c 742 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 741) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_741
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 742 - ((-184669/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_742).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_743 : ((191815413/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 743, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 743, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 742, cos1269o2c k) + cos1269o2c 743 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 742) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_742
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 743 - ((-8958521/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_743).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_744 : ((94636583/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 744, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 744, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 743, cos1269o2c k) + cos1269o2c 744 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 743) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_743
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 744 - ((-2541247/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_744).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_745 : ((38975977/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 745, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 745, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 744, cos1269o2c k) + cos1269o2c 745 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 744) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_744
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 745 - ((5607719/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_745).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_746 : ((204801657/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 746, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 746, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 745, cos1269o2c k) + cos1269o2c 746 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 745) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_745
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 746 - ((2480693/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_746).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_747 : ((106140993/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 747, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 747, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 746, cos1269o2c k) + cos1269o2c 747 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 746) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_746
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 747 - ((7481329/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_747).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_748 : ((53061271/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 748, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 748, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 747, cos1269o2c k) + cos1269o2c 748 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 747) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_747
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 748 - ((-17951/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_748).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_749 : ((25590353/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 749, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 749, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 748, cos1269o2c k) + cos1269o2c 749 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 748) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_748
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 749 - ((-376063/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_749).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_750 : ((97401243/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 750, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 750, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 749, cos1269o2c k) + cos1269o2c 750 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 749) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_749
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 750 - ((-4959669/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_750).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_751 : ((189169189/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 751, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 751, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 750, cos1269o2c k) + cos1269o2c 751 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 750) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_750
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 751 - ((-5632297/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_751).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_752 : ((191603839/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 752, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 752, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 751, cos1269o2c k) + cos1269o2c 752 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 751) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_751
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 752 - ((48713/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_752).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_753 : ((20046553/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 753, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 753, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 752, cos1269o2c k) + cos1269o2c 753 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 752) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_752
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 753 - ((8862691/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_753).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_754 : ((104910911/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 754, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 754, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 753, cos1269o2c k) + cos1269o2c 754 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 753) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_753
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 754 - ((2339323/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_754).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_755 : ((213430957/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 755, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 755, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 754, cos1269o2c k) + cos1269o2c 755 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 754) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_754
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 755 - ((722027/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_755).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_756 : ((104448453/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 756, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 756, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 755, cos1269o2c k) + cos1269o2c 756 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 755) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_755
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 756 - ((-4533051/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_756).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_757 : ((199236083/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 757, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 757, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 756, cos1269o2c k) + cos1269o2c 757 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 756) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_756
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 757 - ((-9659823/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_757).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_758 : ((7633949/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 758, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 758, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 757, cos1269o2c k) + cos1269o2c 758 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 757) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_757
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 758 - ((-4193179/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_758).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_759 : ((189271831/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 759, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 759, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 758, cos1269o2c k) + cos1269o2c 759 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 758) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_758
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 759 - ((-787947/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_759).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_760 : ((97768471/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 760, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 760, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 759, cos1269o2c k) + cos1269o2c 760 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 759) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_759
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 760 - ((6266111/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_760).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_761 : ((6422449/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 761, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 761, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 760, cos1269o2c k) + cos1269o2c 761 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 760) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_760
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 761 - ((4991213/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_761).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_762 : ((10633453/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 762, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 762, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 761, cos1269o2c k) + cos1269o2c 762 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 761) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_761
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 762 - ((1787923/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_762).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_763 : ((212315327/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 763, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 763, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 762, cos1269o2c k) + cos1269o2c 763 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 762) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_762
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 763 - ((-352733/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_763).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_764 : ((51173761/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 764, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 764, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 763, cos1269o2c k) + cos1269o2c 764 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 763) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_763
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 764 - ((-7619283/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_764).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_765 : ((38954533/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 765, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 765, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 764, cos1269o2c k) + cos1269o2c 765 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 764) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_764
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 765 - ((-9921379/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_765).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_766 : ((94495037/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 766, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 766, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 765, cos1269o2c k) + cos1269o2c 766 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 765) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_765
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 766 - ((-5781591/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_766).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_767 : ((191086987/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 767, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 767, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 766, cos1269o2c k) + cos1269o2c 767 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 766) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_766
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 767 - ((2097913/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_767).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_768 : ((3994003/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 768, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 768, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 767, cos1269o2c k) + cos1269o2c 768 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 767) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_767
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 768 - ((8614163/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_768).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_769 : ((26159169/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 769, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 769, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 768, cos1269o2c k) + cos1269o2c 769 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 768) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_768
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 769 - ((4787101/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_769).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_770 : ((213651999/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 770, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 770, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 769, cos1269o2c k) + cos1269o2c 770 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 769) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_769
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 770 - ((4379647/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_770).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_771 : ((5250843/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 771, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 771, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 770, cos1269o2c k) + cos1269o2c 771 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 770) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_770
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 771 - ((-3617279/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_771).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_772 : ((50184887/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 772, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 772, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 771, cos1269o2c k) + cos1269o2c 772 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 771) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_771
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 772 - ((-2323293/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_772).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_773 : ((191704379/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 773, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 773, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 772, cos1269o2c k) + cos1269o2c 773 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 772) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_772
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 773 - ((-9034169/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_773).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_774 : ((188677647/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 774, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 774, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 773, cos1269o2c k) + cos1269o2c 774 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 773) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_773
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 774 - ((-756433/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_774).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_775 : ((24196847/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 775, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 775, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 774, cos1269o2c k) + cos1269o2c 775 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 774) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_774
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 775 - ((4898129/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_775).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_776 : ((20328541/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 776, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 776, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 775, cos1269o2c k) + cos1269o2c 776 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 775) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_775
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 776 - ((4855817/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_776).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_777 : ((52917211/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 777, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 777, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 776, cos1269o2c k) + cos1269o2c 777 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 776) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_776
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 777 - ((4192217/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_777).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_778 : ((8537667/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 778, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 778, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 777, cos1269o2c k) + cos1269o2c 778 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 777) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_777
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 778 - ((1773831/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_778).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_779 : ((41499063/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 779, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 779, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 778, cos1269o2c k) + cos1269o2c 779 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 778) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_778
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 779 - ((-74317/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_779).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_780 : ((98783179/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 780, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 780, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 779, cos1269o2c k) + cos1269o2c 780 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 779) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_779
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 780 - ((-9927957/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_780).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_781 : ((94935419/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 781, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 781, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 780, cos1269o2c k) + cos1269o2c 781 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 780) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_780
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 781 - ((-192363/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_781).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_782 : ((94604777/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 782, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 782, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 781, cos1269o2c k) + cos1269o2c 782 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 781) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_781
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 782 - ((-165071/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_782).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_783 : ((97993221/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 783, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 783, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 782, cos1269o2c k) + cos1269o2c 783 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 782) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_782
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 783 - ((211809/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_783).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_784 : ((41196827/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 784, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 784, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 783, cos1269o2c k) + cos1269o2c 784 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 783) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_783
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 784 - ((9998693/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_784).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_785 : ((106501449/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 785, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 785, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 784, cos1269o2c k) + cos1269o2c 785 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 784) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_784
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 785 - ((7019763/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_785).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_786 : ((212706443/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 786, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 786, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 785, cos1269o2c k) + cos1269o2c 786 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 785) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_785
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 786 - ((-59091/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_786).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_787 : ((3207557/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 787, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 787, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 786, cos1269o2c k) + cos1269o2c 787 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 786) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_786
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 787 - ((-1484359/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_787).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_788 : ((19530799/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 788, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 788, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 787, cos1269o2c k) + cos1269o2c 788 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 787) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_787
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 788 - ((-4987329/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_788).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_789 : ((7556171/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 789, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 789, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 788, cos1269o2c k) + cos1269o2c 789 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 788) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_788
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 789 - ((-1280543/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_789).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_790 : ((18998919/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 790, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 790, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 789, cos1269o2c k) + cos1269o2c 790 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 789) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_789
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 790 - ((217183/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_790).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_791 : ((19789211/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 791, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 791, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 790, cos1269o2c k) + cos1269o2c 791 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 790) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_790
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 791 - ((98799/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_791).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_792 : ((207790063/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 792, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 792, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 791, cos1269o2c k) + cos1269o2c 792 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 791) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_791
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 792 - ((9898953/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_792).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_793 : ((106831527/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 793, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 793, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 792, cos1269o2c k) + cos1269o2c 793 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 792) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_792
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 793 - ((5873991/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_793).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_794 : ((211952929/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 794, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 794, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 793, cos1269o2c k) + cos1269o2c 794 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 793) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_793
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 794 - ((-13673/80000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_794).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_795 : ((203700807/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 795, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 795, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 794, cos1269o2c k) + cos1269o2c 795 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 794) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_794
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 795 - ((-4125561/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_795).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_796 : ((4847339/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 796, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 796, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 795, cos1269o2c k) + cos1269o2c 796 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 795) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_795
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 796 - ((-9806247/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_796).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_797 : ((3768747/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 797, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 797, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 796, cos1269o2c k) + cos1269o2c 797 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 796) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_796
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 797 - ((-545521/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_797).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_798 : ((95302437/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 798, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 798, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 797, cos1269o2c k) + cos1269o2c 798 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 797) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_797
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 798 - ((542131/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_798).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_799 : ((199089363/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 799, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 799, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 798, cos1269o2c k) + cos1269o2c 799 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 798) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_798
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 799 - ((8485489/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_799).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_800 : ((104405501/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 800, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 800, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 799, cos1269o2c k) + cos1269o2c 800 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 799) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_799
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 800 - ((9722639/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_800).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_801 : ((213969413/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 801, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 801, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 800, cos1269o2c k) + cos1269o2c 801 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 800) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_800
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 801 - ((5159411/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_801).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_802 : ((211498639/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 802, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 802, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 801, cos1269o2c k) + cos1269o2c 802 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 801) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_801
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 802 - ((-1234887/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_802).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_803 : ((202872533/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 803, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 803, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 802, cos1269o2c k) + cos1269o2c 803 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 802) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_802
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 803 - ((-4312553/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_803).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_804 : ((193205193/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 804, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 804, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 803, cos1269o2c k) + cos1269o2c 804 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 803) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_803
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 804 - ((-483317/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_804).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_805 : ((188208827/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 805, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 805, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 804, cos1269o2c k) + cos1269o2c 805 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 804) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_804
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 805 - ((-2497683/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_805).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_806 : ((47705929/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 806, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 806, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 805, cos1269o2c k) + cos1269o2c 806 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 805) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_805
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 806 - ((2615889/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_806).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_807 : ((199503829/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 807, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 807, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 806, cos1269o2c k) + cos1269o2c 807 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 806) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_806
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 807 - ((8681113/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_807).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_808 : ((209150201/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 808, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 808, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 807, cos1269o2c k) + cos1269o2c 808 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 807) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_807
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 808 - ((2411843/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_808).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_809 : ((214114793/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 809, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 809, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 808, cos1269o2c k) + cos1269o2c 809 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 808) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_808
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 809 - ((620699/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_809).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_810 : ((105751367/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 810, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 810, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 809, cos1269o2c k) + cos1269o2c 810 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 809) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_809
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 810 - ((-2611059/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_810).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_811 : ((202842399/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 811, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 811, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 810, cos1269o2c k) + cos1269o2c 811 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 810) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_810
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 811 - ((-1731867/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_811).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_812 : ((96586331/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 812, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 812, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 811, cos1269o2c k) + cos1269o2c 812 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 811) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_811
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 812 - ((-9668737/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_812).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_813 : ((188101307/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 813, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 813, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 812, cos1269o2c k) + cos1269o2c 813 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 812) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_812
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 813 - ((-1014071/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_813).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_814 : ((190556761/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 814, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 814, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 813, cos1269o2c k) + cos1269o2c 814 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 813) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_813
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 814 - ((1228227/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_814).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_815 : ((199114429/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 815, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 815, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 814, cos1269o2c k) + cos1269o2c 815 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 814) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_814
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 815 - ((2139667/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_815).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_816 : ((208839847/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 816, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 816, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 815, cos1269o2c k) + cos1269o2c 816 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 815) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_815
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 816 - ((4863209/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_816).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_817 : ((10707227/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 817, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 817, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 816, cos1269o2c k) + cos1269o2c 817 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 816) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_816
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 817 - ((5305693/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_817).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_818 : ((6624731/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 818, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 818, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 817, cos1269o2c k) + cos1269o2c 818 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 817) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_817
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 818 - ((-538037/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_818).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_819 : ((40723747/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 819, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 819, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 818, cos1269o2c k) + cos1269o2c 819 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 818) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_818
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 819 - ((-8371657/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_819).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_820 : ((96904177/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 820, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 820, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 819, cos1269o2c k) + cos1269o2c 820 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 819) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_819
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 820 - ((-9809381/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_820).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_821 : ((188145231/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 821, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 821, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 820, cos1269o2c k) + cos1269o2c 821 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 820) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_820
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 821 - ((-5662123/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_821).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_822 : ((5932503/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 822, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 822, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 821, cos1269o2c k) + cos1269o2c 822 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 821) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_821
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 822 - ((339173/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_822).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_823 : ((197925861/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 823, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 823, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 822, cos1269o2c k) + cos1269o2c 823 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 822) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_822
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 823 - ((1617353/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_823).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_824 : ((20782481/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 824, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 824, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 823, cos1269o2c k) + cos1269o2c 824 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 823) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_823
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 824 - ((9899949/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_824).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_825 : ((1069763/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 825, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 825, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 824, cos1269o2c k) + cos1269o2c 825 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 824) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_824
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 825 - ((612879/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_825).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_826 : ((21286441/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 826, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 826, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 825, cos1269o2c k) + cos1269o2c 826 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 825) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_825
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 826 - ((-108719/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_826).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_827 : ((51294407/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 827, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 827, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 826, cos1269o2c k) + cos1269o2c 827 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 826) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_826
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 827 - ((-3842891/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_827).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_828 : ((195202979/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 828, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 828, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 827, cos1269o2c k) + cos1269o2c 828 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 827) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_827
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 828 - ((-9973649/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_828).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_829 : ((23564481/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 829, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 829, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 828, cos1269o2c k) + cos1269o2c 829 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 828) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_828
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 829 - ((-6686131/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_829).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_830 : ((188840901/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 830, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 830, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 829, cos1269o2c k) + cos1269o2c 830 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 829) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_829
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 830 - ((326053/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_830).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_831 : ((195989377/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 831, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 831, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 830, cos1269o2c k) + cos1269o2c 831 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 830) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_830
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 831 - ((1787369/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_831).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_832 : ((205987757/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 832, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 832, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 831, cos1269o2c k) + cos1269o2c 832 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 831) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_831
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 832 - ((499969/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_832).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_833 : ((213296639/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 833, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 833, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 832, cos1269o2c k) + cos1269o2c 833 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 832) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_832
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 833 - ((3654941/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_833).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_834 : ((26735033/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 834, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 834, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 833, cos1269o2c k) + cos1269o2c 834 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 833) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_833
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 834 - ((4677/80000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_834).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_835 : ((6481973/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 835, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 835, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 834, cos1269o2c k) + cos1269o2c 835 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 834) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_834
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 835 - ((-100877/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_835).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_836 : ((197482069/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 836, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 836, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 835, cos1269o2c k) + cos1269o2c 836 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 835) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_835
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 836 - ((-9940067/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_836).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_837 : ((94756921/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 837, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 837, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 836, cos1269o2c k) + cos1269o2c 837 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 836) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_836
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 837 - ((-7967227/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_837).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_838 : ((93939123/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 838, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 838, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 837, cos1269o2c k) + cos1269o2c 838 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 837) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_837
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 838 - ((-408649/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_838).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_839 : ((193461681/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 839, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 839, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 838, cos1269o2c k) + cos1269o2c 839 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 838) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_838
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 839 - ((1116887/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_839).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_840 : ((50803523/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 840, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 840, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 839, cos1269o2c k) + cos1269o2c 840 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 839) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_839
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 840 - ((9753411/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_840).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_841 : ((2647863/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 841, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 841, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 840, cos1269o2c k) + cos1269o2c 841 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 840) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_840
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 841 - ((2153987/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_841).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_842 : ((107316753/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 842, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 842, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 841, cos1269o2c k) + cos1269o2c 842 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 841) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_841
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 842 - ((1402733/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_842).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_843 : ((105057509/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 843, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 843, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 842, cos1269o2c k) + cos1269o2c 843 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 842) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_842
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 843 - ((-282343/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_843).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_844 : ((50179963/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 844, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 844, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 843, cos1269o2c k) + cos1269o2c 844 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 843) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_843
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 844 - ((-4697083/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_844).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_845 : ((38302821/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 845, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 845, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 844, cos1269o2c k) + cos1269o2c 845 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 844) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_844
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 845 - ((-9204747/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_845).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_846 : ((93722909/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 846, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 846, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 845, cos1269o2c k) + cos1269o2c 846 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 845) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_845
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 846 - ((-4067287/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_846).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_847 : ((38138307/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 847, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 847, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 846, cos1269o2c k) + cos1269o2c 847 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 846) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_846
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 847 - ((3246717/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_847).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_848 : ((199507163/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 848, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 848, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 847, cos1269o2c k) + cos1269o2c 848 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 847) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_847
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 848 - ((2204157/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_848).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_849 : ((26147427/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 849, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 849, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 848, cos1269o2c k) + cos1269o2c 849 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 848) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_848
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 849 - ((9673253/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_849).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_850 : ((42910779/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 850, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 850, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 849, cos1269o2c k) + cos1269o2c 850 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 849) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_849
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 850 - ((5375479/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_850).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_851 : ((8511087/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 851, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 851, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 850, cos1269o2c k) + cos1269o2c 851 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 850) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_850
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 851 - ((-44393/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_851).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_852 : ((102398973/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 852, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 852, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 851, cos1269o2c k) + cos1269o2c 852 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 851) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_851
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 852 - ((-7978229/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_852).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_853 : ((194844097/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 853, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 853, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 852, cos1269o2c k) + cos1269o2c 853 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 852) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_852
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 853 - ((-9952849/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_853).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_854 : ((470431/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 854, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 854, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 853, cos1269o2c k) + cos1269o2c 854 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 853) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_853
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 854 - ((-6670697/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_854).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_855 : ((37658853/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 855, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 855, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 854, cos1269o2c k) + cos1269o2c 855 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 854) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_854
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 855 - ((24573/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_855).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_856 : ((195138529/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 856, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 856, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 855, cos1269o2c k) + cos1269o2c 856 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 855) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_855
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 856 - ((427829/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_856).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_857 : ((205108663/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 857, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 857, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 856, cos1269o2c k) + cos1269o2c 857 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 856) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_856
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 857 - ((4985567/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_857).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_858 : ((106491837/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 858, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 858, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 857, cos1269o2c k) + cos1269o2c 858 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 857) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_857
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 858 - ((7876011/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_858).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_859 : ((26831573/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 859, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 859, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 858, cos1269o2c k) + cos1269o2c 859 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 858) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_858
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 859 - ((166991/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_859).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_860 : ((104625947/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 860, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 860, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 859, cos1269o2c k) + cos1269o2c 860 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 859) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_859
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 860 - ((-539969/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_860).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_861 : ((199594699/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 861, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 861, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 860, cos1269o2c k) + cos1269o2c 861 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 860) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_860
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 861 - ((-1931239/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_861).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_862 : ((190693849/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 862, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 862, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 861, cos1269o2c k) + cos1269o2c 862 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 861) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_861
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 862 - ((-177997/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_862).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_863 : ((93577227/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 863, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 863, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 862, cos1269o2c k) + cos1269o2c 863 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 862) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_862
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 863 - ((-707679/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_863).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_864 : ((190798879/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 864, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 864, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 863, cos1269o2c k) + cos1269o2c 864 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 863) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_863
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 864 - ((145817/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_864).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_865 : ((24967759/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 865, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 865, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 864, cos1269o2c k) + cos1269o2c 865 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 864) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_864
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 865 - ((8944193/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_865).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_866 : ((52345071/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 866, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 866, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 865, cos1269o2c k) + cos1269o2c 866 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 865) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_865
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 866 - ((2409803/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_866).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_867 : ((26846053/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 867, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 867, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 866, cos1269o2c k) + cos1269o2c 867 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 866) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_866
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 867 - ((269457/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_867).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_868 : ((106575749/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 868, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 868, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 867, cos1269o2c k) + cos1269o2c 868 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 867) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_867
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 868 - ((-807963/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_868).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_869 : ((51340441/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 869, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 869, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 868, cos1269o2c k) + cos1269o2c 869 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 868) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_868
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 869 - ((-3894367/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_869).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_870 : ((97687091/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 870, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 870, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 869, cos1269o2c k) + cos1269o2c 870 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 869) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_869
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 870 - ((-4993291/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_870).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_871 : ((11766793/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 871, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 871, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 870, cos1269o2c k) + cos1269o2c 871 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 870) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_870
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 871 - ((-3552247/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_871).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_872 : ((187647609/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 872, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 872, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 871, cos1269o2c k) + cos1269o2c 872 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 871) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_871
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 872 - ((-620079/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_872).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_873 : ((96909201/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 873, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 873, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 872, cos1269o2c k) + cos1269o2c 873 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 872) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_872
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 873 - ((6171793/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_873).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_874 : ((203657147/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 874, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 874, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 873, cos1269o2c k) + cos1269o2c 874 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 873) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_873
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 874 - ((1967949/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_874).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_875 : ((212200763/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 875, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 875, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 874, cos1269o2c k) + cos1269o2c 875 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 874) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_874
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 875 - ((1068077/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_875).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_876 : ((215152937/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 876, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 876, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 875, cos1269o2c k) + cos1269o2c 876 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 875) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_875
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 876 - ((1476587/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_876).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_877 : ((26379601/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 877, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 877, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 876, cos1269o2c k) + cos1269o2c 877 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 876) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_876
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 877 - ((-4115129/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_877).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_878 : ((40383937/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 878, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 878, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 877, cos1269o2c k) + cos1269o2c 878 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 877) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_877
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 878 - ((-9116123/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_878).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_879 : ((192361323/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 879, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 879, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 878, cos1269o2c k) + cos1269o2c 879 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 878) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_878
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 879 - ((-4778681/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_879).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_880 : ((18712781/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 880, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 880, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 879, cos1269o2c k) + cos1269o2c 880 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 879) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_879
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 880 - ((-5232513/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_880).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_881 : ((188818041/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 881, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 881, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 880, cos1269o2c k) + cos1269o2c 881 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 880) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_880
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 881 - ((1691231/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_881).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_882 : ((7863439/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 882, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 882, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 881, cos1269o2c k) + cos1269o2c 882 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 881) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_881
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 882 - ((3884467/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_882).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_883 : ((10328889/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 883, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 883, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 882, cos1269o2c k) + cos1269o2c 883 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 882) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_882
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 883 - ((1998561/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_883).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_884 : ((13365763/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 884, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 884, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 883, cos1269o2c k) + cos1269o2c 884 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 883) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_883
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 884 - ((1818857/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_884).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_885 : ((53705837/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 885, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 885, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 884, cos1269o2c k) + cos1269o2c 885 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 884) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_884
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 885 - ((48607/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_885).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_886 : ((209018729/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 886, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 886, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 885, cos1269o2c k) + cos1269o2c 886 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 885) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_885
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 886 - ((-5803619/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_886).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_887 : ((99647351/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 887, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 887, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 886, cos1269o2c k) + cos1269o2c 887 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 886) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_886
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 887 - ((-9723027/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_887).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_888 : ((190419357/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 888, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 888, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 887, cos1269o2c k) + cos1269o2c 888 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 887) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_887
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 888 - ((-1774869/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_888).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_889 : ((23341409/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 889, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 889, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 888, cos1269o2c k) + cos1269o2c 889 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 888) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_888
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 889 - ((-737417/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_889).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_890 : ((95012219/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 890, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 890, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 889, cos1269o2c k) + cos1269o2c 890 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 889) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_889
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 890 - ((1647083/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_890).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_891 : ((39737769/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 891, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 891, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 890, cos1269o2c k) + cos1269o2c 891 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 890) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_890
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 891 - ((8665407/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_891).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_892 : ((104254743/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 892, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 892, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 891, cos1269o2c k) + cos1269o2c 892 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 891) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_891
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 892 - ((9821641/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_892).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_893 : ((214724231/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 893, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 893, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 892, cos1269o2c k) + cos1269o2c 893 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 892) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_892
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 893 - ((1243149/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_893).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_894 : ((2679119/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 894, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 894, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 893, cos1269o2c k) + cos1269o2c 894 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 893) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_893
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 894 - ((-393711/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_894).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_895 : ((207521267/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 895, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 895, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 894, cos1269o2c k) + cos1269o2c 895 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 894) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_894
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 895 - ((-6807253/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_895).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_896 : ((197584607/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 896, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 896, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 895, cos1269o2c k) + cos1269o2c 896 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 895) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_895
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 896 - ((-496783/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_896).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_897 : ((47324443/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 897, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 897, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 896, cos1269o2c k) + cos1269o2c 897 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 896) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_896
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 897 - ((-1657167/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_897).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_898 : ((46658297/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 898, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 898, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 897, cos1269o2c k) + cos1269o2c 898 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 897) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_897
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 898 - ((-83237/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_898).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_899 : ((38172133/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 899, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 899, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 898, cos1269o2c k) + cos1269o2c 899 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 898) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_898
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 899 - ((4228477/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_899).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_900 : ((49988541/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 900, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 900, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 899, cos1269o2c k) + cos1269o2c 900 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 899) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_899
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 900 - ((9094499/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_900).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_901 : ((52393827/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 901, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 901, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 900, cos1269o2c k) + cos1269o2c 901 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 900) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_900
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 901 - ((75173/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_901).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_902 : ((215147639/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 902, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 902, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 901, cos1269o2c k) + cos1269o2c 902 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 901) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_901
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 902 - ((5573331/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_902).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_903 : ((107015207/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 903, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 903, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 902, cos1269o2c k) + cos1269o2c 903 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 902) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_902
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 903 - ((-44649/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_903).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_904 : ((41351639/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 904, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 904, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 903, cos1269o2c k) + cos1269o2c 904 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 903) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_903
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 904 - ((-7271219/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_904).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_905 : ((196772411/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 905, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 905, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 904, cos1269o2c k) + cos1269o2c 905 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 904) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_904
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 905 - ((-624049/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_905).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_906 : ((37756767/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 906, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 906, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 905, cos1269o2c k) + cos1269o2c 906 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 905) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_905
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 906 - ((-998447/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_906).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_907 : ((37309749/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 907, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 907, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 906, cos1269o2c k) + cos1269o2c 907 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 906) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_906
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 907 - ((-223409/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_907).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_908 : ((23888857/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 908, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 908, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 907, cos1269o2c k) + cos1269o2c 908 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 907) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_907
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 908 - ((4563111/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_908).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_909 : ((8013043/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 909, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 909, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 908, cos1269o2c k) + cos1269o2c 909 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 908) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_908
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 909 - ((9216219/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_909).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_910 : ((209881167/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 910, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 910, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 909, cos1269o2c k) + cos1269o2c 910 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 909) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_909
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 910 - ((2389023/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_910).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_911 : ((861269/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 911, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 911, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 910, cos1269o2c k) + cos1269o2c 911 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 910) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_910
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 911 - ((5437083/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_911).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_912 : ((107053307/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 912, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 912, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 911, cos1269o2c k) + cos1269o2c 912 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 911) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_911
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 912 - ((-302409/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_912).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_913 : ((206817331/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 913, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 913, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 912, cos1269o2c k) + cos1269o2c 913 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 912) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_912
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 913 - ((-7288283/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_913).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_914 : ((196834087/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 914, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 914, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 913, cos1269o2c k) + cos1269o2c 914 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 913) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_913
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 914 - ((-2495561/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_914).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_915 : ((9438889/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 915, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 915, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 914, cos1269o2c k) + cos1269o2c 915 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 914) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_914
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 915 - ((-8055307/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_915).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_916 : ((186365711/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 916, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 916, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 915, cos1269o2c k) + cos1269o2c 916 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 915) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_915
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 916 - ((-2411069/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_916).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_917 : ((23837941/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 917, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 917, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 916, cos1269o2c k) + cos1269o2c 917 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 916) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_916
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 917 - ((4338817/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_917).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_918 : ((7991611/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 918, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 918, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 917, cos1269o2c k) + cos1269o2c 918 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 917) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_917
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 918 - ((9087747/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_918).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_919 : ((209452183/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 919, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 919, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 918, cos1269o2c k) + cos1269o2c 919 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 918) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_918
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 919 - ((2415727/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_919).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_920 : ((8610589/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 920, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 920, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 919, cos1269o2c k) + cos1269o2c 920 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 919) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_919
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 920 - ((2906771/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_920).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_921 : ((214574983/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 921, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 921, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 920, cos1269o2c k) + cos1269o2c 921 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 920) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_920
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 921 - ((-344371/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_921).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_922 : ((207702997/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 922, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 922, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 921, cos1269o2c k) + cos1269o2c 922 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 921) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_921
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 922 - ((-3435493/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_922).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_923 : ((98890329/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 923, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 923, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 922, cos1269o2c k) + cos1269o2c 923 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 922) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_922
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 923 - ((-9921339/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_923).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_924 : ((7572609/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 924, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 924, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 923, cos1269o2c k) + cos1269o2c 924 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 923) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_923
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 924 - ((-8464433/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_924).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_925 : ((186140749/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 925, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 925, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 924, cos1269o2c k) + cos1269o2c 925 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 924) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_924
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 925 - ((-793369/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_925).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_926 : ((189687243/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 926, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 926, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 925, cos1269o2c k) + cos1269o2c 926 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 925) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_925
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 926 - ((1773747/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_926).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_927 : ((99173909/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 927, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 927, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 926, cos1269o2c k) + cos1269o2c 927 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 926) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_926
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 927 - ((346463/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_927).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_928 : ((2602723/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 928, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 928, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 927, cos1269o2c k) + cos1269o2c 928 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 927) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_927
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 928 - ((4935511/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_928).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_929 : ((26857573/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 929, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 929, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 928, cos1269o2c k) + cos1269o2c 929 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 928) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_928
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 929 - ((207617/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_929).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_930 : ((107650027/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 930, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 930, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 929, cos1269o2c k) + cos1269o2c 930 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 929) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_929
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 930 - ((44047/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_930).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_931 : ((26168059/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 931, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 931, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 930, cos1269o2c k) + cos1269o2c 931 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 930) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_930
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 931 - ((-2977291/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_931).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_932 : ((1247867/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 932, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 932, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 931, cos1269o2c k) + cos1269o2c 932 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 931) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_931
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 932 - ((-605297/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_932).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_933 : ((190562553/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 933, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 933, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 932, cos1269o2c k) + cos1269o2c 933 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 932) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_932
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 933 - ((-9095167/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_933).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_934 : ((186100191/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 934, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 934, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 933, cos1269o2c k) + cos1269o2c 934 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 933) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_933
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 934 - ((-2230681/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_934).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_935 : ((9412383/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 935, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 935, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 934, cos1269o2c k) + cos1269o2c 935 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 934) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_934
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 935 - ((2148469/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_935).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_936 : ((245059/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 936, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 936, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 935, cos1269o2c k) + cos1269o2c 936 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 935) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_935
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 936 - ((390027/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_936).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_937 : ((206046189/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 937, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 937, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 936, cos1269o2c k) + cos1269o2c 937 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 936) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_936
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 937 - ((9999989/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_937).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_938 : ((10691581/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 938, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 938, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 937, cos1269o2c k) + cos1269o2c 938 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 937) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_937
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 938 - ((7786431/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_938).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_939 : ((107989083/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 939, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 939, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 938, cos1269o2c k) + cos1269o2c 939 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 938) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_938
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 939 - ((1073773/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_939).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_940 : ((105773677/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 940, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 940, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 939, cos1269o2c k) + cos1269o2c 940 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 939) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_939
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 940 - ((-1107453/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_940).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_941 : ((101243497/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 941, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 941, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 940, cos1269o2c k) + cos1269o2c 941 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 940) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_940
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 941 - ((-56621/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_941).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_942 : ((96382401/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 942, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 942, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 941, cos1269o2c k) + cos1269o2c 942 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 941) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_941
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 942 - ((-1215149/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_942).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_943 : ((186625521/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 943, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 943, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 942, cos1269o2c k) + cos1269o2c 943 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 942) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_942
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 943 - ((-6138281/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_943).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_944 : ((93370289/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 944, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 944, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 943, cos1269o2c k) + cos1269o2c 944 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 943) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_943
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 944 - ((116057/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_944).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_945 : ((96527011/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 945, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 945, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 944, cos1269o2c k) + cos1269o2c 945 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 944) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_944
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 945 - ((1578611/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_945).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_946 : ((20281993/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 946, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 946, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 945, cos1269o2c k) + cos1269o2c 946 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 945) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_945
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 946 - ((2441727/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_946).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_947 : ((105902933/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 947, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 947, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 946, cos1269o2c k) + cos1269o2c 947 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 946) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_946
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 947 - ((1123367/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_947).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_948 : ((54032023/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 948, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 948, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 947, cos1269o2c k) + cos1269o2c 948 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 947) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_947
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 948 - ((2161613/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_948).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_949 : ((213927009/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 949, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 949, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 948, cos1269o2c k) + cos1269o2c 949 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 948) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_948
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 949 - ((-2200083/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_949).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_950 : ((103077399/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 950, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 950, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 949, cos1269o2c k) + cos1269o2c 950 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 949) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_949
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 950 - ((-7771211/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_950).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_951 : ((24519333/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 951, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 951, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 950, cos1269o2c k) + cos1269o2c 951 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 950) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_950
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 951 - ((-4999567/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_951).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_952 : ((94107633/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 952, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 952, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 951, cos1269o2c k) + cos1269o2c 952 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 951) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_951
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 952 - ((-3969199/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_952).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_953 : ((4643279/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 953, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 953, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 952, cos1269o2c k) + cos1269o2c 953 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 952) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_952
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 953 - ((-1241553/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_953).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_954 : ((189757157/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 954, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 954, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 953, cos1269o2c k) + cos1269o2c 954 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 953) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_953
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 954 - ((4026997/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_954).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_955 : ((198572103/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 955, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 955, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 954, cos1269o2c k) + cos1269o2c 955 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 954) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_954
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 955 - ((4407973/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_955).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_956 : ((6513209/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 956, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 956, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 955, cos1269o2c k) + cos1269o2c 956 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 955) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_955
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 956 - ((1970317/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_956).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_957 : ((8605099/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 957, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 957, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 956, cos1269o2c k) + cos1269o2c 957 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 956) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_956
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 957 - ((6705787/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_957).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_958 : ((215849013/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 958, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 958, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 957, cos1269o2c k) + cos1269o2c 958 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 957) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_957
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 958 - ((361269/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_958).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_959 : ((210287253/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 959, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 959, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 958, cos1269o2c k) + cos1269o2c 959 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 958) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_958
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 959 - ((-139019/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_959).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_960 : ((200793469/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 960, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 960, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 959, cos1269o2c k) + cos1269o2c 960 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 959) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_959
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 960 - ((-593299/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_960).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_961 : ((1196047/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 961, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 961, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 960, cos1269o2c k) + cos1269o2c 961 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 960) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_960
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 961 - ((-9424949/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_961).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_962 : ((37193807/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 962, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 962, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 961, cos1269o2c k) + cos1269o2c 962 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 961) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_961
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 962 - ((-1079497/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_962).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_963 : ((23357241/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 963, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 963, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 962, cos1269o2c k) + cos1269o2c 963 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 962) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_962
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 963 - ((889893/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_963).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_964 : ((24206959/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 964, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 964, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 963, cos1269o2c k) + cos1269o2c 964 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 963) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_963
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 964 - ((849843/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_964).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_965 : ((25439797/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 965, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 965, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 964, cos1269o2c k) + cos1269o2c 965 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 964) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_964
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 965 - ((1232963/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_965).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_966 : ((212331937/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 966, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 966, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 965, cos1269o2c k) + cos1269o2c 966 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 965) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_965
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 966 - ((8814561/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_966).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_967 : ((216431201/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 967, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 967, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 966, cos1269o2c k) + cos1269o2c 967 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 966) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_966
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 967 - ((512533/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_967).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_968 : ((42823591/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 968, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 968, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 967, cos1269o2c k) + cos1269o2c 968 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 967) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_967
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 968 - ((-1156123/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_968).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_969 : ((51588889/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 969, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 969, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 968, cos1269o2c k) + cos1269o2c 969 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 968) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_968
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 969 - ((-7761399/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_969).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_970 : ((98179217/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 970, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 970, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 969, cos1269o2c k) + cos1269o2c 970 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 969) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_969
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 970 - ((-4998061/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_970).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_971 : ((188253287/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 971, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 971, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 970, cos1269o2c k) + cos1269o2c 971 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 970) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_970
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 971 - ((-8104147/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_971).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_972 : ((185376427/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 972, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 972, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 971, cos1269o2c k) + cos1269o2c 972 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 971) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_971
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 972 - ((-143793/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_972).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_973 : ((188904603/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 973, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 973, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 972, cos1269o2c k) + cos1269o2c 973 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 972) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_972
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 973 - ((441147/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_973).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_974 : ((197385241/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 974, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 974, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 973, cos1269o2c k) + cos1269o2c 974 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 973) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_973
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 974 - ((4240819/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_974).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_975 : ((207341237/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 975, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 975, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 974, cos1269o2c k) + cos1269o2c 975 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 974) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_974
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 975 - ((2489249/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_975).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_976 : ((214703311/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 976, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 976, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 975, cos1269o2c k) + cos1269o2c 976 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 975) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_975
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 976 - ((3681537/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_976).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_977 : ((216471011/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 977, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 977, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 976, cos1269o2c k) + cos1269o2c 977 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 976) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_976
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 977 - ((17687/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_977).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_978 : ((211929667/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 978, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 978, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 977, cos1269o2c k) + cos1269o2c 978 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 977) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_977
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 978 - ((-567543/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_978).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_979 : ((40585753/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 979, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 979, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 978, cos1269o2c k) + cos1269o2c 979 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 978) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_978
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 979 - ((-4499951/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_979).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_980 : ((9656031/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 980, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 980, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 979, cos1269o2c k) + cos1269o2c 980 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 979) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_979
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 980 - ((-1961429/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_980).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_981 : ((186473623/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 981, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 981, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 980, cos1269o2c k) + cos1269o2c 981 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 980) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_980
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 981 - ((-6645997/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_981).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_982 : ((5802151/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 982, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 982, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 981, cos1269o2c k) + cos1269o2c 982 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 981) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_981
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 982 - ((-803791/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_982).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_983 : ((95512381/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 983, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 983, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 982, cos1269o2c k) + cos1269o2c 983 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 982) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_982
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 983 - ((535693/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_983).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_984 : ((200381419/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 984, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 984, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 983, cos1269o2c k) + cos1269o2c 984 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 983) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_983
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 984 - ((9357657/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_984).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_985 : ((209979413/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 985, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 985, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 984, cos1269o2c k) + cos1269o2c 985 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 984) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_984
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 985 - ((4799497/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_985).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_986 : ((215972931/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 986, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 986, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 985, cos1269o2c k) + cos1269o2c 986 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 985) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_985
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 986 - ((2997259/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_986).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_987 : ((43193633/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 987, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 987, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 986, cos1269o2c k) + cos1269o2c 987 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 986) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_986
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 987 - ((-1883/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_987).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_988 : ((41994441/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 988, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 988, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 987, cos1269o2c k) + cos1269o2c 988 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 987) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_987
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 988 - ((-74937/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_988).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_989 : ((200377409/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 989, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 989, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 988, cos1269o2c k) + cos1269o2c 989 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 988) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_988
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 989 - ((-2398449/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_989).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_990 : ((47750181/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 990, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 990, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 989, cos1269o2c k) + cos1269o2c 990 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 989) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_989
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 990 - ((-1875137/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_990).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_991 : ((185561537/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 991, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 991, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 990, cos1269o2c k) + cos1269o2c 991 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 990) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_990
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 991 - ((-5438187/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_991).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_992 : ((186209839/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 992, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 992, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 991, cos1269o2c k) + cos1269o2c 992 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 991) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_991
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 992 - ((324651/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_992).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_993 : ((96341673/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 993, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 993, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 992, cos1269o2c k) + cos1269o2c 993 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 992) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_992
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 993 - ((6474507/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_993).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_994 : ((40484767/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 994, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 994, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 993, cos1269o2c k) + cos1269o2c 994 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 993) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_993
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 994 - ((9741489/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_994).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_995 : ((105796791/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 995, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 995, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 994, cos1269o2c k) + cos1269o2c 995 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 994) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_994
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 995 - ((9170747/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_995).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_996 : ((216590213/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 996, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 996, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 995, cos1269o2c k) + cos1269o2c 996 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 995) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_995
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 996 - ((4997631/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_996).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_997 : ((215457687/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 997, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 997, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 996, cos1269o2c k) + cos1269o2c 997 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 996) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_996
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 997 - ((-565763/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_997).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_998 : ((208644093/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 998, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 998, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 997, cos1269o2c k) + cos1269o2c 998 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 997) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_997
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 998 - ((-3406297/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_998).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_999 : ((198815321/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 999, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 999, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 998, cos1269o2c k) + cos1269o2c 999 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 998) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_998
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 999 - ((-2456943/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_999).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1269o2_1000 : ((189805307/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 1000, cos1269o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 1000, cos1269o2c k)
      = (∑ k ∈ Finset.Icc 11 999, cos1269o2c k) + cos1269o2c 1000 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 999) (by norm_num) cos1269o2c
    simpa using h
  have hprev := psum1269o2_999
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1269o2c 1000 - ((-4504507/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1269o2_br_1000).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 32768 in
theorem psum1269o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 1000 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos1269o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum1269o2_11
  · exact le_trans (by norm_num) psum1269o2_12
  · exact le_trans (by norm_num) psum1269o2_13
  · exact le_trans (by norm_num) psum1269o2_14
  · exact le_trans (by norm_num) psum1269o2_15
  · exact le_trans (by norm_num) psum1269o2_16
  · exact le_trans (by norm_num) psum1269o2_17
  · exact le_trans (by norm_num) psum1269o2_18
  · exact le_trans (by norm_num) psum1269o2_19
  · exact le_trans (by norm_num) psum1269o2_20
  · exact le_trans (by norm_num) psum1269o2_21
  · exact le_trans (by norm_num) psum1269o2_22
  · exact le_trans (by norm_num) psum1269o2_23
  · exact le_trans (by norm_num) psum1269o2_24
  · exact le_trans (by norm_num) psum1269o2_25
  · exact le_trans (by norm_num) psum1269o2_26
  · exact le_trans (by norm_num) psum1269o2_27
  · exact le_trans (by norm_num) psum1269o2_28
  · exact le_trans (by norm_num) psum1269o2_29
  · exact le_trans (by norm_num) psum1269o2_30
  · exact le_trans (by norm_num) psum1269o2_31
  · exact le_trans (by norm_num) psum1269o2_32
  · exact le_trans (by norm_num) psum1269o2_33
  · exact le_trans (by norm_num) psum1269o2_34
  · exact le_trans (by norm_num) psum1269o2_35
  · exact le_trans (by norm_num) psum1269o2_36
  · exact le_trans (by norm_num) psum1269o2_37
  · exact le_trans (by norm_num) psum1269o2_38
  · exact le_trans (by norm_num) psum1269o2_39
  · exact le_trans (by norm_num) psum1269o2_40
  · exact le_trans (by norm_num) psum1269o2_41
  · exact le_trans (by norm_num) psum1269o2_42
  · exact le_trans (by norm_num) psum1269o2_43
  · exact le_trans (by norm_num) psum1269o2_44
  · exact le_trans (by norm_num) psum1269o2_45
  · exact le_trans (by norm_num) psum1269o2_46
  · exact le_trans (by norm_num) psum1269o2_47
  · exact le_trans (by norm_num) psum1269o2_48
  · exact le_trans (by norm_num) psum1269o2_49
  · exact le_trans (by norm_num) psum1269o2_50
  · exact le_trans (by norm_num) psum1269o2_51
  · exact le_trans (by norm_num) psum1269o2_52
  · exact le_trans (by norm_num) psum1269o2_53
  · exact le_trans (by norm_num) psum1269o2_54
  · exact le_trans (by norm_num) psum1269o2_55
  · exact le_trans (by norm_num) psum1269o2_56
  · exact le_trans (by norm_num) psum1269o2_57
  · exact le_trans (by norm_num) psum1269o2_58
  · exact le_trans (by norm_num) psum1269o2_59
  · exact le_trans (by norm_num) psum1269o2_60
  · exact le_trans (by norm_num) psum1269o2_61
  · exact le_trans (by norm_num) psum1269o2_62
  · exact le_trans (by norm_num) psum1269o2_63
  · exact le_trans (by norm_num) psum1269o2_64
  · exact le_trans (by norm_num) psum1269o2_65
  · exact le_trans (by norm_num) psum1269o2_66
  · exact le_trans (by norm_num) psum1269o2_67
  · exact le_trans (by norm_num) psum1269o2_68
  · exact le_trans (by norm_num) psum1269o2_69
  · exact le_trans (by norm_num) psum1269o2_70
  · exact le_trans (by norm_num) psum1269o2_71
  · exact le_trans (by norm_num) psum1269o2_72
  · exact le_trans (by norm_num) psum1269o2_73
  · exact le_trans (by norm_num) psum1269o2_74
  · exact le_trans (by norm_num) psum1269o2_75
  · exact le_trans (by norm_num) psum1269o2_76
  · exact le_trans (by norm_num) psum1269o2_77
  · exact le_trans (by norm_num) psum1269o2_78
  · exact le_trans (by norm_num) psum1269o2_79
  · exact le_trans (by norm_num) psum1269o2_80
  · exact le_trans (by norm_num) psum1269o2_81
  · exact le_trans (by norm_num) psum1269o2_82
  · exact le_trans (by norm_num) psum1269o2_83
  · exact le_trans (by norm_num) psum1269o2_84
  · exact le_trans (by norm_num) psum1269o2_85
  · exact le_trans (by norm_num) psum1269o2_86
  · exact le_trans (by norm_num) psum1269o2_87
  · exact le_trans (by norm_num) psum1269o2_88
  · exact le_trans (by norm_num) psum1269o2_89
  · exact le_trans (by norm_num) psum1269o2_90
  · exact le_trans (by norm_num) psum1269o2_91
  · exact le_trans (by norm_num) psum1269o2_92
  · exact le_trans (by norm_num) psum1269o2_93
  · exact le_trans (by norm_num) psum1269o2_94
  · exact le_trans (by norm_num) psum1269o2_95
  · exact le_trans (by norm_num) psum1269o2_96
  · exact le_trans (by norm_num) psum1269o2_97
  · exact le_trans (by norm_num) psum1269o2_98
  · exact le_trans (by norm_num) psum1269o2_99
  · exact le_trans (by norm_num) psum1269o2_100
  · exact le_trans (by norm_num) psum1269o2_101
  · exact le_trans (by norm_num) psum1269o2_102
  · exact le_trans (by norm_num) psum1269o2_103
  · exact le_trans (by norm_num) psum1269o2_104
  · exact le_trans (by norm_num) psum1269o2_105
  · exact le_trans (by norm_num) psum1269o2_106
  · exact le_trans (by norm_num) psum1269o2_107
  · exact le_trans (by norm_num) psum1269o2_108
  · exact le_trans (by norm_num) psum1269o2_109
  · exact le_trans (by norm_num) psum1269o2_110
  · exact le_trans (by norm_num) psum1269o2_111
  · exact le_trans (by norm_num) psum1269o2_112
  · exact le_trans (by norm_num) psum1269o2_113
  · exact le_trans (by norm_num) psum1269o2_114
  · exact le_trans (by norm_num) psum1269o2_115
  · exact le_trans (by norm_num) psum1269o2_116
  · exact le_trans (by norm_num) psum1269o2_117
  · exact le_trans (by norm_num) psum1269o2_118
  · exact le_trans (by norm_num) psum1269o2_119
  · exact le_trans (by norm_num) psum1269o2_120
  · exact le_trans (by norm_num) psum1269o2_121
  · exact le_trans (by norm_num) psum1269o2_122
  · exact le_trans (by norm_num) psum1269o2_123
  · exact le_trans (by norm_num) psum1269o2_124
  · exact le_trans (by norm_num) psum1269o2_125
  · exact le_trans (by norm_num) psum1269o2_126
  · exact le_trans (by norm_num) psum1269o2_127
  · exact le_trans (by norm_num) psum1269o2_128
  · exact le_trans (by norm_num) psum1269o2_129
  · exact le_trans (by norm_num) psum1269o2_130
  · exact le_trans (by norm_num) psum1269o2_131
  · exact le_trans (by norm_num) psum1269o2_132
  · exact le_trans (by norm_num) psum1269o2_133
  · exact le_trans (by norm_num) psum1269o2_134
  · exact le_trans (by norm_num) psum1269o2_135
  · exact le_trans (by norm_num) psum1269o2_136
  · exact le_trans (by norm_num) psum1269o2_137
  · exact le_trans (by norm_num) psum1269o2_138
  · exact le_trans (by norm_num) psum1269o2_139
  · exact le_trans (by norm_num) psum1269o2_140
  · exact le_trans (by norm_num) psum1269o2_141
  · exact le_trans (by norm_num) psum1269o2_142
  · exact le_trans (by norm_num) psum1269o2_143
  · exact le_trans (by norm_num) psum1269o2_144
  · exact le_trans (by norm_num) psum1269o2_145
  · exact le_trans (by norm_num) psum1269o2_146
  · exact le_trans (by norm_num) psum1269o2_147
  · exact le_trans (by norm_num) psum1269o2_148
  · exact le_trans (by norm_num) psum1269o2_149
  · exact le_trans (by norm_num) psum1269o2_150
  · exact le_trans (by norm_num) psum1269o2_151
  · exact le_trans (by norm_num) psum1269o2_152
  · exact le_trans (by norm_num) psum1269o2_153
  · exact le_trans (by norm_num) psum1269o2_154
  · exact le_trans (by norm_num) psum1269o2_155
  · exact le_trans (by norm_num) psum1269o2_156
  · exact le_trans (by norm_num) psum1269o2_157
  · exact le_trans (by norm_num) psum1269o2_158
  · exact le_trans (by norm_num) psum1269o2_159
  · exact le_trans (by norm_num) psum1269o2_160
  · exact le_trans (by norm_num) psum1269o2_161
  · exact le_trans (by norm_num) psum1269o2_162
  · exact le_trans (by norm_num) psum1269o2_163
  · exact le_trans (by norm_num) psum1269o2_164
  · exact le_trans (by norm_num) psum1269o2_165
  · exact le_trans (by norm_num) psum1269o2_166
  · exact le_trans (by norm_num) psum1269o2_167
  · exact le_trans (by norm_num) psum1269o2_168
  · exact le_trans (by norm_num) psum1269o2_169
  · exact le_trans (by norm_num) psum1269o2_170
  · exact le_trans (by norm_num) psum1269o2_171
  · exact le_trans (by norm_num) psum1269o2_172
  · exact le_trans (by norm_num) psum1269o2_173
  · exact le_trans (by norm_num) psum1269o2_174
  · exact le_trans (by norm_num) psum1269o2_175
  · exact le_trans (by norm_num) psum1269o2_176
  · exact le_trans (by norm_num) psum1269o2_177
  · exact le_trans (by norm_num) psum1269o2_178
  · exact le_trans (by norm_num) psum1269o2_179
  · exact le_trans (by norm_num) psum1269o2_180
  · exact le_trans (by norm_num) psum1269o2_181
  · exact le_trans (by norm_num) psum1269o2_182
  · exact le_trans (by norm_num) psum1269o2_183
  · exact le_trans (by norm_num) psum1269o2_184
  · exact le_trans (by norm_num) psum1269o2_185
  · exact le_trans (by norm_num) psum1269o2_186
  · exact le_trans (by norm_num) psum1269o2_187
  · exact le_trans (by norm_num) psum1269o2_188
  · exact le_trans (by norm_num) psum1269o2_189
  · exact le_trans (by norm_num) psum1269o2_190
  · exact le_trans (by norm_num) psum1269o2_191
  · exact le_trans (by norm_num) psum1269o2_192
  · exact le_trans (by norm_num) psum1269o2_193
  · exact le_trans (by norm_num) psum1269o2_194
  · exact le_trans (by norm_num) psum1269o2_195
  · exact le_trans (by norm_num) psum1269o2_196
  · exact le_trans (by norm_num) psum1269o2_197
  · exact le_trans (by norm_num) psum1269o2_198
  · exact le_trans (by norm_num) psum1269o2_199
  · exact le_trans (by norm_num) psum1269o2_200
  · exact le_trans (by norm_num) psum1269o2_201
  · exact le_trans (by norm_num) psum1269o2_202
  · exact le_trans (by norm_num) psum1269o2_203
  · exact le_trans (by norm_num) psum1269o2_204
  · exact le_trans (by norm_num) psum1269o2_205
  · exact le_trans (by norm_num) psum1269o2_206
  · exact le_trans (by norm_num) psum1269o2_207
  · exact le_trans (by norm_num) psum1269o2_208
  · exact le_trans (by norm_num) psum1269o2_209
  · exact le_trans (by norm_num) psum1269o2_210
  · exact le_trans (by norm_num) psum1269o2_211
  · exact le_trans (by norm_num) psum1269o2_212
  · exact le_trans (by norm_num) psum1269o2_213
  · exact le_trans (by norm_num) psum1269o2_214
  · exact le_trans (by norm_num) psum1269o2_215
  · exact le_trans (by norm_num) psum1269o2_216
  · exact le_trans (by norm_num) psum1269o2_217
  · exact le_trans (by norm_num) psum1269o2_218
  · exact le_trans (by norm_num) psum1269o2_219
  · exact le_trans (by norm_num) psum1269o2_220
  · exact le_trans (by norm_num) psum1269o2_221
  · exact le_trans (by norm_num) psum1269o2_222
  · exact le_trans (by norm_num) psum1269o2_223
  · exact le_trans (by norm_num) psum1269o2_224
  · exact le_trans (by norm_num) psum1269o2_225
  · exact le_trans (by norm_num) psum1269o2_226
  · exact le_trans (by norm_num) psum1269o2_227
  · exact le_trans (by norm_num) psum1269o2_228
  · exact le_trans (by norm_num) psum1269o2_229
  · exact le_trans (by norm_num) psum1269o2_230
  · exact le_trans (by norm_num) psum1269o2_231
  · exact le_trans (by norm_num) psum1269o2_232
  · exact le_trans (by norm_num) psum1269o2_233
  · exact le_trans (by norm_num) psum1269o2_234
  · exact le_trans (by norm_num) psum1269o2_235
  · exact le_trans (by norm_num) psum1269o2_236
  · exact le_trans (by norm_num) psum1269o2_237
  · exact le_trans (by norm_num) psum1269o2_238
  · exact le_trans (by norm_num) psum1269o2_239
  · exact le_trans (by norm_num) psum1269o2_240
  · exact le_trans (by norm_num) psum1269o2_241
  · exact le_trans (by norm_num) psum1269o2_242
  · exact le_trans (by norm_num) psum1269o2_243
  · exact le_trans (by norm_num) psum1269o2_244
  · exact le_trans (by norm_num) psum1269o2_245
  · exact le_trans (by norm_num) psum1269o2_246
  · exact le_trans (by norm_num) psum1269o2_247
  · exact le_trans (by norm_num) psum1269o2_248
  · exact le_trans (by norm_num) psum1269o2_249
  · exact le_trans (by norm_num) psum1269o2_250
  · exact le_trans (by norm_num) psum1269o2_251
  · exact le_trans (by norm_num) psum1269o2_252
  · exact le_trans (by norm_num) psum1269o2_253
  · exact le_trans (by norm_num) psum1269o2_254
  · exact le_trans (by norm_num) psum1269o2_255
  · exact le_trans (by norm_num) psum1269o2_256
  · exact le_trans (by norm_num) psum1269o2_257
  · exact le_trans (by norm_num) psum1269o2_258
  · exact le_trans (by norm_num) psum1269o2_259
  · exact le_trans (by norm_num) psum1269o2_260
  · exact le_trans (by norm_num) psum1269o2_261
  · exact le_trans (by norm_num) psum1269o2_262
  · exact le_trans (by norm_num) psum1269o2_263
  · exact le_trans (by norm_num) psum1269o2_264
  · exact le_trans (by norm_num) psum1269o2_265
  · exact le_trans (by norm_num) psum1269o2_266
  · exact le_trans (by norm_num) psum1269o2_267
  · exact le_trans (by norm_num) psum1269o2_268
  · exact le_trans (by norm_num) psum1269o2_269
  · exact le_trans (by norm_num) psum1269o2_270
  · exact le_trans (by norm_num) psum1269o2_271
  · exact le_trans (by norm_num) psum1269o2_272
  · exact le_trans (by norm_num) psum1269o2_273
  · exact le_trans (by norm_num) psum1269o2_274
  · exact le_trans (by norm_num) psum1269o2_275
  · exact le_trans (by norm_num) psum1269o2_276
  · exact le_trans (by norm_num) psum1269o2_277
  · exact le_trans (by norm_num) psum1269o2_278
  · exact le_trans (by norm_num) psum1269o2_279
  · exact le_trans (by norm_num) psum1269o2_280
  · exact le_trans (by norm_num) psum1269o2_281
  · exact le_trans (by norm_num) psum1269o2_282
  · exact le_trans (by norm_num) psum1269o2_283
  · exact le_trans (by norm_num) psum1269o2_284
  · exact le_trans (by norm_num) psum1269o2_285
  · exact le_trans (by norm_num) psum1269o2_286
  · exact le_trans (by norm_num) psum1269o2_287
  · exact le_trans (by norm_num) psum1269o2_288
  · exact le_trans (by norm_num) psum1269o2_289
  · exact le_trans (by norm_num) psum1269o2_290
  · exact le_trans (by norm_num) psum1269o2_291
  · exact le_trans (by norm_num) psum1269o2_292
  · exact le_trans (by norm_num) psum1269o2_293
  · exact le_trans (by norm_num) psum1269o2_294
  · exact le_trans (by norm_num) psum1269o2_295
  · exact le_trans (by norm_num) psum1269o2_296
  · exact le_trans (by norm_num) psum1269o2_297
  · exact le_trans (by norm_num) psum1269o2_298
  · exact le_trans (by norm_num) psum1269o2_299
  · exact le_trans (by norm_num) psum1269o2_300
  · exact le_trans (by norm_num) psum1269o2_301
  · exact le_trans (by norm_num) psum1269o2_302
  · exact le_trans (by norm_num) psum1269o2_303
  · exact le_trans (by norm_num) psum1269o2_304
  · exact le_trans (by norm_num) psum1269o2_305
  · exact le_trans (by norm_num) psum1269o2_306
  · exact le_trans (by norm_num) psum1269o2_307
  · exact le_trans (by norm_num) psum1269o2_308
  · exact le_trans (by norm_num) psum1269o2_309
  · exact le_trans (by norm_num) psum1269o2_310
  · exact le_trans (by norm_num) psum1269o2_311
  · exact le_trans (by norm_num) psum1269o2_312
  · exact le_trans (by norm_num) psum1269o2_313
  · exact le_trans (by norm_num) psum1269o2_314
  · exact le_trans (by norm_num) psum1269o2_315
  · exact le_trans (by norm_num) psum1269o2_316
  · exact le_trans (by norm_num) psum1269o2_317
  · exact le_trans (by norm_num) psum1269o2_318
  · exact le_trans (by norm_num) psum1269o2_319
  · exact le_trans (by norm_num) psum1269o2_320
  · exact le_trans (by norm_num) psum1269o2_321
  · exact le_trans (by norm_num) psum1269o2_322
  · exact le_trans (by norm_num) psum1269o2_323
  · exact le_trans (by norm_num) psum1269o2_324
  · exact le_trans (by norm_num) psum1269o2_325
  · exact le_trans (by norm_num) psum1269o2_326
  · exact le_trans (by norm_num) psum1269o2_327
  · exact le_trans (by norm_num) psum1269o2_328
  · exact le_trans (by norm_num) psum1269o2_329
  · exact le_trans (by norm_num) psum1269o2_330
  · exact le_trans (by norm_num) psum1269o2_331
  · exact le_trans (by norm_num) psum1269o2_332
  · exact le_trans (by norm_num) psum1269o2_333
  · exact le_trans (by norm_num) psum1269o2_334
  · exact le_trans (by norm_num) psum1269o2_335
  · exact le_trans (by norm_num) psum1269o2_336
  · exact le_trans (by norm_num) psum1269o2_337
  · exact le_trans (by norm_num) psum1269o2_338
  · exact le_trans (by norm_num) psum1269o2_339
  · exact le_trans (by norm_num) psum1269o2_340
  · exact le_trans (by norm_num) psum1269o2_341
  · exact le_trans (by norm_num) psum1269o2_342
  · exact le_trans (by norm_num) psum1269o2_343
  · exact le_trans (by norm_num) psum1269o2_344
  · exact le_trans (by norm_num) psum1269o2_345
  · exact le_trans (by norm_num) psum1269o2_346
  · exact le_trans (by norm_num) psum1269o2_347
  · exact le_trans (by norm_num) psum1269o2_348
  · exact le_trans (by norm_num) psum1269o2_349
  · exact le_trans (by norm_num) psum1269o2_350
  · exact le_trans (by norm_num) psum1269o2_351
  · exact le_trans (by norm_num) psum1269o2_352
  · exact le_trans (by norm_num) psum1269o2_353
  · exact le_trans (by norm_num) psum1269o2_354
  · exact le_trans (by norm_num) psum1269o2_355
  · exact le_trans (by norm_num) psum1269o2_356
  · exact le_trans (by norm_num) psum1269o2_357
  · exact le_trans (by norm_num) psum1269o2_358
  · exact le_trans (by norm_num) psum1269o2_359
  · exact le_trans (by norm_num) psum1269o2_360
  · exact le_trans (by norm_num) psum1269o2_361
  · exact le_trans (by norm_num) psum1269o2_362
  · exact le_trans (by norm_num) psum1269o2_363
  · exact le_trans (by norm_num) psum1269o2_364
  · exact le_trans (by norm_num) psum1269o2_365
  · exact le_trans (by norm_num) psum1269o2_366
  · exact le_trans (by norm_num) psum1269o2_367
  · exact le_trans (by norm_num) psum1269o2_368
  · exact le_trans (by norm_num) psum1269o2_369
  · exact le_trans (by norm_num) psum1269o2_370
  · exact le_trans (by norm_num) psum1269o2_371
  · exact le_trans (by norm_num) psum1269o2_372
  · exact le_trans (by norm_num) psum1269o2_373
  · exact le_trans (by norm_num) psum1269o2_374
  · exact le_trans (by norm_num) psum1269o2_375
  · exact le_trans (by norm_num) psum1269o2_376
  · exact le_trans (by norm_num) psum1269o2_377
  · exact le_trans (by norm_num) psum1269o2_378
  · exact le_trans (by norm_num) psum1269o2_379
  · exact le_trans (by norm_num) psum1269o2_380
  · exact le_trans (by norm_num) psum1269o2_381
  · exact le_trans (by norm_num) psum1269o2_382
  · exact le_trans (by norm_num) psum1269o2_383
  · exact le_trans (by norm_num) psum1269o2_384
  · exact le_trans (by norm_num) psum1269o2_385
  · exact le_trans (by norm_num) psum1269o2_386
  · exact le_trans (by norm_num) psum1269o2_387
  · exact le_trans (by norm_num) psum1269o2_388
  · exact le_trans (by norm_num) psum1269o2_389
  · exact le_trans (by norm_num) psum1269o2_390
  · exact le_trans (by norm_num) psum1269o2_391
  · exact le_trans (by norm_num) psum1269o2_392
  · exact le_trans (by norm_num) psum1269o2_393
  · exact le_trans (by norm_num) psum1269o2_394
  · exact le_trans (by norm_num) psum1269o2_395
  · exact le_trans (by norm_num) psum1269o2_396
  · exact le_trans (by norm_num) psum1269o2_397
  · exact le_trans (by norm_num) psum1269o2_398
  · exact le_trans (by norm_num) psum1269o2_399
  · exact le_trans (by norm_num) psum1269o2_400
  · exact le_trans (by norm_num) psum1269o2_401
  · exact le_trans (by norm_num) psum1269o2_402
  · exact le_trans (by norm_num) psum1269o2_403
  · exact le_trans (by norm_num) psum1269o2_404
  · exact le_trans (by norm_num) psum1269o2_405
  · exact le_trans (by norm_num) psum1269o2_406
  · exact le_trans (by norm_num) psum1269o2_407
  · exact le_trans (by norm_num) psum1269o2_408
  · exact le_trans (by norm_num) psum1269o2_409
  · exact le_trans (by norm_num) psum1269o2_410
  · exact le_trans (by norm_num) psum1269o2_411
  · exact le_trans (by norm_num) psum1269o2_412
  · exact le_trans (by norm_num) psum1269o2_413
  · exact le_trans (by norm_num) psum1269o2_414
  · exact le_trans (by norm_num) psum1269o2_415
  · exact le_trans (by norm_num) psum1269o2_416
  · exact le_trans (by norm_num) psum1269o2_417
  · exact le_trans (by norm_num) psum1269o2_418
  · exact le_trans (by norm_num) psum1269o2_419
  · exact le_trans (by norm_num) psum1269o2_420
  · exact le_trans (by norm_num) psum1269o2_421
  · exact le_trans (by norm_num) psum1269o2_422
  · exact le_trans (by norm_num) psum1269o2_423
  · exact le_trans (by norm_num) psum1269o2_424
  · exact le_trans (by norm_num) psum1269o2_425
  · exact le_trans (by norm_num) psum1269o2_426
  · exact le_trans (by norm_num) psum1269o2_427
  · exact le_trans (by norm_num) psum1269o2_428
  · exact le_trans (by norm_num) psum1269o2_429
  · exact le_trans (by norm_num) psum1269o2_430
  · exact le_trans (by norm_num) psum1269o2_431
  · exact le_trans (by norm_num) psum1269o2_432
  · exact le_trans (by norm_num) psum1269o2_433
  · exact le_trans (by norm_num) psum1269o2_434
  · exact le_trans (by norm_num) psum1269o2_435
  · exact le_trans (by norm_num) psum1269o2_436
  · exact le_trans (by norm_num) psum1269o2_437
  · exact le_trans (by norm_num) psum1269o2_438
  · exact le_trans (by norm_num) psum1269o2_439
  · exact le_trans (by norm_num) psum1269o2_440
  · exact le_trans (by norm_num) psum1269o2_441
  · exact le_trans (by norm_num) psum1269o2_442
  · exact le_trans (by norm_num) psum1269o2_443
  · exact le_trans (by norm_num) psum1269o2_444
  · exact le_trans (by norm_num) psum1269o2_445
  · exact le_trans (by norm_num) psum1269o2_446
  · exact le_trans (by norm_num) psum1269o2_447
  · exact le_trans (by norm_num) psum1269o2_448
  · exact le_trans (by norm_num) psum1269o2_449
  · exact le_trans (by norm_num) psum1269o2_450
  · exact le_trans (by norm_num) psum1269o2_451
  · exact le_trans (by norm_num) psum1269o2_452
  · exact le_trans (by norm_num) psum1269o2_453
  · exact le_trans (by norm_num) psum1269o2_454
  · exact le_trans (by norm_num) psum1269o2_455
  · exact le_trans (by norm_num) psum1269o2_456
  · exact le_trans (by norm_num) psum1269o2_457
  · exact le_trans (by norm_num) psum1269o2_458
  · exact le_trans (by norm_num) psum1269o2_459
  · exact le_trans (by norm_num) psum1269o2_460
  · exact le_trans (by norm_num) psum1269o2_461
  · exact le_trans (by norm_num) psum1269o2_462
  · exact le_trans (by norm_num) psum1269o2_463
  · exact le_trans (by norm_num) psum1269o2_464
  · exact le_trans (by norm_num) psum1269o2_465
  · exact le_trans (by norm_num) psum1269o2_466
  · exact le_trans (by norm_num) psum1269o2_467
  · exact le_trans (by norm_num) psum1269o2_468
  · exact le_trans (by norm_num) psum1269o2_469
  · exact le_trans (by norm_num) psum1269o2_470
  · exact le_trans (by norm_num) psum1269o2_471
  · exact le_trans (by norm_num) psum1269o2_472
  · exact le_trans (by norm_num) psum1269o2_473
  · exact le_trans (by norm_num) psum1269o2_474
  · exact le_trans (by norm_num) psum1269o2_475
  · exact le_trans (by norm_num) psum1269o2_476
  · exact le_trans (by norm_num) psum1269o2_477
  · exact le_trans (by norm_num) psum1269o2_478
  · exact le_trans (by norm_num) psum1269o2_479
  · exact le_trans (by norm_num) psum1269o2_480
  · exact le_trans (by norm_num) psum1269o2_481
  · exact le_trans (by norm_num) psum1269o2_482
  · exact le_trans (by norm_num) psum1269o2_483
  · exact le_trans (by norm_num) psum1269o2_484
  · exact le_trans (by norm_num) psum1269o2_485
  · exact le_trans (by norm_num) psum1269o2_486
  · exact le_trans (by norm_num) psum1269o2_487
  · exact le_trans (by norm_num) psum1269o2_488
  · exact le_trans (by norm_num) psum1269o2_489
  · exact le_trans (by norm_num) psum1269o2_490
  · exact le_trans (by norm_num) psum1269o2_491
  · exact le_trans (by norm_num) psum1269o2_492
  · exact le_trans (by norm_num) psum1269o2_493
  · exact le_trans (by norm_num) psum1269o2_494
  · exact le_trans (by norm_num) psum1269o2_495
  · exact le_trans (by norm_num) psum1269o2_496
  · exact le_trans (by norm_num) psum1269o2_497
  · exact le_trans (by norm_num) psum1269o2_498
  · exact le_trans (by norm_num) psum1269o2_499
  · exact le_trans (by norm_num) psum1269o2_500
  · exact le_trans (by norm_num) psum1269o2_501
  · exact le_trans (by norm_num) psum1269o2_502
  · exact le_trans (by norm_num) psum1269o2_503
  · exact le_trans (by norm_num) psum1269o2_504
  · exact le_trans (by norm_num) psum1269o2_505
  · exact le_trans (by norm_num) psum1269o2_506
  · exact le_trans (by norm_num) psum1269o2_507
  · exact le_trans (by norm_num) psum1269o2_508
  · exact le_trans (by norm_num) psum1269o2_509
  · exact le_trans (by norm_num) psum1269o2_510
  · exact le_trans (by norm_num) psum1269o2_511
  · exact le_trans (by norm_num) psum1269o2_512
  · exact le_trans (by norm_num) psum1269o2_513
  · exact le_trans (by norm_num) psum1269o2_514
  · exact le_trans (by norm_num) psum1269o2_515
  · exact le_trans (by norm_num) psum1269o2_516
  · exact le_trans (by norm_num) psum1269o2_517
  · exact le_trans (by norm_num) psum1269o2_518
  · exact le_trans (by norm_num) psum1269o2_519
  · exact le_trans (by norm_num) psum1269o2_520
  · exact le_trans (by norm_num) psum1269o2_521
  · exact le_trans (by norm_num) psum1269o2_522
  · exact le_trans (by norm_num) psum1269o2_523
  · exact le_trans (by norm_num) psum1269o2_524
  · exact le_trans (by norm_num) psum1269o2_525
  · exact le_trans (by norm_num) psum1269o2_526
  · exact le_trans (by norm_num) psum1269o2_527
  · exact le_trans (by norm_num) psum1269o2_528
  · exact le_trans (by norm_num) psum1269o2_529
  · exact le_trans (by norm_num) psum1269o2_530
  · exact le_trans (by norm_num) psum1269o2_531
  · exact le_trans (by norm_num) psum1269o2_532
  · exact le_trans (by norm_num) psum1269o2_533
  · exact le_trans (by norm_num) psum1269o2_534
  · exact le_trans (by norm_num) psum1269o2_535
  · exact le_trans (by norm_num) psum1269o2_536
  · exact le_trans (by norm_num) psum1269o2_537
  · exact le_trans (by norm_num) psum1269o2_538
  · exact le_trans (by norm_num) psum1269o2_539
  · exact le_trans (by norm_num) psum1269o2_540
  · exact le_trans (by norm_num) psum1269o2_541
  · exact le_trans (by norm_num) psum1269o2_542
  · exact le_trans (by norm_num) psum1269o2_543
  · exact le_trans (by norm_num) psum1269o2_544
  · exact le_trans (by norm_num) psum1269o2_545
  · exact le_trans (by norm_num) psum1269o2_546
  · exact le_trans (by norm_num) psum1269o2_547
  · exact le_trans (by norm_num) psum1269o2_548
  · exact le_trans (by norm_num) psum1269o2_549
  · exact le_trans (by norm_num) psum1269o2_550
  · exact le_trans (by norm_num) psum1269o2_551
  · exact le_trans (by norm_num) psum1269o2_552
  · exact le_trans (by norm_num) psum1269o2_553
  · exact le_trans (by norm_num) psum1269o2_554
  · exact le_trans (by norm_num) psum1269o2_555
  · exact le_trans (by norm_num) psum1269o2_556
  · exact le_trans (by norm_num) psum1269o2_557
  · exact le_trans (by norm_num) psum1269o2_558
  · exact le_trans (by norm_num) psum1269o2_559
  · exact le_trans (by norm_num) psum1269o2_560
  · exact le_trans (by norm_num) psum1269o2_561
  · exact le_trans (by norm_num) psum1269o2_562
  · exact le_trans (by norm_num) psum1269o2_563
  · exact le_trans (by norm_num) psum1269o2_564
  · exact le_trans (by norm_num) psum1269o2_565
  · exact le_trans (by norm_num) psum1269o2_566
  · exact le_trans (by norm_num) psum1269o2_567
  · exact le_trans (by norm_num) psum1269o2_568
  · exact le_trans (by norm_num) psum1269o2_569
  · exact le_trans (by norm_num) psum1269o2_570
  · exact le_trans (by norm_num) psum1269o2_571
  · exact le_trans (by norm_num) psum1269o2_572
  · exact le_trans (by norm_num) psum1269o2_573
  · exact le_trans (by norm_num) psum1269o2_574
  · exact le_trans (by norm_num) psum1269o2_575
  · exact le_trans (by norm_num) psum1269o2_576
  · exact le_trans (by norm_num) psum1269o2_577
  · exact le_trans (by norm_num) psum1269o2_578
  · exact le_trans (by norm_num) psum1269o2_579
  · exact le_trans (by norm_num) psum1269o2_580
  · exact le_trans (by norm_num) psum1269o2_581
  · exact le_trans (by norm_num) psum1269o2_582
  · exact le_trans (by norm_num) psum1269o2_583
  · exact le_trans (by norm_num) psum1269o2_584
  · exact le_trans (by norm_num) psum1269o2_585
  · exact le_trans (by norm_num) psum1269o2_586
  · exact le_trans (by norm_num) psum1269o2_587
  · exact le_trans (by norm_num) psum1269o2_588
  · exact le_trans (by norm_num) psum1269o2_589
  · exact le_trans (by norm_num) psum1269o2_590
  · exact le_trans (by norm_num) psum1269o2_591
  · exact le_trans (by norm_num) psum1269o2_592
  · exact le_trans (by norm_num) psum1269o2_593
  · exact le_trans (by norm_num) psum1269o2_594
  · exact le_trans (by norm_num) psum1269o2_595
  · exact le_trans (by norm_num) psum1269o2_596
  · exact le_trans (by norm_num) psum1269o2_597
  · exact le_trans (by norm_num) psum1269o2_598
  · exact le_trans (by norm_num) psum1269o2_599
  · exact le_trans (by norm_num) psum1269o2_600
  · exact le_trans (by norm_num) psum1269o2_601
  · exact le_trans (by norm_num) psum1269o2_602
  · exact le_trans (by norm_num) psum1269o2_603
  · exact le_trans (by norm_num) psum1269o2_604
  · exact le_trans (by norm_num) psum1269o2_605
  · exact le_trans (by norm_num) psum1269o2_606
  · exact le_trans (by norm_num) psum1269o2_607
  · exact le_trans (by norm_num) psum1269o2_608
  · exact le_trans (by norm_num) psum1269o2_609
  · exact le_trans (by norm_num) psum1269o2_610
  · exact le_trans (by norm_num) psum1269o2_611
  · exact le_trans (by norm_num) psum1269o2_612
  · exact le_trans (by norm_num) psum1269o2_613
  · exact le_trans (by norm_num) psum1269o2_614
  · exact le_trans (by norm_num) psum1269o2_615
  · exact le_trans (by norm_num) psum1269o2_616
  · exact le_trans (by norm_num) psum1269o2_617
  · exact le_trans (by norm_num) psum1269o2_618
  · exact le_trans (by norm_num) psum1269o2_619
  · exact le_trans (by norm_num) psum1269o2_620
  · exact le_trans (by norm_num) psum1269o2_621
  · exact le_trans (by norm_num) psum1269o2_622
  · exact le_trans (by norm_num) psum1269o2_623
  · exact le_trans (by norm_num) psum1269o2_624
  · exact le_trans (by norm_num) psum1269o2_625
  · exact le_trans (by norm_num) psum1269o2_626
  · exact le_trans (by norm_num) psum1269o2_627
  · exact le_trans (by norm_num) psum1269o2_628
  · exact le_trans (by norm_num) psum1269o2_629
  · exact le_trans (by norm_num) psum1269o2_630
  · exact le_trans (by norm_num) psum1269o2_631
  · exact le_trans (by norm_num) psum1269o2_632
  · exact le_trans (by norm_num) psum1269o2_633
  · exact le_trans (by norm_num) psum1269o2_634
  · exact le_trans (by norm_num) psum1269o2_635
  · exact le_trans (by norm_num) psum1269o2_636
  · exact le_trans (by norm_num) psum1269o2_637
  · exact le_trans (by norm_num) psum1269o2_638
  · exact le_trans (by norm_num) psum1269o2_639
  · exact le_trans (by norm_num) psum1269o2_640
  · exact le_trans (by norm_num) psum1269o2_641
  · exact le_trans (by norm_num) psum1269o2_642
  · exact le_trans (by norm_num) psum1269o2_643
  · exact le_trans (by norm_num) psum1269o2_644
  · exact le_trans (by norm_num) psum1269o2_645
  · exact le_trans (by norm_num) psum1269o2_646
  · exact le_trans (by norm_num) psum1269o2_647
  · exact le_trans (by norm_num) psum1269o2_648
  · exact le_trans (by norm_num) psum1269o2_649
  · exact le_trans (by norm_num) psum1269o2_650
  · exact le_trans (by norm_num) psum1269o2_651
  · exact le_trans (by norm_num) psum1269o2_652
  · exact le_trans (by norm_num) psum1269o2_653
  · exact le_trans (by norm_num) psum1269o2_654
  · exact le_trans (by norm_num) psum1269o2_655
  · exact le_trans (by norm_num) psum1269o2_656
  · exact le_trans (by norm_num) psum1269o2_657
  · exact le_trans (by norm_num) psum1269o2_658
  · exact le_trans (by norm_num) psum1269o2_659
  · exact le_trans (by norm_num) psum1269o2_660
  · exact le_trans (by norm_num) psum1269o2_661
  · exact le_trans (by norm_num) psum1269o2_662
  · exact le_trans (by norm_num) psum1269o2_663
  · exact le_trans (by norm_num) psum1269o2_664
  · exact le_trans (by norm_num) psum1269o2_665
  · exact le_trans (by norm_num) psum1269o2_666
  · exact le_trans (by norm_num) psum1269o2_667
  · exact le_trans (by norm_num) psum1269o2_668
  · exact le_trans (by norm_num) psum1269o2_669
  · exact le_trans (by norm_num) psum1269o2_670
  · exact le_trans (by norm_num) psum1269o2_671
  · exact le_trans (by norm_num) psum1269o2_672
  · exact le_trans (by norm_num) psum1269o2_673
  · exact le_trans (by norm_num) psum1269o2_674
  · exact le_trans (by norm_num) psum1269o2_675
  · exact le_trans (by norm_num) psum1269o2_676
  · exact le_trans (by norm_num) psum1269o2_677
  · exact le_trans (by norm_num) psum1269o2_678
  · exact le_trans (by norm_num) psum1269o2_679
  · exact le_trans (by norm_num) psum1269o2_680
  · exact le_trans (by norm_num) psum1269o2_681
  · exact le_trans (by norm_num) psum1269o2_682
  · exact le_trans (by norm_num) psum1269o2_683
  · exact le_trans (by norm_num) psum1269o2_684
  · exact le_trans (by norm_num) psum1269o2_685
  · exact le_trans (by norm_num) psum1269o2_686
  · exact le_trans (by norm_num) psum1269o2_687
  · exact le_trans (by norm_num) psum1269o2_688
  · exact le_trans (by norm_num) psum1269o2_689
  · exact le_trans (by norm_num) psum1269o2_690
  · exact le_trans (by norm_num) psum1269o2_691
  · exact le_trans (by norm_num) psum1269o2_692
  · exact le_trans (by norm_num) psum1269o2_693
  · exact le_trans (by norm_num) psum1269o2_694
  · exact le_trans (by norm_num) psum1269o2_695
  · exact le_trans (by norm_num) psum1269o2_696
  · exact le_trans (by norm_num) psum1269o2_697
  · exact le_trans (by norm_num) psum1269o2_698
  · exact le_trans (by norm_num) psum1269o2_699
  · exact le_trans (by norm_num) psum1269o2_700
  · exact le_trans (by norm_num) psum1269o2_701
  · exact le_trans (by norm_num) psum1269o2_702
  · exact le_trans (by norm_num) psum1269o2_703
  · exact le_trans (by norm_num) psum1269o2_704
  · exact le_trans (by norm_num) psum1269o2_705
  · exact le_trans (by norm_num) psum1269o2_706
  · exact le_trans (by norm_num) psum1269o2_707
  · exact le_trans (by norm_num) psum1269o2_708
  · exact le_trans (by norm_num) psum1269o2_709
  · exact le_trans (by norm_num) psum1269o2_710
  · exact le_trans (by norm_num) psum1269o2_711
  · exact le_trans (by norm_num) psum1269o2_712
  · exact le_trans (by norm_num) psum1269o2_713
  · exact le_trans (by norm_num) psum1269o2_714
  · exact le_trans (by norm_num) psum1269o2_715
  · exact le_trans (by norm_num) psum1269o2_716
  · exact le_trans (by norm_num) psum1269o2_717
  · exact le_trans (by norm_num) psum1269o2_718
  · exact le_trans (by norm_num) psum1269o2_719
  · exact le_trans (by norm_num) psum1269o2_720
  · exact le_trans (by norm_num) psum1269o2_721
  · exact le_trans (by norm_num) psum1269o2_722
  · exact le_trans (by norm_num) psum1269o2_723
  · exact le_trans (by norm_num) psum1269o2_724
  · exact le_trans (by norm_num) psum1269o2_725
  · exact le_trans (by norm_num) psum1269o2_726
  · exact le_trans (by norm_num) psum1269o2_727
  · exact le_trans (by norm_num) psum1269o2_728
  · exact le_trans (by norm_num) psum1269o2_729
  · exact le_trans (by norm_num) psum1269o2_730
  · exact le_trans (by norm_num) psum1269o2_731
  · exact le_trans (by norm_num) psum1269o2_732
  · exact le_trans (by norm_num) psum1269o2_733
  · exact le_trans (by norm_num) psum1269o2_734
  · exact le_trans (by norm_num) psum1269o2_735
  · exact le_trans (by norm_num) psum1269o2_736
  · exact le_trans (by norm_num) psum1269o2_737
  · exact le_trans (by norm_num) psum1269o2_738
  · exact le_trans (by norm_num) psum1269o2_739
  · exact le_trans (by norm_num) psum1269o2_740
  · exact le_trans (by norm_num) psum1269o2_741
  · exact le_trans (by norm_num) psum1269o2_742
  · exact le_trans (by norm_num) psum1269o2_743
  · exact le_trans (by norm_num) psum1269o2_744
  · exact le_trans (by norm_num) psum1269o2_745
  · exact le_trans (by norm_num) psum1269o2_746
  · exact le_trans (by norm_num) psum1269o2_747
  · exact le_trans (by norm_num) psum1269o2_748
  · exact le_trans (by norm_num) psum1269o2_749
  · exact le_trans (by norm_num) psum1269o2_750
  · exact le_trans (by norm_num) psum1269o2_751
  · exact le_trans (by norm_num) psum1269o2_752
  · exact le_trans (by norm_num) psum1269o2_753
  · exact le_trans (by norm_num) psum1269o2_754
  · exact le_trans (by norm_num) psum1269o2_755
  · exact le_trans (by norm_num) psum1269o2_756
  · exact le_trans (by norm_num) psum1269o2_757
  · exact le_trans (by norm_num) psum1269o2_758
  · exact le_trans (by norm_num) psum1269o2_759
  · exact le_trans (by norm_num) psum1269o2_760
  · exact le_trans (by norm_num) psum1269o2_761
  · exact le_trans (by norm_num) psum1269o2_762
  · exact le_trans (by norm_num) psum1269o2_763
  · exact le_trans (by norm_num) psum1269o2_764
  · exact le_trans (by norm_num) psum1269o2_765
  · exact le_trans (by norm_num) psum1269o2_766
  · exact le_trans (by norm_num) psum1269o2_767
  · exact le_trans (by norm_num) psum1269o2_768
  · exact le_trans (by norm_num) psum1269o2_769
  · exact le_trans (by norm_num) psum1269o2_770
  · exact le_trans (by norm_num) psum1269o2_771
  · exact le_trans (by norm_num) psum1269o2_772
  · exact le_trans (by norm_num) psum1269o2_773
  · exact le_trans (by norm_num) psum1269o2_774
  · exact le_trans (by norm_num) psum1269o2_775
  · exact le_trans (by norm_num) psum1269o2_776
  · exact le_trans (by norm_num) psum1269o2_777
  · exact le_trans (by norm_num) psum1269o2_778
  · exact le_trans (by norm_num) psum1269o2_779
  · exact le_trans (by norm_num) psum1269o2_780
  · exact le_trans (by norm_num) psum1269o2_781
  · exact le_trans (by norm_num) psum1269o2_782
  · exact le_trans (by norm_num) psum1269o2_783
  · exact le_trans (by norm_num) psum1269o2_784
  · exact le_trans (by norm_num) psum1269o2_785
  · exact le_trans (by norm_num) psum1269o2_786
  · exact le_trans (by norm_num) psum1269o2_787
  · exact le_trans (by norm_num) psum1269o2_788
  · exact le_trans (by norm_num) psum1269o2_789
  · exact le_trans (by norm_num) psum1269o2_790
  · exact le_trans (by norm_num) psum1269o2_791
  · exact le_trans (by norm_num) psum1269o2_792
  · exact le_trans (by norm_num) psum1269o2_793
  · exact le_trans (by norm_num) psum1269o2_794
  · exact le_trans (by norm_num) psum1269o2_795
  · exact le_trans (by norm_num) psum1269o2_796
  · exact le_trans (by norm_num) psum1269o2_797
  · exact le_trans (by norm_num) psum1269o2_798
  · exact le_trans (by norm_num) psum1269o2_799
  · exact le_trans (by norm_num) psum1269o2_800
  · exact le_trans (by norm_num) psum1269o2_801
  · exact le_trans (by norm_num) psum1269o2_802
  · exact le_trans (by norm_num) psum1269o2_803
  · exact le_trans (by norm_num) psum1269o2_804
  · exact le_trans (by norm_num) psum1269o2_805
  · exact le_trans (by norm_num) psum1269o2_806
  · exact le_trans (by norm_num) psum1269o2_807
  · exact le_trans (by norm_num) psum1269o2_808
  · exact le_trans (by norm_num) psum1269o2_809
  · exact le_trans (by norm_num) psum1269o2_810
  · exact le_trans (by norm_num) psum1269o2_811
  · exact le_trans (by norm_num) psum1269o2_812
  · exact le_trans (by norm_num) psum1269o2_813
  · exact le_trans (by norm_num) psum1269o2_814
  · exact le_trans (by norm_num) psum1269o2_815
  · exact le_trans (by norm_num) psum1269o2_816
  · exact le_trans (by norm_num) psum1269o2_817
  · exact le_trans (by norm_num) psum1269o2_818
  · exact le_trans (by norm_num) psum1269o2_819
  · exact le_trans (by norm_num) psum1269o2_820
  · exact le_trans (by norm_num) psum1269o2_821
  · exact le_trans (by norm_num) psum1269o2_822
  · exact le_trans (by norm_num) psum1269o2_823
  · exact le_trans (by norm_num) psum1269o2_824
  · exact le_trans (by norm_num) psum1269o2_825
  · exact le_trans (by norm_num) psum1269o2_826
  · exact le_trans (by norm_num) psum1269o2_827
  · exact le_trans (by norm_num) psum1269o2_828
  · exact le_trans (by norm_num) psum1269o2_829
  · exact le_trans (by norm_num) psum1269o2_830
  · exact le_trans (by norm_num) psum1269o2_831
  · exact le_trans (by norm_num) psum1269o2_832
  · exact le_trans (by norm_num) psum1269o2_833
  · exact le_trans (by norm_num) psum1269o2_834
  · exact le_trans (by norm_num) psum1269o2_835
  · exact le_trans (by norm_num) psum1269o2_836
  · exact le_trans (by norm_num) psum1269o2_837
  · exact le_trans (by norm_num) psum1269o2_838
  · exact le_trans (by norm_num) psum1269o2_839
  · exact le_trans (by norm_num) psum1269o2_840
  · exact le_trans (by norm_num) psum1269o2_841
  · exact le_trans (by norm_num) psum1269o2_842
  · exact le_trans (by norm_num) psum1269o2_843
  · exact le_trans (by norm_num) psum1269o2_844
  · exact le_trans (by norm_num) psum1269o2_845
  · exact le_trans (by norm_num) psum1269o2_846
  · exact le_trans (by norm_num) psum1269o2_847
  · exact le_trans (by norm_num) psum1269o2_848
  · exact le_trans (by norm_num) psum1269o2_849
  · exact le_trans (by norm_num) psum1269o2_850
  · exact le_trans (by norm_num) psum1269o2_851
  · exact le_trans (by norm_num) psum1269o2_852
  · exact le_trans (by norm_num) psum1269o2_853
  · exact le_trans (by norm_num) psum1269o2_854
  · exact le_trans (by norm_num) psum1269o2_855
  · exact le_trans (by norm_num) psum1269o2_856
  · exact le_trans (by norm_num) psum1269o2_857
  · exact le_trans (by norm_num) psum1269o2_858
  · exact le_trans (by norm_num) psum1269o2_859
  · exact le_trans (by norm_num) psum1269o2_860
  · exact le_trans (by norm_num) psum1269o2_861
  · exact le_trans (by norm_num) psum1269o2_862
  · exact le_trans (by norm_num) psum1269o2_863
  · exact le_trans (by norm_num) psum1269o2_864
  · exact le_trans (by norm_num) psum1269o2_865
  · exact le_trans (by norm_num) psum1269o2_866
  · exact le_trans (by norm_num) psum1269o2_867
  · exact le_trans (by norm_num) psum1269o2_868
  · exact le_trans (by norm_num) psum1269o2_869
  · exact le_trans (by norm_num) psum1269o2_870
  · exact le_trans (by norm_num) psum1269o2_871
  · exact le_trans (by norm_num) psum1269o2_872
  · exact le_trans (by norm_num) psum1269o2_873
  · exact le_trans (by norm_num) psum1269o2_874
  · exact le_trans (by norm_num) psum1269o2_875
  · exact le_trans (by norm_num) psum1269o2_876
  · exact le_trans (by norm_num) psum1269o2_877
  · exact le_trans (by norm_num) psum1269o2_878
  · exact le_trans (by norm_num) psum1269o2_879
  · exact le_trans (by norm_num) psum1269o2_880
  · exact le_trans (by norm_num) psum1269o2_881
  · exact le_trans (by norm_num) psum1269o2_882
  · exact le_trans (by norm_num) psum1269o2_883
  · exact le_trans (by norm_num) psum1269o2_884
  · exact le_trans (by norm_num) psum1269o2_885
  · exact le_trans (by norm_num) psum1269o2_886
  · exact le_trans (by norm_num) psum1269o2_887
  · exact le_trans (by norm_num) psum1269o2_888
  · exact le_trans (by norm_num) psum1269o2_889
  · exact le_trans (by norm_num) psum1269o2_890
  · exact le_trans (by norm_num) psum1269o2_891
  · exact le_trans (by norm_num) psum1269o2_892
  · exact le_trans (by norm_num) psum1269o2_893
  · exact le_trans (by norm_num) psum1269o2_894
  · exact le_trans (by norm_num) psum1269o2_895
  · exact le_trans (by norm_num) psum1269o2_896
  · exact le_trans (by norm_num) psum1269o2_897
  · exact le_trans (by norm_num) psum1269o2_898
  · exact le_trans (by norm_num) psum1269o2_899
  · exact le_trans (by norm_num) psum1269o2_900
  · exact le_trans (by norm_num) psum1269o2_901
  · exact le_trans (by norm_num) psum1269o2_902
  · exact le_trans (by norm_num) psum1269o2_903
  · exact le_trans (by norm_num) psum1269o2_904
  · exact le_trans (by norm_num) psum1269o2_905
  · exact le_trans (by norm_num) psum1269o2_906
  · exact le_trans (by norm_num) psum1269o2_907
  · exact le_trans (by norm_num) psum1269o2_908
  · exact le_trans (by norm_num) psum1269o2_909
  · exact le_trans (by norm_num) psum1269o2_910
  · exact le_trans (by norm_num) psum1269o2_911
  · exact le_trans (by norm_num) psum1269o2_912
  · exact le_trans (by norm_num) psum1269o2_913
  · exact le_trans (by norm_num) psum1269o2_914
  · exact le_trans (by norm_num) psum1269o2_915
  · exact le_trans (by norm_num) psum1269o2_916
  · exact le_trans (by norm_num) psum1269o2_917
  · exact le_trans (by norm_num) psum1269o2_918
  · exact le_trans (by norm_num) psum1269o2_919
  · exact le_trans (by norm_num) psum1269o2_920
  · exact le_trans (by norm_num) psum1269o2_921
  · exact le_trans (by norm_num) psum1269o2_922
  · exact le_trans (by norm_num) psum1269o2_923
  · exact le_trans (by norm_num) psum1269o2_924
  · exact le_trans (by norm_num) psum1269o2_925
  · exact le_trans (by norm_num) psum1269o2_926
  · exact le_trans (by norm_num) psum1269o2_927
  · exact le_trans (by norm_num) psum1269o2_928
  · exact le_trans (by norm_num) psum1269o2_929
  · exact le_trans (by norm_num) psum1269o2_930
  · exact le_trans (by norm_num) psum1269o2_931
  · exact le_trans (by norm_num) psum1269o2_932
  · exact le_trans (by norm_num) psum1269o2_933
  · exact le_trans (by norm_num) psum1269o2_934
  · exact le_trans (by norm_num) psum1269o2_935
  · exact le_trans (by norm_num) psum1269o2_936
  · exact le_trans (by norm_num) psum1269o2_937
  · exact le_trans (by norm_num) psum1269o2_938
  · exact le_trans (by norm_num) psum1269o2_939
  · exact le_trans (by norm_num) psum1269o2_940
  · exact le_trans (by norm_num) psum1269o2_941
  · exact le_trans (by norm_num) psum1269o2_942
  · exact le_trans (by norm_num) psum1269o2_943
  · exact le_trans (by norm_num) psum1269o2_944
  · exact le_trans (by norm_num) psum1269o2_945
  · exact le_trans (by norm_num) psum1269o2_946
  · exact le_trans (by norm_num) psum1269o2_947
  · exact le_trans (by norm_num) psum1269o2_948
  · exact le_trans (by norm_num) psum1269o2_949
  · exact le_trans (by norm_num) psum1269o2_950
  · exact le_trans (by norm_num) psum1269o2_951
  · exact le_trans (by norm_num) psum1269o2_952
  · exact le_trans (by norm_num) psum1269o2_953
  · exact le_trans (by norm_num) psum1269o2_954
  · exact le_trans (by norm_num) psum1269o2_955
  · exact le_trans (by norm_num) psum1269o2_956
  · exact le_trans (by norm_num) psum1269o2_957
  · exact le_trans (by norm_num) psum1269o2_958
  · exact le_trans (by norm_num) psum1269o2_959
  · exact le_trans (by norm_num) psum1269o2_960
  · exact le_trans (by norm_num) psum1269o2_961
  · exact le_trans (by norm_num) psum1269o2_962
  · exact le_trans (by norm_num) psum1269o2_963
  · exact le_trans (by norm_num) psum1269o2_964
  · exact le_trans (by norm_num) psum1269o2_965
  · exact le_trans (by norm_num) psum1269o2_966
  · exact le_trans (by norm_num) psum1269o2_967
  · exact le_trans (by norm_num) psum1269o2_968
  · exact le_trans (by norm_num) psum1269o2_969
  · exact le_trans (by norm_num) psum1269o2_970
  · exact le_trans (by norm_num) psum1269o2_971
  · exact le_trans (by norm_num) psum1269o2_972
  · exact le_trans (by norm_num) psum1269o2_973
  · exact le_trans (by norm_num) psum1269o2_974
  · exact le_trans (by norm_num) psum1269o2_975
  · exact le_trans (by norm_num) psum1269o2_976
  · exact le_trans (by norm_num) psum1269o2_977
  · exact le_trans (by norm_num) psum1269o2_978
  · exact le_trans (by norm_num) psum1269o2_979
  · exact le_trans (by norm_num) psum1269o2_980
  · exact le_trans (by norm_num) psum1269o2_981
  · exact le_trans (by norm_num) psum1269o2_982
  · exact le_trans (by norm_num) psum1269o2_983
  · exact le_trans (by norm_num) psum1269o2_984
  · exact le_trans (by norm_num) psum1269o2_985
  · exact le_trans (by norm_num) psum1269o2_986
  · exact le_trans (by norm_num) psum1269o2_987
  · exact le_trans (by norm_num) psum1269o2_988
  · exact le_trans (by norm_num) psum1269o2_989
  · exact le_trans (by norm_num) psum1269o2_990
  · exact le_trans (by norm_num) psum1269o2_991
  · exact le_trans (by norm_num) psum1269o2_992
  · exact le_trans (by norm_num) psum1269o2_993
  · exact le_trans (by norm_num) psum1269o2_994
  · exact le_trans (by norm_num) psum1269o2_995
  · exact le_trans (by norm_num) psum1269o2_996
  · exact le_trans (by norm_num) psum1269o2_997
  · exact le_trans (by norm_num) psum1269o2_998
  · exact le_trans (by norm_num) psum1269o2_999
  · exact le_trans (by norm_num) psum1269o2_1000

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum1269o2_floor
#print axioms CriticalLinePhasor.DVP.psum1269o2_1000
end AxiomAudit
