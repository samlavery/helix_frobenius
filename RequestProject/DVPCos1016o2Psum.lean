import RequestProject.DVPCos1016o2Table

/-!
# The cosine partial-sum floor, `t = 1016/2` (N = 1000)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 1016/2` segment certificate. -/
def cos1016o2c (n : ℕ) : ℝ := Real.cos (((1016:ℕ):ℝ) * (Real.log n / 2))

theorem psum1016o2_11 : ((6914507/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos1016o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 11 - ((6915507/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum1016o2_12 : ((7617931/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos1016o2c k) + cos1016o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_11
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 12 - ((1664471/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_13 : ((8032693/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos1016o2c k) + cos1016o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_12
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 13 - ((-7202169/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_14 : ((150207/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos1016o2c k) + cos1016o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_13
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 14 - ((-6830037/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_15 : ((10667363/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos1016o2c k) + cos1016o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_14
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 15 - ((9466707/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_16 : ((7857483/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos1016o2c k) + cos1016o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_15
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 16 - ((5048603/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_17 : ((24832801/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos1016o2c k) + cos1016o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_16
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 17 - ((1823767/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_18 : ((2106957/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos1016o2c k) + cos1016o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_17
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 18 - ((-3762231/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_19 : ((30366731/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos1016o2c k) + cos1016o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_18
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 19 - ((9298161/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_20 : ((16514873/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos1016o2c k) + cos1016o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_19
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 20 - ((532803/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_21 : ((3881447/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos1016o2c k) + cos1016o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_20
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 21 - ((1446431/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_22 : ((23677797/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos1016o2c k) + cos1016o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_21
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 22 - ((2135531/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_23 : ((37364099/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos1016o2c k) + cos1016o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_22
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 23 - ((-1998099/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_24 : ((46832339/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos1016o2c k) + cos1016o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_23
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 24 - ((236731/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_25 : ((46931781/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos1016o2c k) + cos1016o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_24
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 25 - ((50221/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_26 : ((38185241/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos1016o2c k) + cos1016o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_25
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 26 - ((-437277/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_27 : ((28352613/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos1016o2c k) + cos1016o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_26
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 27 - ((-2457907/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_28 : ((19871257/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos1016o2c k) + cos1016o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_27
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 28 - ((-2120089/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_29 : ((2497417/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos1016o2c k) + cos1016o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_28
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 29 - ((109079/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_30 : ((936107/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos1016o2c k) + cos1016o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_29
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 30 - ((77946/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_31 : ((11797627/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos1016o2c k) + cos1016o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_30
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 31 - ((-635917/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_32 : ((26250191/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos1016o2c k) + cos1016o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_31
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 32 - ((2655937/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_33 : ((22869011/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos1016o2c k) + cos1016o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_32
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 33 - ((-169009/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_34 : ((612453/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos1016o2c k) + cos1016o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_33
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 34 - ((7754639/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_35 : ((5266309/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos1016o2c k) + cos1016o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_34
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 35 - ((-4778207/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_36 : ((1238397/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos1016o2c k) + cos1016o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_35
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 36 - ((-312471/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_37 : ((7307047/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos1016o2c k) + cos1016o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_36
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 37 - ((2353709/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_38 : ((37264337/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos1016o2c k) + cos1016o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_37
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 38 - ((8037149/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_39 : ((10064967/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos1016o2c k) + cos1016o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_38
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 39 - ((2996531/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_40 : ((40351439/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos1016o2c k) + cos1016o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_39
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 40 - ((92571/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_41 : ((1270883/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos1016o2c k) + cos1016o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_40
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 41 - ((317817/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_42 : ((44157941/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos1016o2c k) + cos1016o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_41
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 42 - ((698137/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_43 : ((13100677/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos1016o2c k) + cos1016o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_42
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 43 - ((8245767/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_44 : ((61994487/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos1016o2c k) + cos1016o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_43
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 44 - ((9592779/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_45 : ((31665961/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos1016o2c k) + cos1016o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_44
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 45 - ((267687/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_46 : ((26894657/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos1016o2c k) + cos1016o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_45
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 46 - ((-1192701/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_47 : ((25736851/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos1016o2c k) + cos1016o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_46
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 47 - ((-578653/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_48 : ((30725177/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos1016o2c k) + cos1016o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_47
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 48 - ((2494413/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_49 : ((27951651/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos1016o2c k) + cos1016o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_48
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 49 - ((-1386513/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_50 : ((53424813/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos1016o2c k) + cos1016o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_49
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 50 - ((-2477489/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_51 : ((12232971/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos1016o2c k) + cos1016o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_50
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 51 - ((3870521/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_52 : ((25732311/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos1016o2c k) + cos1016o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_51
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 52 - ((-9699233/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_53 : ((15365863/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos1016o2c k) + cos1016o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_52
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 53 - ((999983/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_54 : ((51491803/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos1016o2c k) + cos1016o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_53
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 54 - ((-9970649/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_55 : ((15371803/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos1016o2c k) + cos1016o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_54
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 55 - ((9996409/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_56 : ((25963741/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos1016o2c k) + cos1016o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_55
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 56 - ((-955873/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_57 : ((59367811/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos1016o2c k) + cos1016o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_56
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 57 - ((7441329/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_58 : ((56897691/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos1016o2c k) + cos1016o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_57
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 58 - ((-3858/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_59 : ((52178697/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos1016o2c k) + cos1016o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_58
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 59 - ((-2358997/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_60 : ((30996307/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos1016o2c k) + cos1016o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_59
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 60 - ((9814917/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_61 : ((55281311/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos1016o2c k) + cos1016o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_60
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 61 - ((-6710303/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_62 : ((51122091/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos1016o2c k) + cos1016o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_61
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 62 - ((-207911/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_63 : ((12200357/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos1016o2c k) + cos1016o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_62
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 63 - ((4940347/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_64 : ((12217097/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos1016o2c k) + cos1016o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_63
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 64 - ((847/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_65 : ((51085421/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos1016o2c k) + cos1016o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_64
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 65 - ((-1249883/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_66 : ((2009653/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos1016o2c k) + cos1016o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_65
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 66 - ((-105387/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_67 : ((59796233/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos1016o2c k) + cos1016o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_66
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 67 - ((2388977/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_68 : ((65662811/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos1016o2c k) + cos1016o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_67
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 68 - ((2933789/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_69 : ((15203843/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos1016o2c k) + cos1016o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_68
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 69 - ((-4846439/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_70 : ((3176363/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos1016o2c k) + cos1016o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_69
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 70 - ((-2498141/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_71 : ((22240187/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos1016o2c k) + cos1016o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_70
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 71 - ((-3170217/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_72 : ((716033/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos1016o2c k) + cos1016o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_71
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 72 - ((673369/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_73 : ((26698163/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos1016o2c k) + cos1016o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_72
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 73 - ((3785607/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_74 : ((31680267/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos1016o2c k) + cos1016o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_73
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 74 - ((1245651/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_75 : ((36176971/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos1016o2c k) + cos1016o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_74
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 75 - ((1124301/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_76 : ((15717433/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos1016o2c k) + cos1016o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_75
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 76 - ((6234223/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_77 : ((16338141/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos1016o2c k) + cos1016o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_76
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 77 - ((155227/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_78 : ((1642577/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos1016o2c k) + cos1016o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_77
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 78 - ((87829/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_79 : ((5043117/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos1016o2c k) + cos1016o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_78
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 79 - ((-718989/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_80 : ((39101879/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos1016o2c k) + cos1016o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_79
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 80 - ((-1242557/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_81 : ((9431597/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos1016o2c k) + cos1016o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_80
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 81 - ((-1374991/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_82 : ((14637101/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos1016o2c k) + cos1016o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_81
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 82 - ((-2266271/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_83 : ((72155339/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos1016o2c k) + cos1016o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_82
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 83 - ((-514583/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_84 : ((584919/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos1016o2c k) + cos1016o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_83
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 84 - ((120067/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_85 : ((15341317/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos1016o2c k) + cos1016o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_84
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 85 - ((359271/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_86 : ((665737/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos1016o2c k) + cos1016o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_85
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 86 - ((325577/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_87 : ((2881697/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos1016o2c k) + cos1016o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_86
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 87 - ((8998179/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_88 : ((51104967/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos1016o2c k) + cos1016o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_87
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 88 - ((999663/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_89 : ((27658333/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos1016o2c k) + cos1016o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_88
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 89 - ((4212199/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_90 : ((114477153/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos1016o2c k) + cos1016o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_89
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 90 - ((3844821/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_91 : ((13969827/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos1016o2c k) + cos1016o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_90
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 91 - ((-2717537/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_92 : ((103308271/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos1016o2c k) + cos1016o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_91
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 92 - ((-1689869/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_93 : ((46781787/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos1016o2c k) + cos1016o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_92
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 93 - ((-9743697/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_94 : ((17764337/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos1016o2c k) + cos1016o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_93
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 94 - ((-4740889/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_95 : ((92839307/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos1016o2c k) + cos1016o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_94
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 95 - ((2009311/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_96 : ((51325857/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos1016o2c k) + cos1016o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_95
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 96 - ((9813407/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_97 : ((109433337/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos1016o2c k) + cos1016o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_96
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 97 - ((6782623/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_98 : ((106215681/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos1016o2c k) + cos1016o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_97
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 98 - ((-201041/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_99 : ((48141841/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos1016o2c k) + cos1016o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_98
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 99 - ((-9930999/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_100 : ((91394753/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos1016o2c k) + cos1016o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_99
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 100 - ((-4887929/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_101 : ((48985057/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos1016o2c k) + cos1016o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_100
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 101 - ((6576361/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_102 : ((107079101/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos1016o2c k) + cos1016o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_101
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 102 - ((9109987/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_103 : ((52637079/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos1016o2c k) + cos1016o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_102
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 103 - ((-1803943/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_104 : ((19054841/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos1016o2c k) + cos1016o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_103
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 104 - ((-9998953/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_105 : ((18729321/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos1016o2c k) + cos1016o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_104
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 105 - ((-8133/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_106 : ((51646721/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos1016o2c k) + cos1016o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_105
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 106 - ((9647837/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_107 : ((106474213/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos1016o2c k) + cos1016o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_106
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 107 - ((3181771/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_108 : ((6064739/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos1016o2c k) + cos1016o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_107
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 108 - ((-9437389/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_109 : ((734499/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos1016o2c k) + cos1016o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_108
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 109 - ((-377369/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_110 : ((103743263/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos1016o2c k) + cos1016o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_109
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 110 - ((9728391/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_111 : ((1049251/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos1016o2c k) + cos1016o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_110
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 111 - ((1182837/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_112 : ((18986247/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos1016o2c k) + cos1016o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_111
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 112 - ((-1998573/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_113 : ((48627173/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos1016o2c k) + cos1016o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_112
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 113 - ((2324111/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_114 : ((106163769/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos1016o2c k) + cos1016o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_113
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 114 - ((8910423/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_115 : ((49684807/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos1016o2c k) + cos1016o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_114
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 115 - ((-1358631/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_116 : ((94488221/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos1016o2c k) + cos1016o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_115
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 116 - ((-4880393/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_117 : ((815333/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos1016o2c k) + cos1016o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_116
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 117 - ((9875403/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_118 : ((51036397/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos1016o2c k) + cos1016o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_117
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 118 - ((-228883/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_119 : ((94149903/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos1016o2c k) + cos1016o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_118
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 119 - ((-7921891/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_120 : ((25784967/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos1016o2c k) + cos1016o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_119
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 120 - ((1798193/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_121 : ((10270397/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos1016o2c k) + cos1016o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_120
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 121 - ((-217449/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_122 : ((94309951/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos1016o2c k) + cos1016o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_121
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 122 - ((-8393019/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_123 : ((82717/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos1016o2c k) + cos1016o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_122
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 123 - ((9087299/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_124 : ((12714843/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos1016o2c k) + cos1016o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_123
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 124 - ((-838253/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_125 : ((94754103/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos1016o2c k) + cos1016o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_124
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 125 - ((-6963641/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_126 : ((104697213/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos1016o2c k) + cos1016o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_125
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 126 - ((994411/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_127 : ((99125769/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos1016o2c k) + cos1016o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_126
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 127 - ((-1392611/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_128 : ((96632031/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos1016o2c k) + cos1016o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_127
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 128 - ((-1246369/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_129 : ((105372591/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos1016o2c k) + cos1016o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_128
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 129 - ((218539/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_130 : ((95744851/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos1016o2c k) + cos1016o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_129
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 130 - ((-481337/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_131 : ((20186553/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos1016o2c k) + cos1016o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_130
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 131 - ((2594457/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_132 : ((513413/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos1016o2c k) + cos1016o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_131
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 132 - ((350167/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_133 : ((23762199/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos1016o2c k) + cos1016o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_132
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 133 - ((-1908201/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_134 : ((26260071/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos1016o2c k) + cos1016o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_133
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 134 - ((1249061/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_135 : ((9676677/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos1016o2c k) + cos1016o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_134
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 135 - ((-4136257/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_136 : ((100351133/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos1016o2c k) + cos1016o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_135
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 136 - ((3585363/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_137 : ((102467647/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos1016o2c k) + cos1016o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_136
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 137 - ((1058757/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_138 : ((11941483/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos1016o2c k) + cos1016o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_137
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 138 - ((-6934783/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_139 : ((105146457/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos1016o2c k) + cos1016o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_138
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 139 - ((9615593/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_140 : ((47695251/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos1016o2c k) + cos1016o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_139
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 140 - ((-1950991/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_141 : ((20612879/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos1016o2c k) + cos1016o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_140
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 141 - ((7674893/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_142 : ((49463853/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos1016o2c k) + cos1016o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_141
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 142 - ((-4135689/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_143 : ((98956929/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos1016o2c k) + cos1016o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_142
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 143 - ((30223/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_144 : ((20561603/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos1016o2c k) + cos1016o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_143
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 144 - ((1926043/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_145 : ((3833983/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos1016o2c k) + cos1016o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_144
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 145 - ((-10871/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_146 : ((104846509/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos1016o2c k) + cos1016o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_145
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 146 - ((4498967/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_147 : ((47462101/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos1016o2c k) + cos1016o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_146
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 147 - ((-9921307/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_148 : ((52383519/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos1016o2c k) + cos1016o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_147
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 148 - ((2460959/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_149 : ((957891/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos1016o2c k) + cos1016o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_148
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 149 - ((-4488469/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_150 : ((103354369/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos1016o2c k) + cos1016o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_149
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 150 - ((7566269/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_151 : ((97508281/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos1016o2c k) + cos1016o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_150
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 151 - ((-182659/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_152 : ((101518229/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos1016o2c k) + cos1016o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_151
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 152 - ((1002737/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_153 : ((99304251/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos1016o2c k) + cos1016o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_152
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 153 - ((-1106489/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_154 : ((99855671/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos1016o2c k) + cos1016o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_153
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 154 - ((27621/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_155 : ((100765081/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos1016o2c k) + cos1016o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_154
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 155 - ((91041/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_156 : ((9861623/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos1016o2c k) + cos1016o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_155
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 156 - ((-2147851/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_157 : ((50884707/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos1016o2c k) + cos1016o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_156
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 157 - ((394273/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_158 : ((48915499/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos1016o2c k) + cos1016o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_157
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 158 - ((-492177/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_159 : ((102342621/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos1016o2c k) + cos1016o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_158
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 159 - ((4512623/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_160 : ((97446383/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos1016o2c k) + cos1016o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_159
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 160 - ((-2447619/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_161 : ((5127209/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos1016o2c k) + cos1016o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_160
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 161 - ((5098797/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_162 : ((97410501/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos1016o2c k) + cos1016o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_161
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 162 - ((-5132679/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_163 : ((10240931/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos1016o2c k) + cos1016o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_162
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 163 - ((4999809/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_164 : ((24427689/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos1016o2c k) + cos1016o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_163
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 164 - ((-2348777/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_165 : ((815431/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos1016o2c k) + cos1016o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_164
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 165 - ((4219119/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_166 : ((98372877/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos1016o2c k) + cos1016o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_165
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 166 - ((-1777499/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_167 : ((101067659/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos1016o2c k) + cos1016o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_166
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 167 - ((1347891/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_168 : ((99432293/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos1016o2c k) + cos1016o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_167
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 168 - ((-817183/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_169 : ((49902897/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos1016o2c k) + cos1016o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_168
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 169 - ((374501/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_170 : ((100873611/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos1016o2c k) + cos1016o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_169
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 170 - ((1068817/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_171 : ((9821293/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos1016o2c k) + cos1016o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_170
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 171 - ((-2659681/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_172 : ((25637477/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos1016o2c k) + cos1016o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_171
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 172 - ((2168989/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_173 : ((96533973/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos1016o2c k) + cos1016o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_172
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 173 - ((-1202987/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_174 : ((52052443/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos1016o2c k) + cos1016o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_173
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 174 - ((7571913/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_175 : ((23810099/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos1016o2c k) + cos1016o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_174
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 175 - ((-886349/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_176 : ((52482981/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos1016o2c k) + cos1016o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_175
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 176 - ((4863283/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_177 : ((2374229/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos1016o2c k) + cos1016o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_176
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 177 - ((-4997901/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_178 : ((26123939/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos1016o2c k) + cos1016o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_177
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 178 - ((2381899/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_179 : ((96265327/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos1016o2c k) + cos1016o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_178
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 179 - ((-8229429/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_180 : ((102356293/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos1016o2c k) + cos1016o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_179
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 180 - ((3045983/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_181 : ((99134963/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos1016o2c k) + cos1016o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_180
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 181 - ((-322033/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_182 : ((98985571/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos1016o2c k) + cos1016o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_181
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 182 - ((-18549/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_183 : ((102627249/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos1016o2c k) + cos1016o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_182
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 183 - ((1821339/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_184 : ((95838873/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos1016o2c k) + cos1016o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_183
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 184 - ((-424211/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_185 : ((104899937/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos1016o2c k) + cos1016o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_184
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 185 - ((566379/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_186 : ((1898091/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos1016o2c k) + cos1016o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_185
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 186 - ((-9994387/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_187 : ((104174571/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos1016o2c k) + cos1016o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_186
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 187 - ((9271021/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_188 : ((9732557/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos1016o2c k) + cos1016o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_187
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 188 - ((-6848001/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_189 : ((100353507/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos1016o2c k) + cos1016o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_188
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 189 - ((3028937/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_190 : ((101878019/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos1016o2c k) + cos1016o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_189
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 190 - ((190689/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_191 : ((48000683/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos1016o2c k) + cos1016o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_190
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 191 - ((-5875653/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_192 : ((104987883/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos1016o2c k) + cos1016o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_191
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 192 - ((8987517/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_193 : ((23749691/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos1016o2c k) + cos1016o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_192
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 193 - ((-9988119/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_194 : ((103443647/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos1016o2c k) + cos1016o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_193
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 194 - ((8445883/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_195 : ((24715017/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos1016o2c k) + cos1016o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_194
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 195 - ((-4582579/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_196 : ((19637739/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos1016o2c k) + cos1016o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_195
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 196 - ((-670373/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_197 : ((104025827/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos1016o2c k) + cos1016o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_196
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 197 - ((1459533/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_198 : ((94730569/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos1016o2c k) + cos1016o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_197
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 198 - ((-4647129/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_199 : ((52260651/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos1016o2c k) + cos1016o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_198
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 199 - ((9791733/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_200 : ((48775507/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos1016o2c k) + cos1016o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_199
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 200 - ((-871161/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_201 : ((99174919/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos1016o2c k) + cos1016o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_200
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 201 - ((324981/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_202 : ((12948679/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos1016o2c k) + cos1016o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_201
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 202 - ((4415513/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_203 : ((47360473/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos1016o2c k) + cos1016o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_202
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 203 - ((-4433743/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_204 : ((3268267/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos1016o2c k) + cos1016o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_203
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 204 - ((4932299/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_205 : ((97777581/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos1016o2c k) + cos1016o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_204
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 205 - ((-6805963/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_206 : ((9856589/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos1016o2c k) + cos1016o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_205
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 206 - ((789309/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_207 : ((416929/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos1016o2c k) + cos1016o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_206
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 207 - ((35421/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_208 : ((94606643/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos1016o2c k) + cos1016o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_207
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 208 - ((-9624607/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_209 : ((103694243/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos1016o2c k) + cos1016o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_208
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 209 - ((45443/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_210 : ((19916219/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos1016o2c k) + cos1016o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_209
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 210 - ((-1028037/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_211 : ((96581919/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos1016o2c k) + cos1016o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_210
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 211 - ((-93693/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_212 : ((26306561/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos1016o2c k) + cos1016o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_211
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 212 - ((345813/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_213 : ((95476007/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos1016o2c k) + cos1016o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_212
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 213 - ((-9749237/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_214 : ((100990383/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos1016o2c k) + cos1016o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_213
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 214 - ((344711/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_215 : ((102869037/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos1016o2c k) + cos1016o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_214
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 215 - ((939827/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_216 : ((47300117/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos1016o2c k) + cos1016o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_215
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 216 - ((-8267803/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_217 : ((6525271/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos1016o2c k) + cos1016o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_216
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 217 - ((4902551/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_218 : ((49515809/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos1016o2c k) + cos1016o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_217
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 218 - ((-2685859/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_219 : ((12070119/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos1016o2c k) + cos1016o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_218
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 219 - ((-1234833/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_220 : ((52682189/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos1016o2c k) + cos1016o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_219
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 220 - ((4402213/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_221 : ((95948267/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos1016o2c k) + cos1016o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_220
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 221 - ((-9415111/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_222 : ((19929271/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos1016o2c k) + cos1016o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_221
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 222 - ((231193/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_223 : ((104258947/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos1016o2c k) + cos1016o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_222
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 223 - ((576699/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_224 : ((94504727/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos1016o2c k) + cos1016o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_223
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 224 - ((-487661/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_225 : ((102427281/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos1016o2c k) + cos1016o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_224
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 225 - ((3961777/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_226 : ((102168119/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos1016o2c k) + cos1016o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_225
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 226 - ((-129081/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_227 : ((94504981/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos1016o2c k) + cos1016o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_226
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 227 - ((-3831069/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_228 : ((6517669/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos1016o2c k) + cos1016o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_227
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 228 - ((9778723/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_229 : ((100007339/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos1016o2c k) + cos1016o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_228
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 229 - ((-854873/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_230 : ((47665809/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos1016o2c k) + cos1016o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_229
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 230 - ((-4674721/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_231 : ((105223233/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos1016o2c k) + cos1016o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_230
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 231 - ((1978523/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_232 : ((98259141/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos1016o2c k) + cos1016o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_231
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 232 - ((-1740773/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_233 : ((96404999/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos1016o2c k) + cos1016o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_232
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 233 - ((-926571/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_234 : ((21108261/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos1016o2c k) + cos1016o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_233
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 234 - ((4568653/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_235 : ((97051083/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos1016o2c k) + cos1016o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_234
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 235 - ((-4244611/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_236 : ((12168093/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos1016o2c k) + cos1016o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_235
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 236 - ((294661/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_237 : ((105559367/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos1016o2c k) + cos1016o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_236
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 237 - ((8215623/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_238 : ((48166143/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos1016o2c k) + cos1016o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_237
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 238 - ((-9226081/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_239 : ((97955939/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos1016o2c k) + cos1016o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_238
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 239 - ((1624653/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_240 : ((52757863/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos1016o2c k) + cos1016o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_239
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 240 - ((7560787/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_241 : ((96009347/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos1016o2c k) + cos1016o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_240
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 241 - ((-9505379/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_242 : ((1963207/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos1016o2c k) + cos1016o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_241
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 242 - ((2152003/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_243 : ((105537693/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos1016o2c k) + cos1016o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_242
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 243 - ((7378343/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_244 : ((48013433/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos1016o2c k) + cos1016o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_243
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 244 - ((-9509827/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_245 : ((48969501/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos1016o2c k) + cos1016o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_244
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 245 - ((119571/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_246 : ((105644311/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos1016o2c k) + cos1016o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_245
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 246 - ((7706309/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_247 : ((24098339/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos1016o2c k) + cos1016o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_246
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 247 - ((-1849991/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_248 : ((24327651/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos1016o2c k) + cos1016o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_247
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 248 - ((114781/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_249 : ((105753343/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos1016o2c k) + cos1016o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_248
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 249 - ((8443739/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_250 : ((24293913/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos1016o2c k) + cos1016o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_249
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 250 - ((-8576691/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_251 : ((96346229/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 251, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 251, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 250, cos1016o2c k) + cos1016o2c 251 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 250) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_250
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 251 - ((-828423/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_251).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_252 : ((21136489/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 252, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 252, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 251, cos1016o2c k) + cos1016o2c 252 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 251) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_251
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 252 - ((72947/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_252).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_253 : ((3938313/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 253, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 253, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 252, cos1016o2c k) + cos1016o2c 253 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 252) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_252
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 253 - ((-361181/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_253).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_254 : ((238031/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 254, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 254, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 253, cos1016o2c k) + cos1016o2c 254 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 253) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_253
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 254 - ((-129777/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_254).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_255 : ((26291609/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 255, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 255, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 254, cos1016o2c k) + cos1016o2c 255 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 254) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_254
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 255 - ((2488759/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_255).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_256 : ((12532917/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 256, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 256, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 255, cos1016o2c k) + cos1016o2c 256 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 255) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_255
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 256 - ((-49021/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_256).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_257 : ((94220243/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 257, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 257, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 256, cos1016o2c k) + cos1016o2c 257 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 256) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_256
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 257 - ((-6042093/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_257).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_258 : ((103916353/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 258, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 258, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 257, cos1016o2c k) + cos1016o2c 258 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 257) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_257
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 258 - ((969711/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_258).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_259 : ((10244421/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 259, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 259, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 258, cos1016o2c k) + cos1016o2c 259 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 258) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_258
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 259 - ((-1471143/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_259).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_260 : ((93837887/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 260, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 260, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 259, cos1016o2c k) + cos1016o2c 260 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 259) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_259
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 260 - ((-8605323/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_260).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_261 : ((101755169/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 261, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 261, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 260, cos1016o2c k) + cos1016o2c 261 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 260) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_260
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 261 - ((3959141/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_261).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_262 : ((104567213/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 262, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 262, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 261, cos1016o2c k) + cos1016o2c 262 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 261) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_261
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 262 - ((703261/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_262).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_263 : ((4729881/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 263, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 263, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 262, cos1016o2c k) + cos1016o2c 263 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 262) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_262
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 263 - ((-9968593/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_263).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_264 : ((19764667/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 264, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 264, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 263, cos1016o2c k) + cos1016o2c 264 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 263) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_263
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 264 - ((845343/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_264).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_265 : ((105887799/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 265, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 265, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 264, cos1016o2c k) + cos1016o2c 265 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 264) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_264
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 265 - ((883183/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_265).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_266 : ((48423953/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 266, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 266, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 265, cos1016o2c k) + cos1016o2c 266 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 265) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_265
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 266 - ((-9038893/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_266).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_267 : ((95782443/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 267, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 267, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 266, cos1016o2c k) + cos1016o2c 267 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 266) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_266
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 267 - ((-1064463/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_267).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_268 : ((105536887/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 268, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 268, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 267, cos1016o2c k) + cos1016o2c 268 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 267) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_267
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 268 - ((2438861/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_268).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_269 : ((2509261/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 269, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 269, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 268, cos1016o2c k) + cos1016o2c 269 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 268) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_268
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 269 - ((-5165447/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_269).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_270 : ((93822353/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 270, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 270, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 269, cos1016o2c k) + cos1016o2c 270 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 269) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_269
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 270 - ((-6547087/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_270).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_271 : ((51503093/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 271, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 271, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 270, cos1016o2c k) + cos1016o2c 271 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 270) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_270
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 271 - ((9184833/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_271).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_272 : ((813017/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 272, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 272, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 271, cos1016o2c k) + cos1016o2c 272 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 271) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_271
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 272 - ((106099/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_272).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_273 : ((94239721/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 273, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 273, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 272, cos1016o2c k) + cos1016o2c 273 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 272) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_272
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 273 - ((-1965091/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_273).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_274 : ((49400569/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 274, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 274, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 273, cos1016o2c k) + cos1016o2c 274 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 273) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_273
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 274 - ((4562417/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_274).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_275 : ((106092687/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 275, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 275, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 274, cos1016o2c k) + cos1016o2c 275 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 274) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_274
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 275 - ((7292549/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_275).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_276 : ((48767851/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 276, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 276, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 275, cos1016o2c k) + cos1016o2c 276 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 275) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_275
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 276 - ((-1711197/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_276).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_277 : ((9479419/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 277, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 277, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 276, cos1016o2c k) + cos1016o2c 277 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 276) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_276
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 277 - ((-85641/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_277).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_278 : ((104791611/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 278, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 278, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 277, cos1016o2c k) + cos1016o2c 278 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 277) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_277
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 278 - ((9998421/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_278).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_279 : ((800451/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 279, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 279, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 278, cos1016o2c k) + cos1016o2c 279 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 278) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_278
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 279 - ((-2332883/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_279).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_280 : ((93597121/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 280, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 280, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 279, cos1016o2c k) + cos1016o2c 280 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 279) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_279
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 280 - ((-8859607/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_280).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_281 : ((100208431/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 281, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 281, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 280, cos1016o2c k) + cos1016o2c 281 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 280) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_280
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 281 - ((661231/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_281).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_282 : ((52986527/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 282, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 282, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 281, cos1016o2c k) + cos1016o2c 282 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 281) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_281
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 282 - ((5765623/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_282).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_283 : ((1934239/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 283, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 283, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 282, cos1016o2c k) + cos1016o2c 283 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 282) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_282
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 283 - ((-1157513/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_283).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_284 : ((47529429/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 284, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 284, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 283, cos1016o2c k) + cos1016o2c 284 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 283) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_283
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 284 - ((-413023/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_284).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_285 : ((1641343/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 285, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 285, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 284, cos1016o2c k) + cos1016o2c 285 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 284) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_284
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 285 - ((4994047/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_285).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_286 : ((102499493/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 286, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 286, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 285, cos1016o2c k) + cos1016o2c 286 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 285) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_285
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 286 - ((-2545459/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_286).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_287 : ((93536659/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 287, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 287, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 286, cos1016o2c k) + cos1016o2c 287 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 286) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_286
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 287 - ((-4480917/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_287).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_288 : ((19926773/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 288, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 288, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 287, cos1016o2c k) + cos1016o2c 288 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 287) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_287
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 288 - ((3049103/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_288).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_289 : ((106263687/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 289, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 289, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 288, cos1016o2c k) + cos1016o2c 289 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 288) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_288
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 289 - ((3315411/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_289).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_290 : ((97690441/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 290, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 290, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 289, cos1016o2c k) + cos1016o2c 290 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 289) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_289
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 290 - ((-4286123/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_290).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_291 : ((94138183/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 291, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 291, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 290, cos1016o2c k) + cos1016o2c 291 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 290) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_290
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 291 - ((-1775629/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_291).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_292 : ((51977571/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 292, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 292, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 291, cos1016o2c k) + cos1016o2c 292 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 291) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_291
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 292 - ((9817959/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_292).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_293 : ((104205577/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 293, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 293, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 292, cos1016o2c k) + cos1016o2c 293 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 292) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_292
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 293 - ((50287/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_293).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_294 : ((94295381/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 294, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 294, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 293, cos1016o2c k) + cos1016o2c 294 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 293) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_293
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 294 - ((-2477299/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_294).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_295 : ((48572317/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 295, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 295, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 294, cos1016o2c k) + cos1016o2c 295 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 294) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_294
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 295 - ((2850253/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_295).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_296 : ((106202367/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 296, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 296, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 295, cos1016o2c k) + cos1016o2c 296 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 295) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_295
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 296 - ((9058733/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_296).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_297 : ((10072201/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 297, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 297, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 296, cos1016o2c k) + cos1016o2c 297 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 296) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_296
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 297 - ((-5479357/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_297).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_298 : ((93180831/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 298, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 298, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 297, cos1016o2c k) + cos1016o2c 298 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 297) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_297
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 298 - ((-7540179/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_298).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_299 : ((10067739/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 299, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 299, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 298, cos1016o2c k) + cos1016o2c 299 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 298) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_298
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 299 - ((7497559/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_299).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_300 : ((53152067/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 300, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 300, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 299, cos1016o2c k) + cos1016o2c 300 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 299) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_299
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 300 - ((175867/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_300).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_301 : ((97424023/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 301, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 301, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 300, cos1016o2c k) + cos1016o2c 301 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 300) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_300
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 301 - ((-8879111/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_301).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_302 : ((93864049/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 302, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 302, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 301, cos1016o2c k) + cos1016o2c 302 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 301) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_301
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 302 - ((-1779487/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_302).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_303 : ((6471179/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 303, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 303, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 302, cos1016o2c k) + cos1016o2c 303 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 302) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_302
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 303 - ((1935163/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_303).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_304 : ((52527547/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 304, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 304, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 303, cos1016o2c k) + cos1016o2c 304 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 303) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_303
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 304 - ((151723/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_304).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_305 : ((760553/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 305, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 305, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 304, cos1016o2c k) + cos1016o2c 305 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 304) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_304
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 305 - ((-9984969/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_305).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_306 : ((5965037/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 306, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 306, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 305, cos1016o2c k) + cos1016o2c 306 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 305) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_305
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 306 - ((372467/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_306).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_307 : ((13170373/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 307, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 307, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 306, cos1016o2c k) + cos1016o2c 307 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 306) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_306
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 307 - ((155053/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_307).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_308 : ((20665107/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 308, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 308, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 307, cos1016o2c k) + cos1016o2c 308 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 307) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_307
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 308 - ((-2036449/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_308).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_309 : ((23429163/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 309, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 309, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 308, cos1016o2c k) + cos1016o2c 309 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 308) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_308
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 309 - ((-9607883/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_309).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_310 : ((777271/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 310, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 310, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 309, cos1016o2c k) + cos1016o2c 310 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 309) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_309
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 310 - ((3443223/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_310).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_311 : ((5315081/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 311, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 311, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 310, cos1016o2c k) + cos1016o2c 311 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 310) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_310
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 311 - ((1828749/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_311).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_312 : ((50855523/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 312, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 312, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 311, cos1016o2c k) + cos1016o2c 312 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 311) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_311
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 312 - ((-2294787/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_312).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_313 : ((46545101/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 313, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 313, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 312, cos1016o2c k) + cos1016o2c 313 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 312) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_312
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 313 - ((-2154961/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_313).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_314 : ((98579869/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 314, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 314, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 313, cos1016o2c k) + cos1016o2c 314 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 313) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_313
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 314 - ((5490667/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_314).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_315 : ((53342089/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 315, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 315, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 314, cos1016o2c k) + cos1016o2c 315 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 314) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_314
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 315 - ((8105309/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_315).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_316 : ((100511809/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 316, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 316, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 315, cos1016o2c k) + cos1016o2c 316 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 315) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_315
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 316 - ((-6171369/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_316).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_317 : ((92858063/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 317, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 317, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 316, cos1016o2c k) + cos1016o2c 317 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 316) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_316
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 317 - ((-3826373/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_317).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_318 : ((9951479/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 318, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 318, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 317, cos1016o2c k) + cos1016o2c 318 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 317) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_317
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 318 - ((6657727/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_318).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_319 : ((106811899/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 319, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 319, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 318, cos1016o2c k) + cos1016o2c 319 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 318) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_318
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 319 - ((7298109/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_319).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_320 : ((1559937/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 320, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 320, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 319, cos1016o2c k) + cos1016o2c 320 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 319) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_319
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 320 - ((-6974931/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_320).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_321 : ((46384639/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 321, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 321, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 320, cos1016o2c k) + cos1016o2c 321 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 320) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_320
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 321 - ((-706569/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_321).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_322 : ((6244377/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 322, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 322, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 321, cos1016o2c k) + cos1016o2c 322 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 321) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_321
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 322 - ((3570877/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_322).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_323 : ((106877137/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 323, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 323, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 322, cos1016o2c k) + cos1016o2c 323 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 322) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_322
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 323 - ((1393621/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_323).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_324 : ((99706837/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 324, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 324, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 323, cos1016o2c k) + cos1016o2c 324 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 323) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_323
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 324 - ((-71693/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_324).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_325 : ((5793511/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 325, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 325, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 324, cos1016o2c k) + cos1016o2c 325 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 324) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_324
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 325 - ((-7009661/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_325).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_326 : ((99755829/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 326, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 326, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 325, cos1016o2c k) + cos1016o2c 326 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 325) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_325
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 326 - ((7060653/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_326).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_327 : ((26735167/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 327, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 327, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 326, cos1016o2c k) + cos1016o2c 327 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 326) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_326
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 327 - ((7185839/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_327).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_328 : ((6257973/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 328, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 328, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 327, cos1016o2c k) + cos1016o2c 328 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 327) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_327
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 328 - ((-68121/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_328).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_329 : ((9264171/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 329, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 329, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 328, cos1016o2c k) + cos1016o2c 329 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 328) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_328
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 329 - ((-3742429/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_329).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_330 : ((24762971/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 330, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 330, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 329, cos1016o2c k) + cos1016o2c 330 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 329) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_329
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 330 - ((3205587/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_330).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_331 : ((5346861/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 331, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 331, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 330, cos1016o2c k) + cos1016o2c 331 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 330) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_330
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 331 - ((61612/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_331).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_332 : ((12636823/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 332, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 332, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 331, cos1016o2c k) + cos1016o2c 332 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 331) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_331
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 332 - ((-1460409/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_332).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_333 : ((92733689/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 333, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 333, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 332, cos1016o2c k) + cos1016o2c 333 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 332) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_332
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 333 - ((-1671979/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_333).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_334 : ((97816507/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 334, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 334, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 333, cos1016o2c k) + cos1016o2c 334 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 333) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_333
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 334 - ((2541909/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_334).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_335 : ((106679793/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 335, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 335, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 334, cos1016o2c k) + cos1016o2c 335 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 334) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_334
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 335 - ((4432143/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_335).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_336 : ((102559471/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 336, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 336, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 335, cos1016o2c k) + cos1016o2c 336 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 335) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_335
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 336 - ((-2059661/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_336).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_337 : ((93211717/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 337, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 337, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 336, cos1016o2c k) + cos1016o2c 337 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 336) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_336
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 337 - ((-4673377/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_337).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_338 : ((3845799/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 338, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 338, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 337, cos1016o2c k) + cos1016o2c 338 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 337) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_337
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 338 - ((1467129/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_338).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_339 : ((105885639/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 339, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 339, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 338, cos1016o2c k) + cos1016o2c 339 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 338) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_338
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 339 - ((304427/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_339).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_340 : ((13044687/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 340, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 340, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 339, cos1016o2c k) + cos1016o2c 340 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 339) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_339
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 340 - ((-1527143/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_340).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_341 : ((94384169/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 341, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 341, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 340, cos1016o2c k) + cos1016o2c 341 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 340) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_340
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 341 - ((-9972327/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_341).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_342 : ((94295093/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 342, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 342, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 341, cos1016o2c k) + cos1016o2c 342 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 341) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_341
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 342 - ((-22019/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_342).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_343 : ((26061917/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 343, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 343, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 342, cos1016o2c k) + cos1016o2c 343 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 342) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_342
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 343 - ((398143/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_343).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_344 : ((106118591/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 344, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 344, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 343, cos1016o2c k) + cos1016o2c 344 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 343) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_343
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 344 - ((1871923/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_344).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_345 : ((19303901/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 345, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 345, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 344, cos1016o2c k) + cos1016o2c 345 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 344) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_344
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 345 - ((-4799043/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_345).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_346 : ((92763201/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 346, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 346, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 345, cos1016o2c k) + cos1016o2c 346 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 345) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_345
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 346 - ((-469413/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_346).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_347 : ((12698381/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 347, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 347, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 346, cos1016o2c k) + cos1016o2c 347 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 346) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_346
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 347 - ((8824847/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_347).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_348 : ((107220929/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 348, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 348, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 347, cos1016o2c k) + cos1016o2c 348 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 347) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_347
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 348 - ((5634881/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_348).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_349 : ((12455919/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 349, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 349, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 348, cos1016o2c k) + cos1016o2c 349 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 348) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_348
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 349 - ((-7572577/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_349).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_350 : ((92273797/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 350, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 350, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 349, cos1016o2c k) + cos1016o2c 350 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 349) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_349
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 350 - ((-1474511/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_350).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_351 : ((49043103/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 351, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 351, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 350, cos1016o2c k) + cos1016o2c 351 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 350) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_350
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 351 - ((5813409/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_351).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_352 : ((106885897/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 352, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 352, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 351, cos1016o2c k) + cos1016o2c 352 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 351) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_351
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 352 - ((8800691/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_352).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_353 : ((2582853/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 353, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 353, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 352, cos1016o2c k) + cos1016o2c 353 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 352) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_352
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 353 - ((-3570777/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_353).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_354 : ((23394927/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 354, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 354, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 353, cos1016o2c k) + cos1016o2c 354 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 353) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_353
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 354 - ((-2433353/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_354).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_355 : ((47256633/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 355, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 355, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 354, cos1016o2c k) + cos1016o2c 355 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 354) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_354
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 355 - ((467279/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_355).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_356 : ((26125163/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 356, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 356, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 355, cos1016o2c k) + cos1016o2c 356 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 355) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_355
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 356 - ((4994193/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_356).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_357 : ((53214029/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 357, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 357, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 356, cos1016o2c k) + cos1016o2c 357 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 356) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_356
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 357 - ((964203/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_357).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_358 : ((19402501/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 358, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 358, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 357, cos1016o2c k) + cos1016o2c 358 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 357) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_357
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 358 - ((-9414553/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_358).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_359 : ((92237833/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 359, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 359, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 358, cos1016o2c k) + cos1016o2c 359 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 358) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_358
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 359 - ((-596709/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_359).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_360 : ((100165187/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 360, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 360, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 359, cos1016o2c k) + cos1016o2c 360 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 359) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_359
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 360 - ((3964177/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_360).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_361 : ((107455173/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 361, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 361, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 360, cos1016o2c k) + cos1016o2c 361 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 360) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_360
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 361 - ((3645493/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_361).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_362 : ((101904893/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 362, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 362, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 361, cos1016o2c k) + cos1016o2c 362 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 361) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_361
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 362 - ((-34683/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_362).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_363 : ((23192079/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 363, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 363, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 362, cos1016o2c k) + cos1016o2c 363 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 362) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_362
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 363 - ((-9135577/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_363).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_364 : ((47599159/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 364, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 364, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 363, cos1016o2c k) + cos1016o2c 364 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 363) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_363
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 364 - ((1215501/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_364).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_365 : ((26293473/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 365, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 365, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 364, cos1016o2c k) + cos1016o2c 365 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 364) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_364
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 365 - ((4988287/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_365).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_366 : ((13286873/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 366, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 366, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 365, cos1016o2c k) + cos1016o2c 366 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 365) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_365
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 366 - ((280523/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_366).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_367 : ((48366139/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 367, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 367, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 366, cos1016o2c k) + cos1016o2c 367 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 366) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_366
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 367 - ((-4780853/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_367).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_368 : ((92063517/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 368, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 368, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 367, cos1016o2c k) + cos1016o2c 368 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 367) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_367
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 368 - ((-4667761/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_368).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_369 : ((49925783/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 369, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 369, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 368, cos1016o2c k) + cos1016o2c 369 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 368) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_368
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 369 - ((7789049/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_369).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_370 : ((13439807/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 370, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 370, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 369, cos1016o2c k) + cos1016o2c 370 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 369) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_369
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 370 - ((766789/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_370).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_371 : ((12843399/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 371, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 371, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 370, cos1016o2c k) + cos1016o2c 371 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 370) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_370
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 371 - ((-596283/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_371).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_372 : ((93174997/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 372, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 372, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 371, cos1016o2c k) + cos1016o2c 372 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 371) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_371
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 372 - ((-1914239/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_372).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_373 : ((23510443/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 373, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 373, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 372, cos1016o2c k) + cos1016o2c 373 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 372) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_372
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 373 - ((34711/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_373).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_374 : ((103964187/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 374, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 374, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 373, cos1016o2c k) + cos1016o2c 374 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 373) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_373
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 374 - ((1984683/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_374).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_375 : ((13410047/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 375, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 375, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 374, cos1016o2c k) + cos1016o2c 375 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 374) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_374
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 375 - ((3317189/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_375).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_376 : ((98785997/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 376, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 376, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 375, cos1016o2c k) + cos1016o2c 376 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 375) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_375
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 376 - ((-8493379/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_376).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_377 : ((91769179/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 377, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 377, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 376, cos1016o2c k) + cos1016o2c 377 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 376) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_376
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 377 - ((-3507909/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_377).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_378 : ((971483/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 378, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 378, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 377, cos1016o2c k) + cos1016o2c 378 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 377) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_377
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 378 - ((5380121/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_378).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_379 : ((106576621/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 379, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 379, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 378, cos1016o2c k) + cos1016o2c 379 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 378) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_378
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 379 - ((9429321/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_379).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_380 : ((26376291/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 380, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 380, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 379, cos1016o2c k) + cos1016o2c 380 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 379) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_379
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 380 - ((-1070457/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_380).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_381 : ((47793287/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 381, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 381, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 380, cos1016o2c k) + cos1016o2c 381 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 380) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_380
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 381 - ((-991759/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_381).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_382 : ((45995687/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 382, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 382, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 381, cos1016o2c k) + cos1016o2c 382 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 381) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_381
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 382 - ((-17971/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_382).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_383 : ((100184687/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 383, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 383, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 382, cos1016o2c k) + cos1016o2c 383 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 382) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_382
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 383 - ((8194313/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_383).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_384 : ((107739321/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 384, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 384, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 383, cos1016o2c k) + cos1016o2c 384 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 383) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_383
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 384 - ((3777817/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_384).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_385 : ((2581421/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 385, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 385, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 384, cos1016o2c k) + cos1016o2c 385 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 384) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_384
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 385 - ((-4481481/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_385).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_386 : ((4673949/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 386, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 386, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 385, cos1016o2c k) + cos1016o2c 386 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 385) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_385
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 386 - ((-488843/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_386).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_387 : ((46515067/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 387, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 387, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 386, cos1016o2c k) + cos1016o2c 387 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 386) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_386
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 387 - ((-223923/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_387).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_388 : ((102568803/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 388, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 388, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 387, cos1016o2c k) + cos1016o2c 388 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 387) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_387
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 388 - ((9539669/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_388).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_389 : ((107945627/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 389, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 389, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 388, cos1016o2c k) + cos1016o2c 389 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 388) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_388
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 389 - ((168057/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_389).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_390 : ((2530703/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 390, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 390, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 389, cos1016o2c k) + cos1016o2c 390 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 389) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_389
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 390 - ((-6716507/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_390).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_391 : ((11536969/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 391, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 391, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 390, cos1016o2c k) + cos1016o2c 391 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 390) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_390
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 391 - ((-1116421/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_391).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_392 : ((47107931/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 392, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 392, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 391, cos1016o2c k) + cos1016o2c 392 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 391) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_391
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 392 - ((192111/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_392).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_393 : ((10418027/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 393, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 393, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 392, cos1016o2c k) + cos1016o2c 393 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 392) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_392
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 393 - ((311419/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_393).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_394 : ((107730233/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 394, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 394, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 393, cos1016o2c k) + cos1016o2c 394 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 393) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_393
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 394 - ((3550963/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_394).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_395 : ((12468133/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 395, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 395, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 394, cos1016o2c k) + cos1016o2c 395 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 394) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_394
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 395 - ((-7984169/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_395).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_396 : ((45856611/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 396, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 396, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 395, cos1016o2c k) + cos1016o2c 396 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 395) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_395
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 396 - ((-4015421/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_396).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_397 : ((47564599/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 397, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 397, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 396, cos1016o2c k) + cos1016o2c 397 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 396) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_396
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 397 - ((213561/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_397).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_398 : ((105112549/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 398, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 398, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 397, cos1016o2c k) + cos1016o2c 398 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 397) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_397
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 398 - ((9984351/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_398).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_399 : ((2687231/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 399, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 399, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 398, cos1016o2c k) + cos1016o2c 399 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 398) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_398
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 399 - ((2377691/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_399).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_400 : ((19781501/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 400, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 400, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 399, cos1016o2c k) + cos1016o2c 400 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 399) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_399
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 400 - ((-1716147/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_400).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_401 : ((91448997/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 401, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 401, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 400, cos1016o2c k) + cos1016o2c 401 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 400) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_400
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 401 - ((-1864377/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_401).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_402 : ((23889529/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 402, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 402, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 401, cos1016o2c k) + cos1016o2c 402 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 401) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_401
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 402 - ((4110119/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_402).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_403 : ((52745593/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 403, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 403, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 402, cos1016o2c k) + cos1016o2c 403 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 402) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_402
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 403 - ((993407/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_403).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_404 : ((26861687/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 404, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 404, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 403, cos1016o2c k) + cos1016o2c 404 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 403) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_403
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 404 - ((978281/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_404).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_405 : ((49363663/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 405, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 405, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 404, cos1016o2c k) + cos1016o2c 405 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 404) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_404
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 405 - ((-4359211/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_405).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_406 : ((91347939/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 406, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 406, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 405, cos1016o2c k) + cos1016o2c 406 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 405) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_405
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 406 - ((-7378387/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_406).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_407 : ((763383/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 407, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 407, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 406, cos1016o2c k) + cos1016o2c 407 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 406) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_406
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 407 - ((127373/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_407).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_408 : ((52688081/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 408, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 408, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 407, cos1016o2c k) + cos1016o2c 408 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 407) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_407
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 408 - ((9954287/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_408).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_409 : ((53835059/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 409, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 409, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 408, cos1016o2c k) + cos1016o2c 409 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 408) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_408
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 409 - ((573739/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_409).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_410 : ((99206247/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 410, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 410, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 409, cos1016o2c k) + cos1016o2c 410 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 409) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_409
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 410 - ((-8462871/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_410).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_411 : ((91402673/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 411, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 411, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 410, cos1016o2c k) + cos1016o2c 411 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 410) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_410
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 411 - ((-3901287/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_411).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_412 : ((47365507/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 412, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 412, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 411, cos1016o2c k) + cos1016o2c 412 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 411) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_411
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 412 - ((3329341/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_412).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_413 : ((52365007/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 413, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 413, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 412, cos1016o2c k) + cos1016o2c 413 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 412) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_412
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 413 - ((1 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_413).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_414 : ((27021009/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 414, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 414, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 413, cos1016o2c k) + cos1016o2c 414 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 413) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_413
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 414 - ((1677511/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_414).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_415 : ((3136051/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 415, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 415, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 414, cos1016o2c k) + cos1016o2c 415 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 414) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_414
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 415 - ((-1932351/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_415).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_416 : ((91751321/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 416, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 416, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 415, cos1016o2c k) + cos1016o2c 416 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 415) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_415
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 416 - ((-8601311/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_416).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_417 : ((93581739/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 417, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 417, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 416, cos1016o2c k) + cos1016o2c 417 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 416) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_416
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 417 - ((915709/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_417).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_418 : ((20687367/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 418, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 418, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 417, cos1016o2c k) + cos1016o2c 418 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 417) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_417
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 418 - ((308003/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_418).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_419 : ((108463391/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 419, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 419, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 418, cos1016o2c k) + cos1016o2c 419 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 418) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_418
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 419 - ((1256889/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_419).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_420 : ((102141961/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 420, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 420, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 419, cos1016o2c k) + cos1016o2c 420 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 419) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_419
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 420 - ((-632043/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_420).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_421 : ((46326613/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 421, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 421, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 420, cos1016o2c k) + cos1016o2c 421 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 420) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_420
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 421 - ((-1897547/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_421).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_422 : ((46105679/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 422, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 422, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 421, cos1016o2c k) + cos1016o2c 422 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 421) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_421
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 422 - ((-110217/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_422).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_423 : ((2534283/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 423, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 423, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 422, cos1016o2c k) + cos1016o2c 423 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 422) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_422
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 423 - ((4580481/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_423).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_424 : ((27107553/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 424, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 424, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 423, cos1016o2c k) + cos1016o2c 424 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 423) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_423
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 424 - ((1764973/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_424).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_425 : ((104416753/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 425, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 425, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 424, cos1016o2c k) + cos1016o2c 425 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 424) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_424
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 425 - ((-4012459/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_425).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_426 : ((47211113/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 426, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 426, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 425, cos1016o2c k) + cos1016o2c 426 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 425) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_425
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 426 - ((-9993527/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_426).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_427 : ((11381429/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 427, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 427, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 426, cos1016o2c k) + cos1016o2c 427 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 426) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_426
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 427 - ((-1684897/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_427).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_428 : ((19705439/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 428, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 428, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 427, cos1016o2c k) + cos1016o2c 428 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 427) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_427
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 428 - ((7476763/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_428).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_429 : ((26872423/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 429, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 429, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 428, cos1016o2c k) + cos1016o2c 429 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 428) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_428
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 429 - ((8963497/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_429).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_430 : ((21355239/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 430, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 430, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 429, cos1016o2c k) + cos1016o2c 430 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 429) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_429
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 430 - ((-712497/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_430).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_431 : ((97281281/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 431, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 431, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 430, cos1016o2c k) + cos1016o2c 431 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 430) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_430
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 431 - ((-4746957/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_431).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_432 : ((18147829/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 432, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 432, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 431, cos1016o2c k) + cos1016o2c 432 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 431) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_431
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 432 - ((-408821/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_432).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_433 : ((19038369/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 433, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 433, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 432, cos1016o2c k) + cos1016o2c 433 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 432) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_432
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 433 - ((44537/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_433).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_434 : ((105171229/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 434, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 434, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 433, cos1016o2c k) + cos1016o2c 434 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 433) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_433
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 434 - ((311887/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_434).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_435 : ((21699113/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 435, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 435, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 434, cos1016o2c k) + cos1016o2c 435 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 434) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_434
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 435 - ((415667/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_435).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_436 : ((25283069/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 436, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 436, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 435, cos1016o2c k) + cos1016o2c 436 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 435) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_435
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 436 - ((-7362289/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_436).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_437 : ((9200227/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 437, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 437, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 436, cos1016o2c k) + cos1016o2c 437 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 436) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_436
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 437 - ((-4564503/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_437).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_438 : ((46054893/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 438, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 438, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 437, cos1016o2c k) + cos1016o2c 438 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 437) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_437
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 438 - ((27129/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_438).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_439 : ((50656869/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 439, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 439, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 438, cos1016o2c k) + cos1016o2c 439 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 438) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_438
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 439 - ((1150619/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_439).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_440 : ((108599551/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 440, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 440, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 439, cos1016o2c k) + cos1016o2c 440 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 439) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_439
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 440 - ((7286813/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_440).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_441 : ((105293711/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 441, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 441, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 440, cos1016o2c k) + cos1016o2c 441 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 440) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_440
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 441 - ((-82621/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_441).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_442 : ((19065487/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 442, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 442, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 441, cos1016o2c k) + cos1016o2c 442 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 441) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_441
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 442 - ((-2491319/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_442).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_443 : ((90478499/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 443, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 443, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 442, cos1016o2c k) + cos1016o2c 443 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 442) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_442
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 443 - ((-75749/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_443).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_444 : ((12055491/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 444, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 444, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 443, cos1016o2c k) + cos1016o2c 444 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 443) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_443
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 444 - ((5966429/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_444).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_445 : ((26555097/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 445, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 445, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 444, cos1016o2c k) + cos1016o2c 445 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 444) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_444
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 445 - ((488873/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_445).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_446 : ((27098289/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 446, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 446, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 445, cos1016o2c k) + cos1016o2c 446 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 445) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_445
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 446 - ((271721/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_446).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_447 : ((50222343/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 447, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 447, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 446, cos1016o2c k) + cos1016o2c 447 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 446) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_446
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 447 - ((-794747/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_447).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_448 : ((22896933/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 448, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 448, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 447, cos1016o2c k) + cos1016o2c 448 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 447) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_447
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 448 - ((-4427977/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_448).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_449 : ((18407041/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 449, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 449, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 448, cos1016o2c k) + cos1016o2c 449 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 448) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_448
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 449 - ((448473/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_449).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_450 : ((50630571/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 450, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 450, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 449, cos1016o2c k) + cos1016o2c 450 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 449) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_449
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 450 - ((9226937/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_450).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_451 : ((108699389/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 451, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 451, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 450, cos1016o2c k) + cos1016o2c 451 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 450) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_450
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 451 - ((7439247/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_451).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_452 : ((105875357/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 452, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 452, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 451, cos1016o2c k) + cos1016o2c 452 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 451) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_451
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 452 - ((-352879/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_452).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_453 : ((19201033/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 453, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 453, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 452, cos1016o2c k) + cos1016o2c 453 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 452) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_452
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 453 - ((-1233649/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_453).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_454 : ((144407/16000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 454, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 454, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 453, cos1016o2c k) + cos1016o2c 454 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 453) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_453
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 454 - ((-574979/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_454).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_455 : ((95092971/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 455, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 455, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 454, cos1016o2c k) + cos1016o2c 455 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 454) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_454
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 455 - ((1209899/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_455).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_456 : ((105079653/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 456, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 456, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 455, cos1016o2c k) + cos1016o2c 456 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 455) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_455
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 456 - ((4993841/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_456).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_457 : ((54524949/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 457, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 457, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 456, cos1016o2c k) + cos1016o2c 457 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 456) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_456
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 457 - ((794249/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_457).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_458 : ((512957/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 458, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 458, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 457, cos1016o2c k) + cos1016o2c 458 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 457) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_457
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 458 - ((-3228749/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_458).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_459 : ((92875139/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 459, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 459, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 458, cos1016o2c k) + cos1016o2c 459 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 458) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_458
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 459 - ((-9715261/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_459).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_460 : ((45316277/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 460, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 460, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 459, cos1016o2c k) + cos1016o2c 460 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 459) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_459
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 460 - ((-448317/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_460).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_461 : ((98320391/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 461, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 461, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 460, cos1016o2c k) + cos1016o2c 461 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 460) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_460
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 461 - ((7688837/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_461).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_462 : ((13437799/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 462, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 462, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 461, cos1016o2c k) + cos1016o2c 462 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 461) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_461
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 462 - ((9183001/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_462).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_463 : ((108154599/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 463, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 463, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 462, cos1016o2c k) + cos1016o2c 463 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 462) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_462
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 463 - ((653207/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_463).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_464 : ((49788651/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 464, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 464, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 463, cos1016o2c k) + cos1016o2c 464 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 463) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_463
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 464 - ((-8576297/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_464).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_465 : ((45534753/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 465, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 465, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 464, cos1016o2c k) + cos1016o2c 465 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 464) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_464
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 465 - ((-2126699/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_465).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_466 : ((91807919/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 466, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 466, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 465, cos1016o2c k) + cos1016o2c 466 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 465) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_465
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 466 - ((739413/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_466).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_467 : ((100986721/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 467, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 467, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 466, cos1016o2c k) + cos1016o2c 467 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 466) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_466
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 467 - ((4589901/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_467).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_468 : ((27192289/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 468, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 468, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 467, cos1016o2c k) + cos1016o2c 468 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 467) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_467
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 468 - ((1556687/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_468).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_469 : ((106856957/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 469, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 469, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 468, cos1016o2c k) + cos1016o2c 469 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 468) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_468
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 469 - ((-1911199/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_469).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_470 : ((608077/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 470, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 470, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 469, cos1016o2c k) + cos1016o2c 470 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 469) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_469
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 470 - ((-9563637/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_470).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_471 : ((1127559/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 471, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 471, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 470, cos1016o2c k) + cos1016o2c 471 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 470) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_470
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 471 - ((-35433/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_471).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_472 : ((93061517/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 472, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 472, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 471, cos1016o2c k) + cos1016o2c 472 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 471) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_471
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 472 - ((2857797/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_472).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_473 : ((102849403/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 473, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 473, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 472, cos1016o2c k) + cos1016o2c 473 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 472) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_472
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 473 - ((4894443/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_473).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_474 : ((54659591/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 474, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 474, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 473, cos1016o2c k) + cos1016o2c 474 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 473) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_473
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 474 - ((6470779/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_474).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_475 : ((52865639/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 475, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 475, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 474, cos1016o2c k) + cos1016o2c 475 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 474) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_474
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 475 - ((-448363/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_475).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_476 : ((19164417/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 476, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 476, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 475, cos1016o2c k) + cos1016o2c 476 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 475) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_475
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 476 - ((-9908193/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_476).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_477 : ((89846601/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 477, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 477, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 476, cos1016o2c k) + cos1016o2c 477 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 476) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_476
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 477 - ((-1493621/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_477).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_478 : ((1879119/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 478, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 478, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 477, cos1016o2c k) + cos1016o2c 478 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 477) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_477
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 478 - ((4110349/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_478).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_479 : ((20783669/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 479, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 479, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 478, cos1016o2c k) + cos1016o2c 479 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 478) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_478
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 479 - ((1992679/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_479).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_480 : ((109538161/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 480, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 480, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 479, cos1016o2c k) + cos1016o2c 480 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 479) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_479
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 480 - ((351301/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_480).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_481 : ((52547503/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 481, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 481, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 480, cos1016o2c k) + cos1016o2c 481 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 480) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_480
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 481 - ((-888431/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_481).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_482 : ((47554683/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 482, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 482, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 481, cos1016o2c k) + cos1016o2c 482 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 481) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_481
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 482 - ((-15601/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_482).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_483 : ((4484173/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 483, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 483, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 482, cos1016o2c k) + cos1016o2c 483 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 482) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_482
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 483 - ((-2712453/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_483).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_484 : ((47138131/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 484, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 484, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 483, cos1016o2c k) + cos1016o2c 484 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 483) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_483
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 484 - ((2296901/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_484).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_485 : ((52132561/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 485, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 485, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 484, cos1016o2c k) + cos1016o2c 485 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 484) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_484
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 485 - ((499493/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_485).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_486 : ((109655859/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 486, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 486, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 485, cos1016o2c k) + cos1016o2c 486 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 485) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_485
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 486 - ((5391737/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_486).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_487 : ((52541901/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 487, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 487, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 486, cos1016o2c k) + cos1016o2c 487 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 486) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_486
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 487 - ((-4571057/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_487).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_488 : ((95097377/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 488, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 488, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 487, cos1016o2c k) + cos1016o2c 488 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 487) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_487
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 488 - ((-399417/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_488).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_489 : ((89575067/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 489, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 489, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 488, cos1016o2c k) + cos1016o2c 489 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 488) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_488
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 489 - ((-552131/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_489).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_490 : ((46974797/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 490, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 490, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 489, cos1016o2c k) + cos1016o2c 490 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 489) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_489
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 490 - ((4375527/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_490).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_491 : ((5195741/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 491, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 491, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 490, cos1016o2c k) + cos1016o2c 491 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 490) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_490
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 491 - ((4983113/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_491).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_492 : ((109719533/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 492, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 492, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 491, cos1016o2c k) + cos1016o2c 492 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 491) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_491
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 492 - ((5805713/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_492).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_493 : ((52856993/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 493, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 493, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 492, cos1016o2c k) + cos1016o2c 493 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 492) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_492
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 493 - ((-4004547/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_493).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_494 : ((19159311/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 494, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 494, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 493, cos1016o2c k) + cos1016o2c 494 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 493) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_493
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 494 - ((-9916431/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_494).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_495 : ((44781531/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 495, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 495, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 494, cos1016o2c k) + cos1016o2c 495 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 494) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_494
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 495 - ((-6232493/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_495).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_496 : ((1860263/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 496, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 496, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 495, cos1016o2c k) + cos1016o2c 496 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 495) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_495
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 496 - ((215693/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_496).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_497 : ((51411043/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 497, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 497, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 496, cos1016o2c k) + cos1016o2c 497 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 496) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_496
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 497 - ((613121/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_497).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_498 : ((856256/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 498, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 498, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 497, cos1016o2c k) + cos1016o2c 498 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 497) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_497
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 498 - ((3389841/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_498).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_499 : ((21378683/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 499, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 499, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 498, cos1016o2c k) + cos1016o2c 499 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 498) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_498
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 499 - ((-2706353/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_499).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_500 : ((24320277/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 500, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 500, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 499, cos1016o2c k) + cos1016o2c 500 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 499) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_499
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 500 - ((-9611307/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_500).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_501 : ((44931931/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 501, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 501, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 500, cos1016o2c k) + cos1016o2c 501 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 500) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_500
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 501 - ((-3708123/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_501).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_502 : ((2863381/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 502, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 502, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 501, cos1016o2c k) + cos1016o2c 502 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 501) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_501
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 502 - ((176533/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_502).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_503 : ((5045243/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 503, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 503, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 502, cos1016o2c k) + cos1016o2c 503 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 502) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_502
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 503 - ((2319417/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_503).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_504 : ((27251139/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 504, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 504, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 503, cos1016o2c k) + cos1016o2c 504 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 503) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_503
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 504 - ((1012587/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_504).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_505 : ((108377099/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 505, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 505, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 504, cos1016o2c k) + cos1016o2c 505 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 504) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_504
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 505 - ((-626457/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_505).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_506 : ((99615583/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 506, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 506, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 505, cos1016o2c k) + cos1016o2c 506 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 505) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_505
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 506 - ((-2190129/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_506).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_507 : ((90837853/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 507, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 507, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 506, cos1016o2c k) + cos1016o2c 507 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 506) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_506
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 507 - ((-877673/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_507).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_508 : ((45068603/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 508, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 508, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 507, cos1016o2c k) + cos1016o2c 508 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 507) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_507
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 508 - ((-699647/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_508).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_509 : ((12268311/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 509, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 509, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 508, cos1016o2c k) + cos1016o2c 509 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 508) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_508
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 509 - ((4005141/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_509).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_510 : ((107521027/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 510, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 510, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 509, cos1016o2c k) + cos1016o2c 510 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 509) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_509
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 510 - ((9375539/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_510).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_511 : ((109706809/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 511, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 511, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 510, cos1016o2c k) + cos1016o2c 511 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 510) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_510
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 511 - ((1093391/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_511).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_512 : ((25681219/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 512, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 512, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 511, cos1016o2c k) + cos1016o2c 512 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 511) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_511
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 512 - ((-6980933/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_512).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_513 : ((92909821/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 513, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 513, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 512, cos1016o2c k) + cos1016o2c 513 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 512) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_512
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 513 - ((-1962811/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_513).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_514 : ((11140249/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 514, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 514, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 513, cos1016o2c k) + cos1016o2c 514 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 513) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_513
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 514 - ((-3786829/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_514).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_515 : ((47379691/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 515, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 515, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 514, cos1016o2c k) + cos1016o2c 515 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 514) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_514
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 515 - ((563839/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_515).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_516 : ((104757451/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 516, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 516, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 515, cos1016o2c k) + cos1016o2c 516 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 515) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_515
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 516 - ((9999069/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_516).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_517 : ((55091559/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 517, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 517, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 516, cos1016o2c k) + cos1016o2c 517 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 516) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_516
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 517 - ((5426667/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_517).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_518 : ((106213911/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 518, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 518, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 517, cos1016o2c k) + cos1016o2c 518 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 517) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_517
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 518 - ((-3968207/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_518).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_519 : ((1204749/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 519, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 519, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 518, cos1016o2c k) + cos1016o2c 519 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 518) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_518
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 519 - ((-9832991/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_519).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_520 : ((89375237/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 520, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 520, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 519, cos1016o2c k) + cos1016o2c 520 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 519) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_519
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 520 - ((-7003683/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_520).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_521 : ((45680741/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 521, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 521, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 520, cos1016o2c k) + cos1016o2c 521 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 520) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_520
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 521 - ((397449/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_521).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_522 : ((50292043/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 522, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 522, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 521, cos1016o2c k) + cos1016o2c 522 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 521) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_521
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 522 - ((2305901/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_522).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_523 : ((27242921/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 523, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 523, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 522, cos1016o2c k) + cos1016o2c 523 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 522) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_522
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 523 - ((4194299/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_523).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_524 : ((54609347/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 524, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 524, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 523, cos1016o2c k) + cos1016o2c 524 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 523) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_523
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 524 - ((24801/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_524).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_525 : ((101120057/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 525, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 525, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 524, cos1016o2c k) + cos1016o2c 525 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 524) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_524
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 525 - ((-8097637/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_525).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_526 : ((91690433/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 526, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 526, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 525, cos1016o2c k) + cos1016o2c 526 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 525) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_525
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 526 - ((-589289/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_526).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_527 : ((89058037/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 527, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 527, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 526, cos1016o2c k) + cos1016o2c 527 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 526) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_526
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 527 - ((-657849/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_527).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_528 : ((381897/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 528, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 528, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 527, cos1016o2c k) + cos1016o2c 528 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 527) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_527
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 528 - ((6417213/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_528).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_529 : ((105435271/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 529, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 529, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 528, cos1016o2c k) + cos1016o2c 529 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 528) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_528
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 529 - ((9962021/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_529).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_530 : ((55219763/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 530, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 530, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 529, cos1016o2c k) + cos1016o2c 530 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 529) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_529
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 530 - ((1001051/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_530).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_531 : ((10623917/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 531, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 531, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 530, cos1016o2c k) + cos1016o2c 531 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 530) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_530
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 531 - ((-1049839/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_531).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_532 : ((48201369/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 532, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 532, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 531, cos1016o2c k) + cos1016o2c 532 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 531) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_531
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 532 - ((-1229429/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_532).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_533 : ((89239033/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 533, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 533, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 532, cos1016o2c k) + cos1016o2c 533 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 532) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_532
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 533 - ((-1432541/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_533).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_534 : ((90769503/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 534, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 534, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 533, cos1016o2c k) + cos1016o2c 534 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 533) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_533
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 534 - ((153147/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_534).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_535 : ((99699411/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 535, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 535, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 534, cos1016o2c k) + cos1016o2c 535 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 534) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_534
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 535 - ((2232727/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_535).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_536 : ((108559051/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 536, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 536, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 535, cos1016o2c k) + cos1016o2c 536 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 535) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_535
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 536 - ((55379/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_536).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_537 : ((109972521/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 537, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 537, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 536, cos1016o2c k) + cos1016o2c 537 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 536) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_536
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 537 - ((141447/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_537).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_538 : ((51387813/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 538, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 538, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 537, cos1016o2c k) + cos1016o2c 538 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 537) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_537
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 538 - ((-1439179/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_538).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_539 : ((18585741/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 539, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 539, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 538, cos1016o2c k) + cos1016o2c 539 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 538) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_538
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 539 - ((-9845921/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_539).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_540 : ((2767109/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 540, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 540, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 539, cos1016o2c k) + cos1016o2c 540 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 539) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_539
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 540 - ((-4380217/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_540).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_541 : ((9322143/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 541, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 541, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 540, cos1016o2c k) + cos1016o2c 541 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 540) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_540
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 541 - ((2337471/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_541).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_542 : ((20622759/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 542, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 542, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 541, cos1016o2c k) + cos1016o2c 542 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 541) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_541
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 542 - ((1978673/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_542).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_543 : ((881197/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 543, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 543, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 542, cos1016o2c k) + cos1016o2c 543 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 542) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_542
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 543 - ((703683/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_543).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_544 : ((13576713/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 544, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 544, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 543, cos1016o2c k) + cos1016o2c 544 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 543) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_543
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 544 - ((-1534921/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_544).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_545 : ((24940037/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 545, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 545, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 544, cos1016o2c k) + cos1016o2c 545 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 544) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_544
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 545 - ((-2213139/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_545).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_546 : ((18148777/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 546, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 546, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 545, cos1016o2c k) + cos1016o2c 546 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 545) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_545
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 546 - ((-9015263/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_546).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_547 : ((22204507/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 547, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 547, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 546, cos1016o2c k) + cos1016o2c 547 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 546) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_546
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 547 - ((-1924857/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_547).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_548 : ((11939543/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 548, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 548, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 547, cos1016o2c k) + cos1016o2c 548 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 547) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_547
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 548 - ((1674829/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_548).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_549 : ((52737657/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 549, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 549, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 548, cos1016o2c k) + cos1016o2c 549 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 548) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_548
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 549 - ((995997/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_549).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_550 : ((27689827/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 550, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 550, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 549, cos1016o2c k) + cos1016o2c 550 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 549) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_549
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 550 - ((2642497/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_550).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_551 : ((26794867/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 551, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 551, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 550, cos1016o2c k) + cos1016o2c 551 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 550) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_550
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 551 - ((-89471/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_551).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_552 : ((1524659/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 552, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 552, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 551, cos1016o2c k) + cos1016o2c 552 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 551) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_551
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 552 - ((-2400073/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_552).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_553 : ((22382787/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 553, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 553, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 552, cos1016o2c k) + cos1016o2c 553 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 552) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_552
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 553 - ((-2011507/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_553).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_554 : ((44678811/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 554, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 554, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 553, cos1016o2c k) + cos1016o2c 554 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 553) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_553
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 554 - ((-86263/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_554).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_555 : ((48591601/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 555, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 555, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 554, cos1016o2c k) + cos1016o2c 555 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 554) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_554
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 555 - ((391329/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_555).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_556 : ((106889419/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 556, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 556, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 555, cos1016o2c k) + cos1016o2c 556 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 555) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_555
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 556 - ((9707217/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_556).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_557 : ((110923441/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 557, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 557, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 556, cos1016o2c k) + cos1016o2c 557 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 556) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_556
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 557 - ((2017511/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_557).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_558 : ((106164573/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 558, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 558, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 557, cos1016o2c k) + cos1016o2c 558 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 557) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_557
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 558 - ((-1189467/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_558).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_559 : ((24074997/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 559, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 559, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 558, cos1016o2c k) + cos1016o2c 559 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 558) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_558
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 559 - ((-1972717/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_559).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_560 : ((88931753/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 560, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 560, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 559, cos1016o2c k) + cos1016o2c 560 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 559) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_559
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 560 - ((-1473447/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_560).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_561 : ((44855787/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 561, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 561, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 560, cos1016o2c k) + cos1016o2c 561 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 560) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_560
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 561 - ((780821/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_561).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_562 : ((49015719/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 562, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 562, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 561, cos1016o2c k) + cos1016o2c 562 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 561) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_561
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 562 - ((260027/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_562).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_563 : ((107537829/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 563, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 563, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 562, cos1016o2c k) + cos1016o2c 563 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 562) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_562
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 563 - ((9507391/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_563).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_564 : ((111004429/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 564, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 564, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 563, cos1016o2c k) + cos1016o2c 564 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 563) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_563
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 564 - ((8669/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_564).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_565 : ((52906173/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 565, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 565, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 564, cos1016o2c k) + cos1016o2c 565 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 564) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_564
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 565 - ((-5191083/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_565).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_566 : ((47945747/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 566, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 566, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 565, cos1016o2c k) + cos1016o2c 566 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 565) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_565
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 566 - ((-2479963/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_566).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_567 : ((88711943/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 567, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 567, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 566, cos1016o2c k) + cos1016o2c 567 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 566) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_566
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 567 - ((-7178551/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_567).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_568 : ((89653843/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 568, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 568, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 567, cos1016o2c k) + cos1016o2c 568 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 567) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_567
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 568 - ((9429/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_568).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_569 : ((784017/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 569, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 569, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 568, cos1016o2c k) + cos1016o2c 569 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 568) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_568
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 569 - ((4174641/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_569).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_570 : ((13440861/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 570, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 570, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 569, cos1016o2c k) + cos1016o2c 570 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 569) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_569
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 570 - ((9525763/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_570).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_571 : ((111152481/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 571, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 571, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 570, cos1016o2c k) + cos1016o2c 571 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 570) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_570
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 571 - ((3626593/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_571).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_572 : ((26550603/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 572, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 572, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 571, cos1016o2c k) + cos1016o2c 572 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 571) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_571
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 572 - ((-4949069/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_572).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_573 : ((96338371/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 573, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 573, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 572, cos1016o2c k) + cos1016o2c 573 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 572) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_572
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 573 - ((-9863041/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_573).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_574 : ((44409837/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 574, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 574, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 573, cos1016o2c k) + cos1016o2c 574 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 573) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_573
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 574 - ((-7517697/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_574).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_575 : ((1783079/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 575, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 575, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 574, cos1016o2c k) + cos1016o2c 575 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 574) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_574
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 575 - ((83819/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_575).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_576 : ((97086099/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 576, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 576, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 575, cos1016o2c k) + cos1016o2c 576 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 575) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_575
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 576 - ((7933149/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_576).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_577 : ((6676839/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 577, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 577, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 576, cos1016o2c k) + cos1016o2c 577 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 576) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_576
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 577 - ((389773/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_577).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_578 : ((27827109/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 578, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 578, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 577, cos1016o2c k) + cos1016o2c 578 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 577) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_577
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 578 - ((1120003/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_578).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_579 : ((107288349/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 579, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 579, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 578, cos1016o2c k) + cos1016o2c 579 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 578) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_578
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 579 - ((-4019087/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_579).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_580 : ((97678289/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 580, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 580, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 579, cos1016o2c k) + cos1016o2c 580 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 579) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_579
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 580 - ((-480453/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_580).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_581 : ((89393229/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 581, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 581, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 580, cos1016o2c k) + cos1016o2c 581 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 580) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_580
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 581 - ((-414203/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_581).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_582 : ((22091887/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 582, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 582, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 581, cos1016o2c k) + cos1016o2c 582 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 581) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_581
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 582 - ((-1024681/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_582).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_583 : ((19064769/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 583, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 583, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 582, cos1016o2c k) + cos1016o2c 583 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 582) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_582
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 583 - ((6957297/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_583).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_584 : ((105298877/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 584, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 584, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 583, cos1016o2c k) + cos1016o2c 584 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 583) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_583
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 584 - ((311751/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_584).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_585 : ((111208779/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 585, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 585, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 584, cos1016o2c k) + cos1016o2c 585 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 584) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_584
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 585 - ((2955451/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_585).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_586 : ((10887737/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 586, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 586, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 585, cos1016o2c k) + cos1016o2c 586 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 585) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_585
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 586 - ((-2330409/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_586).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_587 : ((99957981/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 587, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 587, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 586, cos1016o2c k) + cos1016o2c 587 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 586) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_586
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 587 - ((-8918389/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_587).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_588 : ((45364017/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 588, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 588, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 587, cos1016o2c k) + cos1016o2c 588 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 587) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_587
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 588 - ((-9228947/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_588).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_589 : ((8765419/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 589, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 589, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 588, cos1016o2c k) + cos1016o2c 589 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 588) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_588
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 589 - ((-768211/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_589).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_590 : ((92875229/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 590, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 590, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 589, cos1016o2c k) + cos1016o2c 590 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 589) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_589
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 590 - ((5222039/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_590).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_591 : ((102744799/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 591, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 591, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 590, cos1016o2c k) + cos1016o2c 591 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 590) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_590
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 591 - ((987057/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_591).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_592 : ((55203317/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 592, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 592, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 591, cos1016o2c k) + cos1016o2c 592 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 591) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_591
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 592 - ((1532567/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_592).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_593 : ((55281239/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 593, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 593, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 592, cos1016o2c k) + cos1016o2c 593 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 592) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_592
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 593 - ((39211/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_593).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_594 : ((51556539/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 594, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 594, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 593, cos1016o2c k) + cos1016o2c 594 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 593) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_593
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 594 - ((-18621/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_594).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_595 : ((46594433/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 595, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 595, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 594, cos1016o2c k) + cos1016o2c 595 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 594) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_594
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 595 - ((-2480803/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_595).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_596 : ((43796537/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 596, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 596, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 595, cos1016o2c k) + cos1016o2c 596 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 595) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_595
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 596 - ((-699349/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_596).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_597 : ((721141/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 597, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 597, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 596, cos1016o2c k) + cos1016o2c 597 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 596) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_596
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 597 - ((2550551/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_597).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_598 : ((49545059/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 598, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 598, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 597, cos1016o2c k) + cos1016o2c 598 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 597) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_597
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 598 - ((8948493/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_598).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_599 : ((108353103/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 599, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 599, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 598, cos1016o2c k) + cos1016o2c 599 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 598) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_598
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 599 - ((1852797/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_599).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_600 : ((22332373/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 600, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 600, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 599, cos1016o2c k) + cos1016o2c 600 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 599) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_599
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 600 - ((1654881/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_600).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_601 : ((21358203/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 601, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 601, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 600, cos1016o2c k) + cos1016o2c 601 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 600) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_600
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 601 - ((-97397/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_601).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_602 : ((97025857/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 602, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 602, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 601, cos1016o2c k) + cos1016o2c 602 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 601) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_601
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 602 - ((-4882079/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_602).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_603 : ((22229561/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 603, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 603, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 602, cos1016o2c k) + cos1016o2c 603 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 602) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_602
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 603 - ((-8106613/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_603).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_604 : ((43941923/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 604, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 604, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 603, cos1016o2c k) + cos1016o2c 604 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 603) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_603
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 604 - ((-516699/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_604).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_605 : ((94602503/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 605, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 605, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 604, cos1016o2c k) + cos1016o2c 605 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 604) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_604
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 605 - ((6719657/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_605).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_606 : ((104601377/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 606, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 606, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 605, cos1016o2c k) + cos1016o2c 606 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 605) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_605
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 606 - ((4999937/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_606).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_607 : ((111255503/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 607, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 607, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 606, cos1016o2c k) + cos1016o2c 607 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 606) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_606
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 607 - ((3327563/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_607).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_608 : ((5508811/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 608, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 608, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 607, cos1016o2c k) + cos1016o2c 608 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 607) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_607
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 608 - ((-1078283/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_608).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_609 : ((51041327/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 609, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 609, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 608, cos1016o2c k) + cos1016o2c 609 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 608) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_608
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 609 - ((-4046283/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_609).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_610 : ((18458439/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 610, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 610, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 609, cos1016o2c k) + cos1016o2c 610 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 609) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_609
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 610 - ((-9789459/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_610).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_611 : ((43604451/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 611, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 611, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 610, cos1016o2c k) + cos1016o2c 611 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 610) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_610
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 611 - ((-5082293/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_611).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_612 : ((45070107/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 612, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 612, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 611, cos1016o2c k) + cos1016o2c 612 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 611) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_611
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 612 - ((366539/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_612).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_613 : ((49585283/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 613, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 613, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 612, cos1016o2c k) + cos1016o2c 613 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 612) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_612
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 613 - ((1128919/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_613).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_614 : ((54220163/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 614, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 614, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 613, cos1016o2c k) + cos1016o2c 614 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 613) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_613
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 614 - ((231769/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_614).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_615 : ((111960831/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 615, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 615, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 614, cos1016o2c k) + cos1016o2c 615 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 614) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_614
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 615 - ((704301/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_615).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_616 : ((21494263/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 616, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 616, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 615, cos1016o2c k) + cos1016o2c 616 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 615) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_615
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 616 - ((-1122129/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_616).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_617 : ((97863333/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 617, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 617, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 616, cos1016o2c k) + cos1016o2c 617 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 616) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_616
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 617 - ((-4803491/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_617).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_618 : ((3571691/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 618, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 618, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 617, cos1016o2c k) + cos1016o2c 618 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 617) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_617
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 618 - ((-4285029/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_618).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_619 : ((43612649/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 619, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 619, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 618, cos1016o2c k) + cos1016o2c 619 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 618) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_618
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 619 - ((-2065977/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_619).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_620 : ((23242169/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 620, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 620, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 619, cos1016o2c k) + cos1016o2c 620 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 619) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_619
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 620 - ((2872189/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_620).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_621 : ((12858697/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 621, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 621, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 620, cos1016o2c k) + cos1016o2c 621 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 620) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_620
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 621 - ((99019/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_621).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_622 : ((110661969/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 622, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 622, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 621, cos1016o2c k) + cos1016o2c 622 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 621) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_621
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 622 - ((7793393/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_622).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_623 : ((1392941/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 623, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 623, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 622, cos1016o2c k) + cos1016o2c 623 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 622) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_622
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 623 - ((774311/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_623).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_624 : ((104711943/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 624, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 624, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 623, cos1016o2c k) + cos1016o2c 624 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 623) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_623
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 624 - ((-6722337/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_624).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_625 : ((47356483/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 625, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 625, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 624, cos1016o2c k) + cos1016o2c 625 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 624) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_624
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 625 - ((-9997977/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_625).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_626 : ((17537583/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 626, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 626, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 625, cos1016o2c k) + cos1016o2c 626 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 625) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_625
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 626 - ((-7024051/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_626).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_627 : ((88007847/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 627, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 627, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 626, cos1016o2c k) + cos1016o2c 627 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 626) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_626
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 627 - ((80233/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_627).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_628 : ((11933033/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 628, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 628, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 627, cos1016o2c k) + cos1016o2c 628 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 627) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_627
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 628 - ((7457417/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_628).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_629 : ((105431973/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 629, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 629, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 628, cos1016o2c k) + cos1016o2c 629 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 628) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_628
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 629 - ((9968709/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_629).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_630 : ((111755051/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 630, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 630, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 629, cos1016o2c k) + cos1016o2c 630 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 629) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_629
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 630 - ((3162039/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_630).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_631 : ((110546699/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 631, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 631, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 630, cos1016o2c k) + cos1016o2c 631 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 630) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_630
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 631 - ((-150919/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_631).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_632 : ((102556793/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 632, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 632, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 631, cos1016o2c k) + cos1016o2c 632 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 631) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_631
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 632 - ((-3994453/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_632).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_633 : ((92680119/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 633, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 633, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 632, cos1016o2c k) + cos1016o2c 633 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 632) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_632
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 633 - ((-4937837/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_633).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_634 : ((43470849/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 634, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 634, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 633, cos1016o2c k) + cos1016o2c 634 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 633) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_633
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 634 - ((-5737421/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_634).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_635 : ((3552991/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 635, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 635, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 634, cos1016o2c k) + cos1016o2c 635 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 634) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_634
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 635 - ((1884077/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_635).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_636 : ((24294539/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 636, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 636, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 635, cos1016o2c k) + cos1016o2c 636 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 635) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_635
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 636 - ((8354381/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_636).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_637 : ((53472121/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 637, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 637, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 636, cos1016o2c k) + cos1016o2c 637 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 636) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_636
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 637 - ((4883543/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_637).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_638 : ((56117783/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 638, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 638, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 637, cos1016o2c k) + cos1016o2c 638 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 637) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_637
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 638 - ((1323081/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_638).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_639 : ((109877613/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 639, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 639, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 638, cos1016o2c k) + cos1016o2c 639 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 638) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_638
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 639 - ((-2356953/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_639).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_640 : ((50645919/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 640, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 640, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 639, cos1016o2c k) + cos1016o2c 640 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 639) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_639
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 640 - ((-343391/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_640).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_641 : ((22903323/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 641, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 641, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 640, cos1016o2c k) + cos1016o2c 641 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 640) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_640
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 641 - ((-4838773/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_641).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_642 : ((86606761/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 642, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 642, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 641, cos1016o2c k) + cos1016o2c 642 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 641) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_641
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 642 - ((-5005531/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_642).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_643 : ((44619247/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 643, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 643, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 642, cos1016o2c k) + cos1016o2c 643 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 642) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_642
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 643 - ((2632733/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_643).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_644 : ((12242583/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 644, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 644, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 643, cos1016o2c k) + cos1016o2c 644 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 643) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_643
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 644 - ((870317/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_644).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_645 : ((5378431/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 645, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 645, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 644, cos1016o2c k) + cos1016o2c 645 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 644) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_644
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 645 - ((2407239/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_645).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_646 : ((11245411/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 646, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 646, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 645, cos1016o2c k) + cos1016o2c 646 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 645) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_645
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 646 - ((488649/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_646).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_647 : ((109735879/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 647, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 647, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 646, cos1016o2c k) + cos1016o2c 647 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 646) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_646
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 647 - ((-2717231/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_647).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_648 : ((25253151/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 648, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 648, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 647, cos1016o2c k) + cos1016o2c 648 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 647) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_647
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 648 - ((-348891/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_648).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_649 : ((91380133/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 649, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 649, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 648, cos1016o2c k) + cos1016o2c 649 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 648) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_648
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 649 - ((-9631471/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_649).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_650 : ((86442033/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 650, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 650, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 649, cos1016o2c k) + cos1016o2c 650 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 649) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_649
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 650 - ((-49371/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_650).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_651 : ((44528121/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 651, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 651, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 650, cos1016o2c k) + cos1016o2c 651 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 650) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_650
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 651 - ((2615209/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_651).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_652 : ((48850553/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 652, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 652, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 651, cos1016o2c k) + cos1016o2c 652 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 651) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_651
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 652 - ((1080733/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_652).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_653 : ((21476807/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 653, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 653, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 652, cos1016o2c k) + cos1016o2c 653 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 652) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_652
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 653 - ((9683929/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_653).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_654 : ((22507217/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 654, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 654, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 653, cos1016o2c k) + cos1016o2c 654 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 653) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_653
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 654 - ((103061/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_654).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_655 : ((55104253/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 655, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 655, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 654, cos1016o2c k) + cos1016o2c 655 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 654) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_654
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 655 - ((-2326579/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_655).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_656 : ((20348089/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 656, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 656, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 655, cos1016o2c k) + cos1016o2c 656 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 655) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_655
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 656 - ((-8467061/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_656).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_657 : ((91965019/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 657, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 657, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 656, cos1016o2c k) + cos1016o2c 657 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 656) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_656
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 657 - ((-4887213/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_657).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_658 : ((5402431/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 658, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 658, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 657, cos1016o2c k) + cos1016o2c 658 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 657) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_657
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 658 - ((-5525123/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_658).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_659 : ((11035989/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 659, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 659, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 658, cos1016o2c k) + cos1016o2c 659 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 658) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_658
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 659 - ((57813/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_659).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_660 : ((48228931/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 660, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 660, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 659, cos1016o2c k) + cos1016o2c 660 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 659) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_659
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 660 - ((163419/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_660).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_661 : ((106337487/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 661, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 661, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 660, cos1016o2c k) + cos1016o2c 661 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 660) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_660
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 661 - ((15809/16000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_661).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_662 : ((56186939/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 662, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 662, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 661, cos1016o2c k) + cos1016o2c 662 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 661) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_661
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 662 - ((6037391/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_662).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_663 : ((13898717/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 663, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 663, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 662, cos1016o2c k) + cos1016o2c 663 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 662) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_662
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 663 - ((-591571/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_663).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_664 : ((103454341/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 664, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 664, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 663, cos1016o2c k) + cos1016o2c 664 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 663) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_663
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 664 - ((-1546879/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_664).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_665 : ((93483701/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 665, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 665, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 664, cos1016o2c k) + cos1016o2c 665 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 664) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_664
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 665 - ((-249241/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_665).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_666 : ((17363497/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 666, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 666, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 665, cos1016o2c k) + cos1016o2c 666 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 665) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_665
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 666 - ((-52072/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_666).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_667 : ((87143129/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 667, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 667, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 666, cos1016o2c k) + cos1016o2c 667 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 666) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_666
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 667 - ((81661/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_667).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_668 : ((9427169/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 668, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 668, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 667, cos1016o2c k) + cos1016o2c 668 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 667) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_667
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 668 - ((7129561/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_668).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_669 : ((20853843/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 669, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 669, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 668, cos1016o2c k) + cos1016o2c 669 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 668) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_668
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 669 - ((399941/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_669).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_670 : ((111641931/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 670, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 670, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 669, cos1016o2c k) + cos1016o2c 670 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 669) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_669
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 670 - ((1843429/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_670).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_671 : ((56177859/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 671, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 671, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 670, cos1016o2c k) + cos1016o2c 671 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 670) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_670
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 671 - ((714787/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_671).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_672 : ((10602819/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 672, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 672, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 671, cos1016o2c k) + cos1016o2c 672 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 671) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_671
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 672 - ((-49426/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_672).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_673 : ((768897/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 673, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 673, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 672, cos1016o2c k) + cos1016o2c 673 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 672) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_672
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 673 - ((-1983013/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_673).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_674 : ((43997391/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 674, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 674, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 673, cos1016o2c k) + cos1016o2c 674 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 673) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_673
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 674 - ((-8116343/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_674).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_675 : ((43033777/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 675, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 675, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 674, cos1016o2c k) + cos1016o2c 675 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 674) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_674
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 675 - ((-481557/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_675).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_676 : ((2855101/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 676, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 676, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 675, cos1016o2c k) + cos1016o2c 676 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 675) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_675
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 676 - ((2648339/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_676).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_677 : ((50510923/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 677, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 677, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 676, cos1016o2c k) + cos1016o2c 677 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 676) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_676
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 677 - ((4829807/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_677).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_678 : ((27463221/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 678, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 678, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 677, cos1016o2c k) + cos1016o2c 678 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 677) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_677
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 678 - ((4416019/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_678).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_679 : ((11312927/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 679, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 679, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 678, cos1016o2c k) + cos1016o2c 679 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 678) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_678
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 679 - ((1638693/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_679).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_680 : ((54554301/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 680, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 680, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 679, cos1016o2c k) + cos1016o2c 680 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 679) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_679
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 680 - ((-1004917/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_680).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_681 : ((9993869/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 681, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 681, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 680, cos1016o2c k) + cos1016o2c 681 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 680) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_680
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 681 - ((-573057/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_681).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_682 : ((90492971/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 682, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 682, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 681, cos1016o2c k) + cos1016o2c 682 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 681) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_681
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 682 - ((-9444719/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_682).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_683 : ((42885527/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 683, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 683, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 682, cos1016o2c k) + cos1016o2c 683 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 682) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_682
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 683 - ((-4720917/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_683).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_684 : ((88259523/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 684, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 684, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 683, cos1016o2c k) + cos1016o2c 684 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 683) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_683
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 684 - ((2489469/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_684).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_685 : ((9663919/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 685, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 685, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 684, cos1016o2c k) + cos1016o2c 685 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 684) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_684
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 685 - ((8380667/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_685).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_686 : ((21300801/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 686, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 686, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 685, cos1016o2c k) + cos1016o2c 686 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 685) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_685
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 686 - ((1973163/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_686).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_687 : ((112688061/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 687, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 687, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 686, cos1016o2c k) + cos1016o2c 687 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 686) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_686
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 687 - ((193283/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_687).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_688 : ((111966713/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 688, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 688, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 687, cos1016o2c k) + cos1016o2c 688 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 687) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_687
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 688 - ((-180087/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_688).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_689 : ((104723417/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 689, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 689, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 688, cos1016o2c k) + cos1016o2c 689 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 688) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_688
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 689 - ((-905287/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_689).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_690 : ((5920333/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 690, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 690, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 689, cos1016o2c k) + cos1016o2c 690 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 689) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_689
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 690 - ((-9997089/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_690).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_691 : ((87151207/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 691, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 691, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 690, cos1016o2c k) + cos1016o2c 691 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 690) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_690
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 691 - ((-7573121/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_691).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_692 : ((85907741/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 692, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 692, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 691, cos1016o2c k) + cos1016o2c 692 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 691) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_691
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 692 - ((-621233/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_692).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_693 : ((2290677/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 693, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 693, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 692, cos1016o2c k) + cos1016o2c 693 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 692) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_692
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 693 - ((5720339/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_693).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_694 : ((10136439/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 694, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 694, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 693, cos1016o2c k) + cos1016o2c 694 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 693) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_693
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 694 - ((973831/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_694).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_695 : ((27532171/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 695, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 695, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 694, cos1016o2c k) + cos1016o2c 695 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 694) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_694
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 695 - ((4382647/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_695).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_696 : ((22689119/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 696, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 696, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 695, cos1016o2c k) + cos1016o2c 696 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 695) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_695
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 696 - ((3317911/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_696).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_697 : ((21926351/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 697, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 697, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 696, cos1016o2c k) + cos1016o2c 697 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 696) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_696
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 697 - ((-95321/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_697).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_698 : ((100631911/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 698, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 698, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 697, cos1016o2c k) + cos1016o2c 698 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 697) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_697
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 698 - ((-2249711/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_698).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_699 : ((91009273/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 699, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 699, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 698, cos1016o2c k) + cos1016o2c 699 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 698) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_698
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 699 - ((-4810819/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_699).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_700 : ((21405939/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 700, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 700, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 699, cos1016o2c k) + cos1016o2c 700 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 699) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_699
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 700 - ((-5384517/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_700).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_701 : ((136222/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 701, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 701, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 700, cos1016o2c k) + cos1016o2c 701 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 700) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_700
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 701 - ((389831/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_701).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_702 : ((23723353/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 702, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 702, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 701, cos1016o2c k) + cos1016o2c 702 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 701) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_701
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 702 - ((1928083/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_702).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_703 : ((20977389/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 703, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 703, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 702, cos1016o2c k) + cos1016o2c 703 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 702) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_702
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 703 - ((9994533/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_703).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_704 : ((22433473/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 704, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 704, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 703, cos1016o2c k) + cos1016o2c 704 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 703) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_703
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 704 - ((364071/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_704).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_705 : ((28277493/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 705, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 705, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 704, cos1016o2c k) + cos1016o2c 705 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 704) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_704
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 705 - ((943607/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_705).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_706 : ((53626819/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 706, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 706, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 705, cos1016o2c k) + cos1016o2c 706 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 705) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_705
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 706 - ((-2927667/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_706).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_707 : ((4875373/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 707, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 707, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 706, cos1016o2c k) + cos1016o2c 707 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 706) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_706
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 707 - ((-4872589/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_707).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_708 : ((22172871/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 708, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 708, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 707, cos1016o2c k) + cos1016o2c 708 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 707) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_707
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 708 - ((-68867/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_708).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_709 : ((17029839/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 709, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 709, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 708, cos1016o2c k) + cos1016o2c 709 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 708) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_708
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 709 - ((-3541289/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_709).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_710 : ((88614653/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 710, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 710, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 709, cos1016o2c k) + cos1016o2c 710 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 709) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_709
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 710 - ((1733229/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_710).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_711 : ((48690433/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 711, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 711, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 710, cos1016o2c k) + cos1016o2c 711 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 710) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_710
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 711 - ((8767213/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_711).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_712 : ((26788891/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 712, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 712, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 711, cos1016o2c k) + cos1016o2c 712 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 711) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_711
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 712 - ((4887849/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_712).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_713 : ((28292871/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 713, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 713, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 712, cos1016o2c k) + cos1016o2c 713 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 712) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_712
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 713 - ((150423/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_713).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_714 : ((112507529/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 714, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 714, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 713, cos1016o2c k) + cos1016o2c 714 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 713) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_713
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 714 - ((-132591/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_714).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_715 : ((105492663/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 715, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 715, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 714, cos1016o2c k) + cos1016o2c 715 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 714) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_714
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 715 - ((-3506933/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_715).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_716 : ((95526483/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 716, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 716, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 715, cos1016o2c k) + cos1016o2c 716 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 715) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_715
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 716 - ((-498259/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_716).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_717 : ((87419019/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 717, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 717, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 716, cos1016o2c k) + cos1016o2c 717 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 716) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_716
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 717 - ((-253327/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_717).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_718 : ((42533829/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 718, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 718, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 717, cos1016o2c k) + cos1016o2c 718 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 717) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_717
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 718 - ((-2350361/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_718).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_719 : ((22398387/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 719, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 719, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 718, cos1016o2c k) + cos1016o2c 719 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 718) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_718
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 719 - ((452689/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_719).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_720 : ((12352839/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 720, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 720, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 719, cos1016o2c k) + cos1016o2c 720 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 719) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_719
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 720 - ((2307541/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_720).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_721 : ((13543091/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 721, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 721, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 720, cos1016o2c k) + cos1016o2c 721 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 720) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_720
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 721 - ((1190377/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_721).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_722 : ((113626783/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 722, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 722, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 721, cos1016o2c k) + cos1016o2c 722 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 721) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_721
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 722 - ((1056611/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_722).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_723 : ((112165827/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 723, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 723, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 722, cos1016o2c k) + cos1016o2c 723 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 722) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_722
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 723 - ((-364989/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_723).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_724 : ((52330549/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 724, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 724, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 723, cos1016o2c k) + cos1016o2c 724 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 723) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_723
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 724 - ((-7503729/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_724).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_725 : ((47331149/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 725, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 725, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 724, cos1016o2c k) + cos1016o2c 725 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 724) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_724
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 725 - ((-49989/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_725).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_726 : ((86880853/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 726, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 726, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 725, cos1016o2c k) + cos1016o2c 726 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 725) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_725
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 726 - ((-1556089/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_726).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_727 : ((21242083/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 727, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 727, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 726, cos1016o2c k) + cos1016o2c 727 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 726) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_726
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 727 - ((-1911521/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_727).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_728 : ((17962763/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 728, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 728, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 727, cos1016o2c k) + cos1016o2c 728 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 727) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_727
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 728 - ((4846483/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_728).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_729 : ((49572543/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 729, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 729, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 728, cos1016o2c k) + cos1016o2c 729 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 728) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_728
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 729 - ((9332271/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_729).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_730 : ((108608189/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 730, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 730, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 729, cos1016o2c k) + cos1016o2c 730 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 729) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_729
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 730 - ((9464103/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_730).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_731 : ((28451117/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 731, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 731, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 730, cos1016o2c k) + cos1016o2c 731 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 730) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_730
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 731 - ((5197279/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_731).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_732 : ((112329317/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 732, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 732, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 731, cos1016o2c k) + cos1016o2c 732 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 731) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_731
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 732 - ((-1474151/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_732).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_733 : ((52436021/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 733, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 733, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 732, cos1016o2c k) + cos1016o2c 733 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 732) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_732
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 733 - ((-298251/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_733).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_734 : ((94877799/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 734, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 734, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 733, cos1016o2c k) + cos1016o2c 734 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 733) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_733
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 734 - ((-9993243/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_734).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_735 : ((86945267/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 735, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 735, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 734, cos1016o2c k) + cos1016o2c 735 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 734) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_734
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 735 - ((-1982883/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_735).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_736 : ((84710849/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 736, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 736, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 735, cos1016o2c k) + cos1016o2c 736 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 735) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_735
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 736 - ((-1116709/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_736).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_737 : ((4459467/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 737, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 737, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 736, cos1016o2c k) + cos1016o2c 737 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 736) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_736
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 737 - ((4479491/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_737).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_738 : ((98329483/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 738, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 738, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 737, cos1016o2c k) + cos1016o2c 738 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 737) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_737
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 738 - ((9141143/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_738).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_739 : ((13495639/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 739, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 739, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 738, cos1016o2c k) + cos1016o2c 739 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 738) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_738
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 739 - ((9636629/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_739).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_740 : ((28430307/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 740, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 740, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 739, cos1016o2c k) + cos1016o2c 740 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 739) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_739
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 740 - ((1439279/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_740).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_741 : ((112995067/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 741, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 741, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 740, cos1016o2c k) + cos1016o2c 741 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 740) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_740
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 741 - ((-725161/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_741).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_742 : ((10612177/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 742, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 742, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 741, cos1016o2c k) + cos1016o2c 742 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 741) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_741
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 742 - ((-6872297/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_742).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_743 : ((481019/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 743, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 743, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 742, cos1016o2c k) + cos1016o2c 743 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 742) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_742
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 743 - ((-991697/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_743).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_744 : ((5481259/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 744, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 744, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 743, cos1016o2c k) + cos1016o2c 744 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 743) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_743
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 744 - ((-66427/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_744).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_745 : ((84419537/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 745, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 745, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 744, cos1016o2c k) + cos1016o2c 745 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 744) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_744
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 745 - ((-3279607/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_745).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_746 : ((87822019/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 746, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 746, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 745, cos1016o2c k) + cos1016o2c 746 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 745) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_745
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 746 - ((1701741/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_746).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_747 : ((4819121/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 747, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 747, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 746, cos1016o2c k) + cos1016o2c 747 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 746) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_746
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 747 - ((8561401/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_747).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_748 : ((106288323/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 748, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 748, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 747, cos1016o2c k) + cos1016o2c 748 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 747) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_747
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 748 - ((9906903/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_748).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_749 : ((113144207/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 749, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 749, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 748, cos1016o2c k) + cos1016o2c 749 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 748) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_748
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 749 - ((1714221/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_749).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_750 : ((14239959/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 750, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 750, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 749, cos1016o2c k) + cos1016o2c 750 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 749) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_749
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 750 - ((155293/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_750).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_751 : ((108279393/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 751, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 751, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 750, cos1016o2c k) + cos1016o2c 751 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 750) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_750
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 751 - ((-5639279/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_751).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_752 : ((98712311/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 752, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 752, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 751, cos1016o2c k) + cos1016o2c 752 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 751) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_751
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 752 - ((-4783041/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_752).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_753 : ((2794453/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 753, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 753, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 752, cos1016o2c k) + cos1016o2c 753 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 752) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_752
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 753 - ((-1857763/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_753).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_754 : ((84476887/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 754, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 754, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 753, cos1016o2c k) + cos1016o2c 754 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 753) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_753
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 754 - ((-4944609/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_754).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_755 : ((86030443/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 755, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 755, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 754, cos1016o2c k) + cos1016o2c 755 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 754) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_754
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 755 - ((388639/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_755).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_756 : ((93398473/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 756, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 756, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 755, cos1016o2c k) + cos1016o2c 756 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 755) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_755
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 756 - ((736903/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_756).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_757 : ((4134897/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 757, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 757, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 756, cos1016o2c k) + cos1016o2c 757 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 756) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_756
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 757 - ((1246869/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_757).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_758 : ((111625813/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 758, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 758, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 757, cos1016o2c k) + cos1016o2c 758 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 757) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_757
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 758 - ((2063597/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_758).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_759 : ((57295891/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 759, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 759, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 758, cos1016o2c k) + cos1016o2c 759 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 758) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_758
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 759 - ((2966969/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_759).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_760 : ((27749133/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 760, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 760, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 759, cos1016o2c k) + cos1016o2c 760 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 759) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_759
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 760 - ((-14377/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_760).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_761 : ((102393741/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 761, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 761, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 760, cos1016o2c k) + cos1016o2c 761 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 760) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_760
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 761 - ((-8601791/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_761).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_762 : ((92479643/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 762, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 762, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 761, cos1016o2c k) + cos1016o2c 762 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 761) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_761
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 762 - ((-4956549/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_762).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_763 : ((3419939/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 763, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 763, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 762, cos1016o2c k) + cos1016o2c 763 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 762) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_762
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 763 - ((-872521/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_763).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_764 : ((42213283/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 764, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 764, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 763, cos1016o2c k) + cos1016o2c 764 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 763) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_763
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 764 - ((-1070909/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_764).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_765 : ((44856919/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 765, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 765, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 764, cos1016o2c k) + cos1016o2c 765 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 764) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_764
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 765 - ((330517/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_765).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_766 : ((99106641/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 766, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 766, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 765, cos1016o2c k) + cos1016o2c 766 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 765) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_765
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 766 - ((9393803/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_766).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_767 : ((108620367/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 767, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 767, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 766, cos1016o2c k) + cos1016o2c 767 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 766) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_766
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 767 - ((4757363/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_767).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_768 : ((114233671/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 768, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 768, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 767, cos1016o2c k) + cos1016o2c 768 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 767) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_767
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 768 - ((175447/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_768).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_769 : ((113584163/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 769, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 769, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 768, cos1016o2c k) + cos1016o2c 769 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 768) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_768
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 769 - ((-162127/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_769).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_770 : ((13368889/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 770, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 770, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 769, cos1016o2c k) + cos1016o2c 770 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 769) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_769
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 770 - ((-6632051/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_770).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_771 : ((97123373/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 771, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 771, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 770, cos1016o2c k) + cos1016o2c 771 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 770) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_770
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 771 - ((-9826739/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_771).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_772 : ((88215987/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 772, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 772, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 771, cos1016o2c k) + cos1016o2c 772 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 771) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_771
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 772 - ((-4453193/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_772).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_773 : ((83945267/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 773, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 773, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 772, cos1016o2c k) + cos1016o2c 773 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 772) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_772
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 773 - ((-106743/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_773).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_774 : ((86083611/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 774, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 774, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 773, cos1016o2c k) + cos1016o2c 774 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 773) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_773
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 774 - ((133709/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_774).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_775 : ((1171697/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 775, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 775, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 774, cos1016o2c k) + cos1016o2c 775 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 774) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_774
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 775 - ((7653149/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_775).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_776 : ((103724993/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 776, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 776, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 775, cos1016o2c k) + cos1016o2c 776 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 775) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_775
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 776 - ((9990233/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_776).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_777 : ((111920459/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 777, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 777, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 776, cos1016o2c k) + cos1016o2c 777 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 776) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_776
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 777 - ((4098233/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_777).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_778 : ((22989063/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 778, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 778, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 777, cos1016o2c k) + cos1016o2c 778 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 777) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_777
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 778 - ((47279/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_778).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_779 : ((55780601/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 779, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 779, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 778, cos1016o2c k) + cos1016o2c 779 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 778) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_778
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 779 - ((-3383113/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_779).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_780 : ((20632527/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 780, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 780, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 779, cos1016o2c k) + cos1016o2c 780 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 779) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_779
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 780 - ((-8397567/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_780).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_781 : ((93191179/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 781, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 781, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 780, cos1016o2c k) + cos1016o2c 781 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 780) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_780
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 781 - ((-1246307/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_781).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_782 : ((17143593/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 782, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 782, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 781, cos1016o2c k) + cos1016o2c 782 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 781) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_781
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 782 - ((-3736107/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_782).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_783 : ((41891131/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 783, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 783, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 782, cos1016o2c k) + cos1016o2c 783 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 782) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_782
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 783 - ((-1934703/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_783).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_784 : ((44082161/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 784, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 784, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 783, cos1016o2c k) + cos1016o2c 784 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 783) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_783
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 784 - ((219153/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_784).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_785 : ((97081107/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 785, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 785, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 784, cos1016o2c k) + cos1016o2c 785 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 784) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_784
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 785 - ((1783557/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_785).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_786 : ((106923609/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 786, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 786, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 785, cos1016o2c k) + cos1016o2c 786 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 785) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_785
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 786 - ((4921751/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_786).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_787 : ((5686117/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 787, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 787, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 786, cos1016o2c k) + cos1016o2c 787 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 786) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_786
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 787 - ((6799731/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_787).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_788 : ((28686553/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 788, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 788, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 787, cos1016o2c k) + cos1016o2c 788 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 787) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_787
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 788 - ((128109/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_788).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_789 : ((856171/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 789, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 789, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 788, cos1016o2c k) + cos1016o2c 789 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 788) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_788
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 789 - ((-1288831/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_789).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_790 : ((20064733/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 790, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 790, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 789, cos1016o2c k) + cos1016o2c 790 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 789) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_789
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 790 - ((-9265223/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_790).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_791 : ((18130161/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 791, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 791, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 790, cos1016o2c k) + cos1016o2c 791 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 790) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_790
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 791 - ((-483593/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_791).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_792 : ((84423469/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 792, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 792, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 791, cos1016o2c k) + cos1016o2c 792 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 791) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_791
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 792 - ((-194573/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_792).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_793 : ((84111933/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 793, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 793, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 792, cos1016o2c k) + cos1016o2c 793 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 792) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_792
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 793 - ((-38817/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_793).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_794 : ((89832417/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 794, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 794, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 793, cos1016o2c k) + cos1016o2c 794 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 793) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_793
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 794 - ((1430371/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_794).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_795 : ((49658329/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 795, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 795, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 794, cos1016o2c k) + cos1016o2c 795 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 794) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_794
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 795 - ((9485241/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_795).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_796 : ((108819579/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 796, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 796, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 795, cos1016o2c k) + cos1016o2c 796 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 795) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_795
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 796 - ((9503921/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_796).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_797 : ((114602041/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 797, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 797, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 796, cos1016o2c k) + cos1016o2c 797 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 796) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_796
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 797 - ((2891731/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_797).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_798 : ((114398243/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 798, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 798, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 797, cos1016o2c k) + cos1016o2c 798 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 797) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_797
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 798 - ((-101399/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_798).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_799 : ((108293759/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 799, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 799, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 798, cos1016o2c k) + cos1016o2c 799 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 798) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_798
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 799 - ((-1525871/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_799).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_800 : ((49339571/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 800, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 800, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 799, cos1016o2c k) + cos1016o2c 800 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 799) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_799
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 800 - ((-9613617/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_800).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_801 : ((89304127/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 801, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 801, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 800, cos1016o2c k) + cos1016o2c 801 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 800) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_800
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 801 - ((-1874803/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_801).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_802 : ((83812347/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 802, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 802, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 801, cos1016o2c k) + cos1016o2c 802 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 801) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_801
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 802 - ((-274539/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_802).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_803 : ((84328697/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 803, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 803, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 802, cos1016o2c k) + cos1016o2c 803 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 802) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_802
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 803 - ((10347/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_803).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_804 : ((45323201/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 804, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 804, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 803, cos1016o2c k) + cos1016o2c 804 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 803) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_803
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 804 - ((1263741/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_804).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_805 : ((20064211/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 805, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 805, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 804, cos1016o2c k) + cos1016o2c 805 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 804) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_804
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 805 - ((9675653/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_805).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_806 : ((21924811/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 806, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 806, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 805, cos1016o2c k) + cos1016o2c 806 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 805) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_805
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 806 - ((1163/1250 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_806).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_807 : ((114982561/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 807, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 807, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 806, cos1016o2c k) + cos1016o2c 807 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 806) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_806
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 807 - ((2679753/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_807).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_808 : ((7146703/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 808, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 808, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 807, cos1016o2c k) + cos1016o2c 808 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 807) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_807
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 808 - ((-634313/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_808).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_809 : ((107966857/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 809, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 809, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 808, cos1016o2c k) + cos1016o2c 809 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 808) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_808
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 809 - ((-6379391/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_809).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_810 : ((49140159/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 810, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 810, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 809, cos1016o2c k) + cos1016o2c 810 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 809) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_809
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 810 - ((-9685539/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_810).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_811 : ((17795087/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 811, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 811, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 810, cos1016o2c k) + cos1016o2c 811 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 810) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_810
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 811 - ((-9303883/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_811).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_812 : ((41791321/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 812, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 812, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 811, cos1016o2c k) + cos1016o2c 812 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 811) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_811
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 812 - ((-5391793/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_812).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_813 : ((84139193/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 813, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 813, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 812, cos1016o2c k) + cos1016o2c 813 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 812) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_812
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 813 - ((557551/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_813).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_814 : ((18085563/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 814, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 814, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 813, cos1016o2c k) + cos1016o2c 814 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 813) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_813
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 814 - ((3144811/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_814).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_815 : ((50036431/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 815, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 815, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 814, cos1016o2c k) + cos1016o2c 815 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 814) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_814
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 815 - ((9646047/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_815).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_816 : ((5472233/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 816, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 816, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 815, cos1016o2c k) + cos1016o2c 816 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 815) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_815
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 816 - ((4686399/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_816).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_817 : ((57514409/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 817, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 817, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 816, cos1016o2c k) + cos1016o2c 817 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 816) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_816
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 817 - ((2792579/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_817).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_818 : ((14342431/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 818, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 818, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 817, cos1016o2c k) + cos1016o2c 818 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 817) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_817
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 818 - ((-28837/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_818).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_819 : ((108690847/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 819, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 819, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 818, cos1016o2c k) + cos1016o2c 819 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 818) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_818
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 819 - ((-6047601/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_819).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_820 : ((49570343/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 820, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 820, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 819, cos1016o2c k) + cos1016o2c 820 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 819) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_819
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 820 - ((-9549161/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_820).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_821 : ((89640219/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 821, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 821, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 820, cos1016o2c k) + cos1016o2c 821 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 820) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_820
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 821 - ((-9499467/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_821).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_822 : ((83709637/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 822, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 822, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 821, cos1016o2c k) + cos1016o2c 822 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 821) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_821
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 822 - ((-2964791/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_822).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_823 : ((83538141/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 823, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 823, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 822, cos1016o2c k) + cos1016o2c 823 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 822) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_822
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 823 - ((-1332/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_823).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_824 : ((8918203/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 824, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 824, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 823, cos1016o2c k) + cos1016o2c 824 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 823) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_823
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 824 - ((5644889/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_824).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_825 : ((12319739/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 825, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 825, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 824, cos1016o2c k) + cos1016o2c 825 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 824) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_824
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 825 - ((4688441/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_825).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_826 : ((13527437/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 826, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 826, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 825, cos1016o2c k) + cos1016o2c 826 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 825) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_825
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 826 - ((1207823/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_826).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_827 : ((114627387/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 827, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 827, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 826, cos1016o2c k) + cos1016o2c 827 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 826) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_826
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 827 - ((6408891/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_827).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_828 : ((14430357/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 828, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 828, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 827, cos1016o2c k) + cos1016o2c 828 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 827) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_827
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 828 - ((816469/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_828).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_829 : ((27593573/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 829, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 829, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 828, cos1016o2c k) + cos1016o2c 829 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 828) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_828
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 829 - ((-1266891/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_829).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_830 : ((50635447/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 830, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 830, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 829, cos1016o2c k) + cos1016o2c 830 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 829) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_829
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 830 - ((-4551199/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_830).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_831 : ((91439977/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 831, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 831, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 830, cos1016o2c k) + cos1016o2c 831 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 830) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_830
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 831 - ((-9829917/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_831).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_832 : ((16888183/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 832, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 832, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 831, cos1016o2c k) + cos1016o2c 832 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 831) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_831
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 832 - ((-3499031/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_832).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_833 : ((41399107/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 833, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 833, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 832, cos1016o2c k) + cos1016o2c 833 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 832) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_832
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 833 - ((-1641701/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_833).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_834 : ((43549009/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 834, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 834, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 833, cos1016o2c k) + cos1016o2c 834 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 833) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_833
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 834 - ((1075201/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_834).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_835 : ((95787713/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 835, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 835, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 834, cos1016o2c k) + cos1016o2c 835 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 834) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_834
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 835 - ((1738139/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_835).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_836 : ((105745747/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 836, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 836, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 835, cos1016o2c k) + cos1016o2c 836 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 835) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_835
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 836 - ((4979517/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_836).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_837 : ((113407257/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 837, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 837, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 836, cos1016o2c k) + cos1016o2c 837 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 836) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_836
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 837 - ((766251/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_837).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_838 : ((116038697/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 838, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 838, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 837, cos1016o2c k) + cos1016o2c 838 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 837) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_837
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 838 - ((65811/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_838).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_839 : ((112707941/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 839, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 839, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 838, cos1016o2c k) + cos1016o2c 839 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 838) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_838
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 839 - ((-832439/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_839).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_840 : ((6537793/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 840, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 840, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 839, cos1016o2c k) + cos1016o2c 840 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 839) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_839
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 840 - ((-8102253/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_840).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_841 : ((94606073/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 841, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 841, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 840, cos1016o2c k) + cos1016o2c 841 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 840) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_840
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 841 - ((-1999523/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_841).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_842 : ((17250137/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 842, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 842, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 841, cos1016o2c k) + cos1016o2c 842 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 841) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_841
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 842 - ((-2088597/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_842).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_843 : ((41242481/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 843, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 843, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 842, cos1016o2c k) + cos1016o2c 843 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 842) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_842
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 843 - ((-3764723/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_843).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_844 : ((661169/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 844, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 844, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 843, cos1016o2c k) + cos1016o2c 844 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 843) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_843
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 844 - ((214567/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_844).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_845 : ((18385043/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 845, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 845, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 844, cos1016o2c k) + cos1016o2c 845 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 844) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_844
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 845 - ((7296583/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_845).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_846 : ((101808671/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 846, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 846, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 845, cos1016o2c k) + cos1016o2c 846 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 845) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_845
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 846 - ((1235557/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_846).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_847 : ((110821093/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 847, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 847, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 846, cos1016o2c k) + cos1016o2c 847 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 846) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_846
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 847 - ((4506711/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_847).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_848 : ((28954633/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 848, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 848, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 847, cos1016o2c k) + cos1016o2c 848 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 847) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_847
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 848 - ((4998439/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_848).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_849 : ((7191603/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 849, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 849, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 848, cos1016o2c k) + cos1016o2c 849 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 848) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_848
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 849 - ((-187971/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_849).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_850 : ((21765827/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 850, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 850, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 849, cos1016o2c k) + cos1016o2c 850 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 849) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_849
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 850 - ((-6235513/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_850).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_851 : ((99275399/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 851, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 851, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 850, cos1016o2c k) + cos1016o2c 851 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 850) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_850
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 851 - ((-298523/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_851).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_852 : ((44855203/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 852, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 852, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 851, cos1016o2c k) + cos1016o2c 852 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 851) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_851
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 852 - ((-9563993/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_852).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_853 : ((83432913/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 853, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 853, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 852, cos1016o2c k) + cos1016o2c 853 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 852) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_852
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 853 - ((-6276493/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_853).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_854 : ((41299653/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 854, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 854, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 853, cos1016o2c k) + cos1016o2c 854 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 853) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_853
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 854 - ((-832607/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_854).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_855 : ((87490157/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 855, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 855, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 854, cos1016o2c k) + cos1016o2c 855 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 854) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_854
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 855 - ((4891851/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_855).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_856 : ((96423603/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 856, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 856, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 855, cos1016o2c k) + cos1016o2c 856 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 855) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_855
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 856 - ((4467223/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_856).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_857 : ((21268337/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 857, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 857, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 856, cos1016o2c k) + cos1016o2c 857 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 856) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_856
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 857 - ((4959541/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_857).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_858 : ((56930427/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 858, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 858, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 857, cos1016o2c k) + cos1016o2c 858 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 857) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_857
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 858 - ((7520169/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_858).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_859 : ((116424353/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 859, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 859, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 858, cos1016o2c k) + cos1016o2c 859 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 858) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_858
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 859 - ((2564499/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_859).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_860 : ((4526689/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 860, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 860, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 859, cos1016o2c k) + cos1016o2c 860 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 859) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_859
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 860 - ((-50877/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_860).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_861 : ((52598881/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 861, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 861, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 860, cos1016o2c k) + cos1016o2c 861 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 860) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_860
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 861 - ((-7968463/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_861).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_862 : ((95214223/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 862, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 862, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 861, cos1016o2c k) + cos1016o2c 862 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 861) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_861
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 862 - ((-9982539/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_862).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_863 : ((10823063/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 863, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 863, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 862, cos1016o2c k) + cos1016o2c 863 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 862) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_862
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 863 - ((-8628719/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_863).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_864 : ((20552591/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 864, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 864, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 863, cos1016o2c k) + cos1016o2c 864 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 863) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_863
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 864 - ((-218657/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_864).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_865 : ((8355571/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 865, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 865, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 864, cos1016o2c k) + cos1016o2c 865 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 864) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_864
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 865 - ((673173/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_865).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_866 : ((90163489/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 866, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 866, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 865, cos1016o2c k) + cos1016o2c 866 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 865) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_865
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 866 - ((6608779/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_866).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_867 : ((99819733/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 867, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 867, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 866, cos1016o2c k) + cos1016o2c 867 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 866) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_866
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 867 - ((2414311/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_867).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_868 : ((54650731/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 868, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 868, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 867, cos1016o2c k) + cos1016o2c 868 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 867) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_867
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 868 - ((9482729/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_868).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_869 : ((23090807/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 869, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 869, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 868, cos1016o2c k) + cos1016o2c 869 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 868) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_868
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 869 - ((6153573/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_869).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_870 : ((11623811/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 870, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 870, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 869, cos1016o2c k) + cos1016o2c 870 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 869) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_869
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 870 - ((31403/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_870).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_871 : ((55699731/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 871, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 871, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 870, cos1016o2c k) + cos1016o2c 871 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 870) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_870
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 871 - ((-302353/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_871).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_872 : ((25635503/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 872, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 872, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 871, cos1016o2c k) + cos1016o2c 872 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 871) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_871
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 872 - ((-177129/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_872).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_873 : ((46295139/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 873, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 873, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 872, cos1016o2c k) + cos1016o2c 873 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 872) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_872
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 873 - ((-4975367/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_873).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_874 : ((3392759/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 874, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 874, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 873, cos1016o2c k) + cos1016o2c 874 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 873) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_873
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 874 - ((-7770303/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_874).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_875 : ((81776569/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 875, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 875, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 874, cos1016o2c k) + cos1016o2c 875 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 874) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_874
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 875 - ((-1520703/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_875).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_876 : ((4222723/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 876, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 876, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 875, cos1016o2c k) + cos1016o2c 876 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 875) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_875
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 876 - ((2678891/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_876).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_877 : ((459857/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 877, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 877, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 876, cos1016o2c k) + cos1016o2c 877 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 876) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_876
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 877 - ((375897/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_877).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_878 : ((50935509/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 878, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 878, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 877, cos1016o2c k) + cos1016o2c 878 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 877) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_877
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 878 - ((4950309/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_878).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_879 : ((55464807/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 879, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 879, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 878, cos1016o2c k) + cos1016o2c 879 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 878) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_878
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 879 - ((2264899/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_879).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_880 : ((116206493/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 880, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 880, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 879, cos1016o2c k) + cos1016o2c 880 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 879) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_879
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 880 - ((5277879/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_880).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_881 : ((115996093/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 881, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 881, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 880, cos1016o2c k) + cos1016o2c 881 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 880) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_880
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 881 - ((-1047/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_881).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_882 : ((110371661/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 882, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 882, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 881, cos1016o2c k) + cos1016o2c 882 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 881) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_881
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 882 - ((-702929/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_882).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_883 : ((25287987/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 883, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 883, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 882, cos1016o2c k) + cos1016o2c 883 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 882) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_882
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 883 - ((-9218713/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_883).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_884 : ((11413407/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 884, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 884, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 883, cos1016o2c k) + cos1016o2c 884 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 883) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_883
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 884 - ((-2460923/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_884).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_885 : ((2624963/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 885, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 885, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 884, cos1016o2c k) + cos1016o2c 885 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 884) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_884
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 885 - ((-91343/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_885).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_886 : ((81565203/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 886, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 886, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 885, cos1016o2c k) + cos1016o2c 886 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 885) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_885
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 886 - ((-2432613/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_886).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_887 : ((84779053/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 887, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 887, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 886, cos1016o2c k) + cos1016o2c 887 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 886) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_886
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 887 - ((64297/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_887).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_888 : ((9260953/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 888, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 888, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 887, cos1016o2c k) + cos1016o2c 888 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 887) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_887
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 888 - ((7831477/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_888).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_889 : ((51279619/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 889, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 889, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 888, cos1016o2c k) + cos1016o2c 889 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 888) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_888
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 889 - ((2487677/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_889).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_890 : ((111465923/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 890, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 890, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 889, cos1016o2c k) + cos1016o2c 890 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 889) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_889
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 890 - ((1781537/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_890).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_891 : ((23301547/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 891, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 891, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 890, cos1016o2c k) + cos1016o2c 891 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 890) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_890
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 891 - ((1260703/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_891).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_892 : ((11609411/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 892, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 892, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 891, cos1016o2c k) + cos1016o2c 892 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 891) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_891
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 892 - ((-3301/80000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_892).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_893 : ((110360851/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 893, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 893, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 892, cos1016o2c k) + cos1016o2c 893 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 892) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_892
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 893 - ((-5732259/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_893).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_894 : ((101117639/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 894, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 894, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 893, cos1016o2c k) + cos1016o2c 894 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 893) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_893
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 894 - ((-2310553/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_894).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_895 : ((91271363/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 895, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 895, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 894, cos1016o2c k) + cos1016o2c 895 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 894) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_894
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 895 - ((-2461319/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_895).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_896 : ((83908797/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 896, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 896, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 895, cos1016o2c k) + cos1016o2c 896 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 895) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_895
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 896 - ((-3680783/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_896).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_897 : ((10166217/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 897, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 897, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 896, cos1016o2c k) + cos1016o2c 897 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 896) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_896
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 897 - ((-2578061/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_897).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_898 : ((42167087/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 898, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 898, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 897, cos1016o2c k) + cos1016o2c 898 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 897) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_897
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 898 - ((1502719/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_898).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_899 : ((91980761/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 899, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 899, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 898, cos1016o2c k) + cos1016o2c 899 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 898) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_898
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 899 - ((7647587/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_899).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_900 : ((50944127/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 900, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 900, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 899, cos1016o2c k) + cos1016o2c 900 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 899) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_899
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 900 - ((9908493/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_900).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_901 : ((110982123/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 901, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 901, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 900, cos1016o2c k) + cos1016o2c 901 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 900) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_900
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 901 - ((9094869/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_901).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_902 : ((116449009/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 902, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 902, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 901, cos1016o2c k) + cos1016o2c 902 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 901) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_901
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 902 - ((2733943/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_902).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_903 : ((116604601/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 903, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 903, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 902, cos1016o2c k) + cos1016o2c 903 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 902) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_902
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 903 - ((9787/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_903).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_904 : ((3481431/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 904, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 904, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 903, cos1016o2c k) + cos1016o2c 904 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 903) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_903
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 904 - ((-5197809/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_904).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_905 : ((3201739/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 905, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 905, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 904, cos1016o2c k) + cos1016o2c 905 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 904) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_904
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 905 - ((-1118643/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_905).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_906 : ((92503099/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 906, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 906, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 905, cos1016o2c k) + cos1016o2c 906 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 905) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_905
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 906 - ((-9951549/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_906).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_907 : ((1691903/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 907, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 907, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 906, cos1016o2c k) + cos1016o2c 907 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 906) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_906
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 907 - ((-7906949/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_907).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_908 : ((81144719/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 908, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 908, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 907, cos1016o2c k) + cos1016o2c 908 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 907) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_907
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 908 - ((-3449431/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_908).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_909 : ((83198747/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 909, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 909, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 908, cos1016o2c k) + cos1016o2c 909 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 908) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_908
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 909 - ((513757/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_909).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_910 : ((22531723/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 910, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 910, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 909, cos1016o2c k) + cos1016o2c 910 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 909) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_909
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 910 - ((1385829/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_910).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_911 : ((24955393/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 911, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 911, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 910, cos1016o2c k) + cos1016o2c 911 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 910) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_910
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 911 - ((30299/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_911).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_912 : ((109343937/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 912, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 912, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 911, cos1016o2c k) + cos1016o2c 912 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 911) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_911
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 912 - ((1904673/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_912).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_913 : ((115816333/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 913, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 913, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 912, cos1016o2c k) + cos1016o2c 913 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 912) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_912
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 913 - ((1618349/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_913).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_914 : ((469159/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 914, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 914, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 913, cos1016o2c k) + cos1016o2c 914 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 913) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_913
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 914 - ((1474417/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_914).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_915 : ((113325443/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 915, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 915, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 914, cos1016o2c k) + cos1016o2c 915 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 914) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_914
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 915 - ((-3963307/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_915).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_916 : ((105118757/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 916, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 916, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 915, cos1016o2c k) + cos1016o2c 916 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 915) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_915
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 916 - ((-4102843/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_916).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_917 : ((47566197/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 917, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 917, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 916, cos1016o2c k) + cos1016o2c 917 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 916) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_916
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 917 - ((-9985363/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_917).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_918 : ((17270689/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 918, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 918, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 917, cos1016o2c k) + cos1016o2c 918 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 917) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_917
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 918 - ((-8777949/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_918).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_919 : ((81399889/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 919, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 919, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 918, cos1016o2c k) + cos1016o2c 919 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 918) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_918
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 919 - ((-1238139/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_919).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_920 : ((81742031/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 920, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 920, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 919, cos1016o2c k) + cos1016o2c 920 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 919) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_919
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 920 - ((171571/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_920).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_921 : ((87273127/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 921, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 921, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 920, cos1016o2c k) + cos1016o2c 921 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 920) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_920
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 921 - ((86439/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_921).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_922 : ((1505437/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 922, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 922, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 921, cos1016o2c k) + cos1016o2c 922 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 921) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_921
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 922 - ((9075841/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_922).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_923 : ((106278169/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 923, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 923, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 922, cos1016o2c k) + cos1016o2c 923 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 922) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_922
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 923 - ((9931201/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_923).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_924 : ((28532827/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 924, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 924, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 923, cos1016o2c k) + cos1016o2c 924 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 923) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_923
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 924 - ((7854139/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_924).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_925 : ((117595529/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 925, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 925, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 924, cos1016o2c k) + cos1016o2c 925 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 924) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_924
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 925 - ((3465221/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_925).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_926 : ((115656539/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 926, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 926, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 925, cos1016o2c k) + cos1016o2c 926 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 925) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_925
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 926 - ((-193799/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_926).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_927 : ((54444099/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 927, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 927, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 926, cos1016o2c k) + cos1016o2c 927 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 926) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_926
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 927 - ((-6767341/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_927).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_928 : ((49637981/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 928, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 928, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 927, cos1016o2c k) + cos1016o2c 928 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 927) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_927
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 928 - ((-2402809/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_928).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_929 : ((22407563/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 929, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 929, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 928, cos1016o2c k) + cos1016o2c 929 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 928) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_928
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 929 - ((-964471/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_929).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_930 : ((82762343/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 930, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 930, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 929, cos1016o2c k) + cos1016o2c 930 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 929) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_929
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 930 - ((-6866909/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_930).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_931 : ((16133433/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 931, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 931, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 930, cos1016o2c k) + cos1016o2c 931 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 930) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_930
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 931 - ((-1047089/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_931).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_932 : ((83948277/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 932, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 932, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 931, cos1016o2c k) + cos1016o2c 932 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 931) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_931
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 932 - ((51283/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_932).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_933 : ((22912373/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 933, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 933, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 932, cos1016o2c k) + cos1016o2c 933 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 932) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_932
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 933 - ((1540443/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_933).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_934 : ((101539999/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 934, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 934, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 933, cos1016o2c k) + cos1016o2c 934 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 933) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_933
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 934 - ((9891507/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_934).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_935 : ((55382223/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 935, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 935, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 934, cos1016o2c k) + cos1016o2c 935 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 934) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_934
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 935 - ((9225447/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_935).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_936 : ((116667997/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 936, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 936, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 935, cos1016o2c k) + cos1016o2c 936 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 935) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_935
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 936 - ((5904551/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_936).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_937 : ((117557617/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 937, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 937, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 936, cos1016o2c k) + cos1016o2c 937 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 936) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_936
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 937 - ((44531/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_937).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_938 : ((22636527/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 938, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 938, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 937, cos1016o2c k) + cos1016o2c 938 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 937) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_937
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 938 - ((-2186991/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_938).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_939 : ((52399809/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 939, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 939, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 938, cos1016o2c k) + cos1016o2c 939 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 938) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_938
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 939 - ((-8382017/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_939).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_940 : ((18961027/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 940, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 940, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 939, cos1016o2c k) + cos1016o2c 940 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 939) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_939
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 940 - ((-9993483/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_940).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_941 : ((86047811/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 941, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 941, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 940, cos1016o2c k) + cos1016o2c 941 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 940) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_940
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 941 - ((-2189081/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_941).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_942 : ((81015683/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 942, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 942, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 941, cos1016o2c k) + cos1016o2c 942 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 941) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_941
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 942 - ((-628891/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_942).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_943 : ((5070787/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 943, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 943, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 942, cos1016o2c k) + cos1016o2c 943 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 942) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_942
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 943 - ((117909/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_943).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_944 : ((86360343/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 944, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 944, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 943, cos1016o2c k) + cos1016o2c 944 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 943) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_943
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 944 - ((5228751/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_944).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_945 : ((47608383/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 945, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 945, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 944, cos1016o2c k) + cos1016o2c 945 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 944) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_944
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 945 - ((8857423/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_945).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_946 : ((13150111/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 946, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 946, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 945, cos1016o2c k) + cos1016o2c 946 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 945) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_945
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 946 - ((4992561/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_946).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_947 : ((113502293/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 947, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 947, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 946, cos1016o2c k) + cos1016o2c 947 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 946) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_946
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 947 - ((1660481/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_947).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_948 : ((7361933/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 948, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 948, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 947, cos1016o2c k) + cos1016o2c 948 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 947) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_947
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 948 - ((857927/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_948).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_949 : ((29217337/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 949, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 949, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 948, cos1016o2c k) + cos1016o2c 949 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 948) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_948
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 949 - ((-46029/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_949).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_950 : ((55499717/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 950, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 950, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 949, cos1016o2c k) + cos1016o2c 950 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 949) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_949
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 950 - ((-2934457/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_950).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_951 : ((101823703/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 951, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 951, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 950, cos1016o2c k) + cos1016o2c 951 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 950) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_950
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 951 - ((-9174731/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_951).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_952 : ((22975117/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 952, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 952, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 951, cos1016o2c k) + cos1016o2c 952 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 951) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_951
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 952 - ((-1984447/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_952).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_953 : ((41994083/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 953, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 953, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 952, cos1016o2c k) + cos1016o2c 953 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 952) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_952
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 953 - ((-3955651/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_953).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_954 : ((80278751/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 954, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 954, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 953, cos1016o2c k) + cos1016o2c 954 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 953) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_953
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 954 - ((-741683/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_954).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_955 : ((16359007/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 955, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 955, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 954, cos1016o2c k) + cos1016o2c 955 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 954) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_954
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 955 - ((379321/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_955).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_956 : ((11014117/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 956, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 956, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 955, cos1016o2c k) + cos1016o2c 956 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 955) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_955
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 956 - ((6318901/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_956).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_957 : ((97485813/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 957, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 957, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 956, cos1016o2c k) + cos1016o2c 957 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 956) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_956
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 957 - ((9373877/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_957).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_958 : ((53666203/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 958, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 958, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 957, cos1016o2c k) + cos1016o2c 958 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 957) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_957
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 958 - ((9847593/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_958).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_959 : ((57474383/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 959, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 959, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 958, cos1016o2c k) + cos1016o2c 959 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 958) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_958
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 959 - ((95217/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_959).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_960 : ((1182501/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 960, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 960, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 959, cos1016o2c k) + cos1016o2c 960 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 959) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_959
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 960 - ((1651167/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_960).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_961 : ((116337157/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 961, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 961, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 960, cos1016o2c k) + cos1016o2c 961 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 960) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_960
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 961 - ((-1911943/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_961).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_962 : ((54868529/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 962, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 962, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 961, cos1016o2c k) + cos1016o2c 962 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 961) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_961
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 962 - ((-6599099/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_962).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_963 : ((50125459/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 963, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 963, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 962, cos1016o2c k) + cos1016o2c 963 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 962) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_962
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 963 - ((-474257/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_963).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_964 : ((90459139/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 964, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 964, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 963, cos1016o2c k) + cos1016o2c 964 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 963) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_963
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 964 - ((-9790779/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_964).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_965 : ((83017489/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 965, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 965, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 964, cos1016o2c k) + cos1016o2c 965 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 964) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_964
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 965 - ((-148813/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_965).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_966 : ((79937359/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 966, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 966, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 965, cos1016o2c k) + cos1016o2c 966 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 965) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_965
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 966 - ((-307913/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_966).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_967 : ((41023083/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 967, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 967, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 966, cos1016o2c k) + cos1016o2c 967 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 966) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_966
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 967 - ((2109807/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_967).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_968 : ((1775413/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 968, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 968, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 967, cos1016o2c k) + cos1016o2c 968 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 967) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_967
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 968 - ((1681371/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_968).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_969 : ((49148641/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 969, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 969, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 968, cos1016o2c k) + cos1016o2c 969 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 968) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_968
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 969 - ((595477/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_969).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_970 : ((13508159/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 970, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 970, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 969, cos1016o2c k) + cos1016o2c 970 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 969) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_969
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 970 - ((976899/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_970).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_971 : ((23091401/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 971, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 971, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 970, cos1016o2c k) + cos1016o2c 971 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 970) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_970
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 971 - ((7392733/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_971).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_972 : ((59248797/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 972, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 972, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 971, cos1016o2c k) + cos1016o2c 972 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 971) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_971
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 972 - ((3041589/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_972).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_973 : ((58190011/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 973, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 973, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 972, cos1016o2c k) + cos1016o2c 973 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 972) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_972
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 973 - ((-529143/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_973).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_974 : ((54836061/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 974, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 974, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 973, cos1016o2c k) + cos1016o2c 974 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 973) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_973
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 974 - ((-67069/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_974).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_975 : ((100161297/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 975, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 975, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 974, cos1016o2c k) + cos1016o2c 975 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 974) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_974
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 975 - ((-380393/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_975).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_976 : ((2824139/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 976, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 976, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 975, cos1016o2c k) + cos1016o2c 976 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 975) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_975
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 976 - ((-9787849/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_976).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_977 : ((82897039/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 977, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 977, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 976, cos1016o2c k) + cos1016o2c 977 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 976) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_976
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 977 - ((-7474409/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_977).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_978 : ((79707523/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 978, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 978, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 977, cos1016o2c k) + cos1016o2c 978 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 977) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_977
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 978 - ((-797129/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_978).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_979 : ((81640837/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 979, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 979, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 978, cos1016o2c k) + cos1016o2c 979 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 978) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_978
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 979 - ((967157/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_979).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_980 : ((88182981/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 980, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 980, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 979, cos1016o2c k) + cos1016o2c 980 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 979) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_979
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 980 - ((817893/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_980).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_981 : ((97611489/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 981, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 981, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 980, cos1016o2c k) + cos1016o2c 981 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 980) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_980
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 981 - ((2357377/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_981).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_982 : ((107452151/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 982, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 982, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 981, cos1016o2c k) + cos1016o2c 982 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 981) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_981
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 982 - ((4920831/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_982).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_983 : ((115130201/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 983, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 983, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 982, cos1016o2c k) + cos1016o2c 983 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 982) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_982
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 983 - ((153581/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_983).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_984 : ((118643337/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 984, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 984, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 983, cos1016o2c k) + cos1016o2c 984 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 983) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_983
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 984 - ((439267/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_984).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_985 : ((58539657/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 985, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 985, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 984, cos1016o2c k) + cos1016o2c 985 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 984) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_984
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 985 - ((-1563023/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_985).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_986 : ((27712389/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 986, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 986, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 985, cos1016o2c k) + cos1016o2c 986 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 985) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_985
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 986 - ((-3114379/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_986).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_987 : ((50787331/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 987, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 987, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 986, cos1016o2c k) + cos1016o2c 987 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 986) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_986
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 987 - ((-4636947/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_987).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_988 : ((18331863/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 988, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 988, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 987, cos1016o2c k) + cos1016o2c 988 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 987) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_987
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 988 - ((-9914347/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_988).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_989 : ((83666843/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 989, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 989, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 988, cos1016o2c k) + cos1016o2c 989 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 988) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_988
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 989 - ((-499467/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_989).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_990 : ((79656921/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 990, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 990, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 989, cos1016o2c k) + cos1016o2c 990 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 989) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_989
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 990 - ((-2004461/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_990).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_991 : ((80658099/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 991, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 991, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 990, cos1016o2c k) + cos1016o2c 991 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 990) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_990
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 991 - ((501089/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_991).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_992 : ((43204167/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 992, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 992, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 991, cos1016o2c k) + cos1016o2c 992 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 991) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_991
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 992 - ((1150247/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_992).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_993 : ((47714067/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 993, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 993, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 992, cos1016o2c k) + cos1016o2c 993 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 992) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_992
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 993 - ((2819/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_993).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_994 : ((105405937/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 994, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 994, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 993, cos1016o2c k) + cos1016o2c 994 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 993) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_993
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 994 - ((9978803/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_994).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_995 : ((113791877/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 995, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 995, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 994, cos1016o2c k) + cos1016o2c 995 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 994) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_994
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 995 - ((419347/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_995).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_996 : ((189519/16000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 996, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 996, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 995, cos1016o2c k) + cos1016o2c 996 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 995) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_995
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 996 - ((2329249/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_996).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_997 : ((118196569/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 997, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 997, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 996, cos1016o2c k) + cos1016o2c 997 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 996) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_996
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 997 - ((-125903/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_997).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_998 : ((113101863/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 998, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 998, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 997, cos1016o2c k) + cos1016o2c 998 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 997) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_997
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 998 - ((-2546853/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_998).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_999 : ((104460589/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 999, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 999, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 998, cos1016o2c k) + cos1016o2c 999 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 998) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_998
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 999 - ((-4320137/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_999).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1016o2_1000 : ((94461457/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 1000, cos1016o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 1000, cos1016o2c k)
      = (∑ k ∈ Finset.Icc 11 999, cos1016o2c k) + cos1016o2c 1000 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 999) (by norm_num) cos1016o2c
    simpa using h
  have hprev := psum1016o2_999
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1016o2c 1000 - ((-2499533/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1016o2_br_1000).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 32768 in
theorem psum1016o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 1000 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos1016o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum1016o2_11
  · exact le_trans (by norm_num) psum1016o2_12
  · exact le_trans (by norm_num) psum1016o2_13
  · exact le_trans (by norm_num) psum1016o2_14
  · exact le_trans (by norm_num) psum1016o2_15
  · exact le_trans (by norm_num) psum1016o2_16
  · exact le_trans (by norm_num) psum1016o2_17
  · exact le_trans (by norm_num) psum1016o2_18
  · exact le_trans (by norm_num) psum1016o2_19
  · exact le_trans (by norm_num) psum1016o2_20
  · exact le_trans (by norm_num) psum1016o2_21
  · exact le_trans (by norm_num) psum1016o2_22
  · exact le_trans (by norm_num) psum1016o2_23
  · exact le_trans (by norm_num) psum1016o2_24
  · exact le_trans (by norm_num) psum1016o2_25
  · exact le_trans (by norm_num) psum1016o2_26
  · exact le_trans (by norm_num) psum1016o2_27
  · exact le_trans (by norm_num) psum1016o2_28
  · exact le_trans (by norm_num) psum1016o2_29
  · exact le_trans (by norm_num) psum1016o2_30
  · exact le_trans (by norm_num) psum1016o2_31
  · exact le_trans (by norm_num) psum1016o2_32
  · exact le_trans (by norm_num) psum1016o2_33
  · exact le_trans (by norm_num) psum1016o2_34
  · exact le_trans (by norm_num) psum1016o2_35
  · exact le_trans (by norm_num) psum1016o2_36
  · exact le_trans (by norm_num) psum1016o2_37
  · exact le_trans (by norm_num) psum1016o2_38
  · exact le_trans (by norm_num) psum1016o2_39
  · exact le_trans (by norm_num) psum1016o2_40
  · exact le_trans (by norm_num) psum1016o2_41
  · exact le_trans (by norm_num) psum1016o2_42
  · exact le_trans (by norm_num) psum1016o2_43
  · exact le_trans (by norm_num) psum1016o2_44
  · exact le_trans (by norm_num) psum1016o2_45
  · exact le_trans (by norm_num) psum1016o2_46
  · exact le_trans (by norm_num) psum1016o2_47
  · exact le_trans (by norm_num) psum1016o2_48
  · exact le_trans (by norm_num) psum1016o2_49
  · exact le_trans (by norm_num) psum1016o2_50
  · exact le_trans (by norm_num) psum1016o2_51
  · exact le_trans (by norm_num) psum1016o2_52
  · exact le_trans (by norm_num) psum1016o2_53
  · exact le_trans (by norm_num) psum1016o2_54
  · exact le_trans (by norm_num) psum1016o2_55
  · exact le_trans (by norm_num) psum1016o2_56
  · exact le_trans (by norm_num) psum1016o2_57
  · exact le_trans (by norm_num) psum1016o2_58
  · exact le_trans (by norm_num) psum1016o2_59
  · exact le_trans (by norm_num) psum1016o2_60
  · exact le_trans (by norm_num) psum1016o2_61
  · exact le_trans (by norm_num) psum1016o2_62
  · exact le_trans (by norm_num) psum1016o2_63
  · exact le_trans (by norm_num) psum1016o2_64
  · exact le_trans (by norm_num) psum1016o2_65
  · exact le_trans (by norm_num) psum1016o2_66
  · exact le_trans (by norm_num) psum1016o2_67
  · exact le_trans (by norm_num) psum1016o2_68
  · exact le_trans (by norm_num) psum1016o2_69
  · exact le_trans (by norm_num) psum1016o2_70
  · exact le_trans (by norm_num) psum1016o2_71
  · exact le_trans (by norm_num) psum1016o2_72
  · exact le_trans (by norm_num) psum1016o2_73
  · exact le_trans (by norm_num) psum1016o2_74
  · exact le_trans (by norm_num) psum1016o2_75
  · exact le_trans (by norm_num) psum1016o2_76
  · exact le_trans (by norm_num) psum1016o2_77
  · exact le_trans (by norm_num) psum1016o2_78
  · exact le_trans (by norm_num) psum1016o2_79
  · exact le_trans (by norm_num) psum1016o2_80
  · exact le_trans (by norm_num) psum1016o2_81
  · exact le_trans (by norm_num) psum1016o2_82
  · exact le_trans (by norm_num) psum1016o2_83
  · exact le_trans (by norm_num) psum1016o2_84
  · exact le_trans (by norm_num) psum1016o2_85
  · exact le_trans (by norm_num) psum1016o2_86
  · exact le_trans (by norm_num) psum1016o2_87
  · exact le_trans (by norm_num) psum1016o2_88
  · exact le_trans (by norm_num) psum1016o2_89
  · exact le_trans (by norm_num) psum1016o2_90
  · exact le_trans (by norm_num) psum1016o2_91
  · exact le_trans (by norm_num) psum1016o2_92
  · exact le_trans (by norm_num) psum1016o2_93
  · exact le_trans (by norm_num) psum1016o2_94
  · exact le_trans (by norm_num) psum1016o2_95
  · exact le_trans (by norm_num) psum1016o2_96
  · exact le_trans (by norm_num) psum1016o2_97
  · exact le_trans (by norm_num) psum1016o2_98
  · exact le_trans (by norm_num) psum1016o2_99
  · exact le_trans (by norm_num) psum1016o2_100
  · exact le_trans (by norm_num) psum1016o2_101
  · exact le_trans (by norm_num) psum1016o2_102
  · exact le_trans (by norm_num) psum1016o2_103
  · exact le_trans (by norm_num) psum1016o2_104
  · exact le_trans (by norm_num) psum1016o2_105
  · exact le_trans (by norm_num) psum1016o2_106
  · exact le_trans (by norm_num) psum1016o2_107
  · exact le_trans (by norm_num) psum1016o2_108
  · exact le_trans (by norm_num) psum1016o2_109
  · exact le_trans (by norm_num) psum1016o2_110
  · exact le_trans (by norm_num) psum1016o2_111
  · exact le_trans (by norm_num) psum1016o2_112
  · exact le_trans (by norm_num) psum1016o2_113
  · exact le_trans (by norm_num) psum1016o2_114
  · exact le_trans (by norm_num) psum1016o2_115
  · exact le_trans (by norm_num) psum1016o2_116
  · exact le_trans (by norm_num) psum1016o2_117
  · exact le_trans (by norm_num) psum1016o2_118
  · exact le_trans (by norm_num) psum1016o2_119
  · exact le_trans (by norm_num) psum1016o2_120
  · exact le_trans (by norm_num) psum1016o2_121
  · exact le_trans (by norm_num) psum1016o2_122
  · exact le_trans (by norm_num) psum1016o2_123
  · exact le_trans (by norm_num) psum1016o2_124
  · exact le_trans (by norm_num) psum1016o2_125
  · exact le_trans (by norm_num) psum1016o2_126
  · exact le_trans (by norm_num) psum1016o2_127
  · exact le_trans (by norm_num) psum1016o2_128
  · exact le_trans (by norm_num) psum1016o2_129
  · exact le_trans (by norm_num) psum1016o2_130
  · exact le_trans (by norm_num) psum1016o2_131
  · exact le_trans (by norm_num) psum1016o2_132
  · exact le_trans (by norm_num) psum1016o2_133
  · exact le_trans (by norm_num) psum1016o2_134
  · exact le_trans (by norm_num) psum1016o2_135
  · exact le_trans (by norm_num) psum1016o2_136
  · exact le_trans (by norm_num) psum1016o2_137
  · exact le_trans (by norm_num) psum1016o2_138
  · exact le_trans (by norm_num) psum1016o2_139
  · exact le_trans (by norm_num) psum1016o2_140
  · exact le_trans (by norm_num) psum1016o2_141
  · exact le_trans (by norm_num) psum1016o2_142
  · exact le_trans (by norm_num) psum1016o2_143
  · exact le_trans (by norm_num) psum1016o2_144
  · exact le_trans (by norm_num) psum1016o2_145
  · exact le_trans (by norm_num) psum1016o2_146
  · exact le_trans (by norm_num) psum1016o2_147
  · exact le_trans (by norm_num) psum1016o2_148
  · exact le_trans (by norm_num) psum1016o2_149
  · exact le_trans (by norm_num) psum1016o2_150
  · exact le_trans (by norm_num) psum1016o2_151
  · exact le_trans (by norm_num) psum1016o2_152
  · exact le_trans (by norm_num) psum1016o2_153
  · exact le_trans (by norm_num) psum1016o2_154
  · exact le_trans (by norm_num) psum1016o2_155
  · exact le_trans (by norm_num) psum1016o2_156
  · exact le_trans (by norm_num) psum1016o2_157
  · exact le_trans (by norm_num) psum1016o2_158
  · exact le_trans (by norm_num) psum1016o2_159
  · exact le_trans (by norm_num) psum1016o2_160
  · exact le_trans (by norm_num) psum1016o2_161
  · exact le_trans (by norm_num) psum1016o2_162
  · exact le_trans (by norm_num) psum1016o2_163
  · exact le_trans (by norm_num) psum1016o2_164
  · exact le_trans (by norm_num) psum1016o2_165
  · exact le_trans (by norm_num) psum1016o2_166
  · exact le_trans (by norm_num) psum1016o2_167
  · exact le_trans (by norm_num) psum1016o2_168
  · exact le_trans (by norm_num) psum1016o2_169
  · exact le_trans (by norm_num) psum1016o2_170
  · exact le_trans (by norm_num) psum1016o2_171
  · exact le_trans (by norm_num) psum1016o2_172
  · exact le_trans (by norm_num) psum1016o2_173
  · exact le_trans (by norm_num) psum1016o2_174
  · exact le_trans (by norm_num) psum1016o2_175
  · exact le_trans (by norm_num) psum1016o2_176
  · exact le_trans (by norm_num) psum1016o2_177
  · exact le_trans (by norm_num) psum1016o2_178
  · exact le_trans (by norm_num) psum1016o2_179
  · exact le_trans (by norm_num) psum1016o2_180
  · exact le_trans (by norm_num) psum1016o2_181
  · exact le_trans (by norm_num) psum1016o2_182
  · exact le_trans (by norm_num) psum1016o2_183
  · exact le_trans (by norm_num) psum1016o2_184
  · exact le_trans (by norm_num) psum1016o2_185
  · exact le_trans (by norm_num) psum1016o2_186
  · exact le_trans (by norm_num) psum1016o2_187
  · exact le_trans (by norm_num) psum1016o2_188
  · exact le_trans (by norm_num) psum1016o2_189
  · exact le_trans (by norm_num) psum1016o2_190
  · exact le_trans (by norm_num) psum1016o2_191
  · exact le_trans (by norm_num) psum1016o2_192
  · exact le_trans (by norm_num) psum1016o2_193
  · exact le_trans (by norm_num) psum1016o2_194
  · exact le_trans (by norm_num) psum1016o2_195
  · exact le_trans (by norm_num) psum1016o2_196
  · exact le_trans (by norm_num) psum1016o2_197
  · exact le_trans (by norm_num) psum1016o2_198
  · exact le_trans (by norm_num) psum1016o2_199
  · exact le_trans (by norm_num) psum1016o2_200
  · exact le_trans (by norm_num) psum1016o2_201
  · exact le_trans (by norm_num) psum1016o2_202
  · exact le_trans (by norm_num) psum1016o2_203
  · exact le_trans (by norm_num) psum1016o2_204
  · exact le_trans (by norm_num) psum1016o2_205
  · exact le_trans (by norm_num) psum1016o2_206
  · exact le_trans (by norm_num) psum1016o2_207
  · exact le_trans (by norm_num) psum1016o2_208
  · exact le_trans (by norm_num) psum1016o2_209
  · exact le_trans (by norm_num) psum1016o2_210
  · exact le_trans (by norm_num) psum1016o2_211
  · exact le_trans (by norm_num) psum1016o2_212
  · exact le_trans (by norm_num) psum1016o2_213
  · exact le_trans (by norm_num) psum1016o2_214
  · exact le_trans (by norm_num) psum1016o2_215
  · exact le_trans (by norm_num) psum1016o2_216
  · exact le_trans (by norm_num) psum1016o2_217
  · exact le_trans (by norm_num) psum1016o2_218
  · exact le_trans (by norm_num) psum1016o2_219
  · exact le_trans (by norm_num) psum1016o2_220
  · exact le_trans (by norm_num) psum1016o2_221
  · exact le_trans (by norm_num) psum1016o2_222
  · exact le_trans (by norm_num) psum1016o2_223
  · exact le_trans (by norm_num) psum1016o2_224
  · exact le_trans (by norm_num) psum1016o2_225
  · exact le_trans (by norm_num) psum1016o2_226
  · exact le_trans (by norm_num) psum1016o2_227
  · exact le_trans (by norm_num) psum1016o2_228
  · exact le_trans (by norm_num) psum1016o2_229
  · exact le_trans (by norm_num) psum1016o2_230
  · exact le_trans (by norm_num) psum1016o2_231
  · exact le_trans (by norm_num) psum1016o2_232
  · exact le_trans (by norm_num) psum1016o2_233
  · exact le_trans (by norm_num) psum1016o2_234
  · exact le_trans (by norm_num) psum1016o2_235
  · exact le_trans (by norm_num) psum1016o2_236
  · exact le_trans (by norm_num) psum1016o2_237
  · exact le_trans (by norm_num) psum1016o2_238
  · exact le_trans (by norm_num) psum1016o2_239
  · exact le_trans (by norm_num) psum1016o2_240
  · exact le_trans (by norm_num) psum1016o2_241
  · exact le_trans (by norm_num) psum1016o2_242
  · exact le_trans (by norm_num) psum1016o2_243
  · exact le_trans (by norm_num) psum1016o2_244
  · exact le_trans (by norm_num) psum1016o2_245
  · exact le_trans (by norm_num) psum1016o2_246
  · exact le_trans (by norm_num) psum1016o2_247
  · exact le_trans (by norm_num) psum1016o2_248
  · exact le_trans (by norm_num) psum1016o2_249
  · exact le_trans (by norm_num) psum1016o2_250
  · exact le_trans (by norm_num) psum1016o2_251
  · exact le_trans (by norm_num) psum1016o2_252
  · exact le_trans (by norm_num) psum1016o2_253
  · exact le_trans (by norm_num) psum1016o2_254
  · exact le_trans (by norm_num) psum1016o2_255
  · exact le_trans (by norm_num) psum1016o2_256
  · exact le_trans (by norm_num) psum1016o2_257
  · exact le_trans (by norm_num) psum1016o2_258
  · exact le_trans (by norm_num) psum1016o2_259
  · exact le_trans (by norm_num) psum1016o2_260
  · exact le_trans (by norm_num) psum1016o2_261
  · exact le_trans (by norm_num) psum1016o2_262
  · exact le_trans (by norm_num) psum1016o2_263
  · exact le_trans (by norm_num) psum1016o2_264
  · exact le_trans (by norm_num) psum1016o2_265
  · exact le_trans (by norm_num) psum1016o2_266
  · exact le_trans (by norm_num) psum1016o2_267
  · exact le_trans (by norm_num) psum1016o2_268
  · exact le_trans (by norm_num) psum1016o2_269
  · exact le_trans (by norm_num) psum1016o2_270
  · exact le_trans (by norm_num) psum1016o2_271
  · exact le_trans (by norm_num) psum1016o2_272
  · exact le_trans (by norm_num) psum1016o2_273
  · exact le_trans (by norm_num) psum1016o2_274
  · exact le_trans (by norm_num) psum1016o2_275
  · exact le_trans (by norm_num) psum1016o2_276
  · exact le_trans (by norm_num) psum1016o2_277
  · exact le_trans (by norm_num) psum1016o2_278
  · exact le_trans (by norm_num) psum1016o2_279
  · exact le_trans (by norm_num) psum1016o2_280
  · exact le_trans (by norm_num) psum1016o2_281
  · exact le_trans (by norm_num) psum1016o2_282
  · exact le_trans (by norm_num) psum1016o2_283
  · exact le_trans (by norm_num) psum1016o2_284
  · exact le_trans (by norm_num) psum1016o2_285
  · exact le_trans (by norm_num) psum1016o2_286
  · exact le_trans (by norm_num) psum1016o2_287
  · exact le_trans (by norm_num) psum1016o2_288
  · exact le_trans (by norm_num) psum1016o2_289
  · exact le_trans (by norm_num) psum1016o2_290
  · exact le_trans (by norm_num) psum1016o2_291
  · exact le_trans (by norm_num) psum1016o2_292
  · exact le_trans (by norm_num) psum1016o2_293
  · exact le_trans (by norm_num) psum1016o2_294
  · exact le_trans (by norm_num) psum1016o2_295
  · exact le_trans (by norm_num) psum1016o2_296
  · exact le_trans (by norm_num) psum1016o2_297
  · exact le_trans (by norm_num) psum1016o2_298
  · exact le_trans (by norm_num) psum1016o2_299
  · exact le_trans (by norm_num) psum1016o2_300
  · exact le_trans (by norm_num) psum1016o2_301
  · exact le_trans (by norm_num) psum1016o2_302
  · exact le_trans (by norm_num) psum1016o2_303
  · exact le_trans (by norm_num) psum1016o2_304
  · exact le_trans (by norm_num) psum1016o2_305
  · exact le_trans (by norm_num) psum1016o2_306
  · exact le_trans (by norm_num) psum1016o2_307
  · exact le_trans (by norm_num) psum1016o2_308
  · exact le_trans (by norm_num) psum1016o2_309
  · exact le_trans (by norm_num) psum1016o2_310
  · exact le_trans (by norm_num) psum1016o2_311
  · exact le_trans (by norm_num) psum1016o2_312
  · exact le_trans (by norm_num) psum1016o2_313
  · exact le_trans (by norm_num) psum1016o2_314
  · exact le_trans (by norm_num) psum1016o2_315
  · exact le_trans (by norm_num) psum1016o2_316
  · exact le_trans (by norm_num) psum1016o2_317
  · exact le_trans (by norm_num) psum1016o2_318
  · exact le_trans (by norm_num) psum1016o2_319
  · exact le_trans (by norm_num) psum1016o2_320
  · exact le_trans (by norm_num) psum1016o2_321
  · exact le_trans (by norm_num) psum1016o2_322
  · exact le_trans (by norm_num) psum1016o2_323
  · exact le_trans (by norm_num) psum1016o2_324
  · exact le_trans (by norm_num) psum1016o2_325
  · exact le_trans (by norm_num) psum1016o2_326
  · exact le_trans (by norm_num) psum1016o2_327
  · exact le_trans (by norm_num) psum1016o2_328
  · exact le_trans (by norm_num) psum1016o2_329
  · exact le_trans (by norm_num) psum1016o2_330
  · exact le_trans (by norm_num) psum1016o2_331
  · exact le_trans (by norm_num) psum1016o2_332
  · exact le_trans (by norm_num) psum1016o2_333
  · exact le_trans (by norm_num) psum1016o2_334
  · exact le_trans (by norm_num) psum1016o2_335
  · exact le_trans (by norm_num) psum1016o2_336
  · exact le_trans (by norm_num) psum1016o2_337
  · exact le_trans (by norm_num) psum1016o2_338
  · exact le_trans (by norm_num) psum1016o2_339
  · exact le_trans (by norm_num) psum1016o2_340
  · exact le_trans (by norm_num) psum1016o2_341
  · exact le_trans (by norm_num) psum1016o2_342
  · exact le_trans (by norm_num) psum1016o2_343
  · exact le_trans (by norm_num) psum1016o2_344
  · exact le_trans (by norm_num) psum1016o2_345
  · exact le_trans (by norm_num) psum1016o2_346
  · exact le_trans (by norm_num) psum1016o2_347
  · exact le_trans (by norm_num) psum1016o2_348
  · exact le_trans (by norm_num) psum1016o2_349
  · exact le_trans (by norm_num) psum1016o2_350
  · exact le_trans (by norm_num) psum1016o2_351
  · exact le_trans (by norm_num) psum1016o2_352
  · exact le_trans (by norm_num) psum1016o2_353
  · exact le_trans (by norm_num) psum1016o2_354
  · exact le_trans (by norm_num) psum1016o2_355
  · exact le_trans (by norm_num) psum1016o2_356
  · exact le_trans (by norm_num) psum1016o2_357
  · exact le_trans (by norm_num) psum1016o2_358
  · exact le_trans (by norm_num) psum1016o2_359
  · exact le_trans (by norm_num) psum1016o2_360
  · exact le_trans (by norm_num) psum1016o2_361
  · exact le_trans (by norm_num) psum1016o2_362
  · exact le_trans (by norm_num) psum1016o2_363
  · exact le_trans (by norm_num) psum1016o2_364
  · exact le_trans (by norm_num) psum1016o2_365
  · exact le_trans (by norm_num) psum1016o2_366
  · exact le_trans (by norm_num) psum1016o2_367
  · exact le_trans (by norm_num) psum1016o2_368
  · exact le_trans (by norm_num) psum1016o2_369
  · exact le_trans (by norm_num) psum1016o2_370
  · exact le_trans (by norm_num) psum1016o2_371
  · exact le_trans (by norm_num) psum1016o2_372
  · exact le_trans (by norm_num) psum1016o2_373
  · exact le_trans (by norm_num) psum1016o2_374
  · exact le_trans (by norm_num) psum1016o2_375
  · exact le_trans (by norm_num) psum1016o2_376
  · exact le_trans (by norm_num) psum1016o2_377
  · exact le_trans (by norm_num) psum1016o2_378
  · exact le_trans (by norm_num) psum1016o2_379
  · exact le_trans (by norm_num) psum1016o2_380
  · exact le_trans (by norm_num) psum1016o2_381
  · exact le_trans (by norm_num) psum1016o2_382
  · exact le_trans (by norm_num) psum1016o2_383
  · exact le_trans (by norm_num) psum1016o2_384
  · exact le_trans (by norm_num) psum1016o2_385
  · exact le_trans (by norm_num) psum1016o2_386
  · exact le_trans (by norm_num) psum1016o2_387
  · exact le_trans (by norm_num) psum1016o2_388
  · exact le_trans (by norm_num) psum1016o2_389
  · exact le_trans (by norm_num) psum1016o2_390
  · exact le_trans (by norm_num) psum1016o2_391
  · exact le_trans (by norm_num) psum1016o2_392
  · exact le_trans (by norm_num) psum1016o2_393
  · exact le_trans (by norm_num) psum1016o2_394
  · exact le_trans (by norm_num) psum1016o2_395
  · exact le_trans (by norm_num) psum1016o2_396
  · exact le_trans (by norm_num) psum1016o2_397
  · exact le_trans (by norm_num) psum1016o2_398
  · exact le_trans (by norm_num) psum1016o2_399
  · exact le_trans (by norm_num) psum1016o2_400
  · exact le_trans (by norm_num) psum1016o2_401
  · exact le_trans (by norm_num) psum1016o2_402
  · exact le_trans (by norm_num) psum1016o2_403
  · exact le_trans (by norm_num) psum1016o2_404
  · exact le_trans (by norm_num) psum1016o2_405
  · exact le_trans (by norm_num) psum1016o2_406
  · exact le_trans (by norm_num) psum1016o2_407
  · exact le_trans (by norm_num) psum1016o2_408
  · exact le_trans (by norm_num) psum1016o2_409
  · exact le_trans (by norm_num) psum1016o2_410
  · exact le_trans (by norm_num) psum1016o2_411
  · exact le_trans (by norm_num) psum1016o2_412
  · exact le_trans (by norm_num) psum1016o2_413
  · exact le_trans (by norm_num) psum1016o2_414
  · exact le_trans (by norm_num) psum1016o2_415
  · exact le_trans (by norm_num) psum1016o2_416
  · exact le_trans (by norm_num) psum1016o2_417
  · exact le_trans (by norm_num) psum1016o2_418
  · exact le_trans (by norm_num) psum1016o2_419
  · exact le_trans (by norm_num) psum1016o2_420
  · exact le_trans (by norm_num) psum1016o2_421
  · exact le_trans (by norm_num) psum1016o2_422
  · exact le_trans (by norm_num) psum1016o2_423
  · exact le_trans (by norm_num) psum1016o2_424
  · exact le_trans (by norm_num) psum1016o2_425
  · exact le_trans (by norm_num) psum1016o2_426
  · exact le_trans (by norm_num) psum1016o2_427
  · exact le_trans (by norm_num) psum1016o2_428
  · exact le_trans (by norm_num) psum1016o2_429
  · exact le_trans (by norm_num) psum1016o2_430
  · exact le_trans (by norm_num) psum1016o2_431
  · exact le_trans (by norm_num) psum1016o2_432
  · exact le_trans (by norm_num) psum1016o2_433
  · exact le_trans (by norm_num) psum1016o2_434
  · exact le_trans (by norm_num) psum1016o2_435
  · exact le_trans (by norm_num) psum1016o2_436
  · exact le_trans (by norm_num) psum1016o2_437
  · exact le_trans (by norm_num) psum1016o2_438
  · exact le_trans (by norm_num) psum1016o2_439
  · exact le_trans (by norm_num) psum1016o2_440
  · exact le_trans (by norm_num) psum1016o2_441
  · exact le_trans (by norm_num) psum1016o2_442
  · exact le_trans (by norm_num) psum1016o2_443
  · exact le_trans (by norm_num) psum1016o2_444
  · exact le_trans (by norm_num) psum1016o2_445
  · exact le_trans (by norm_num) psum1016o2_446
  · exact le_trans (by norm_num) psum1016o2_447
  · exact le_trans (by norm_num) psum1016o2_448
  · exact le_trans (by norm_num) psum1016o2_449
  · exact le_trans (by norm_num) psum1016o2_450
  · exact le_trans (by norm_num) psum1016o2_451
  · exact le_trans (by norm_num) psum1016o2_452
  · exact le_trans (by norm_num) psum1016o2_453
  · exact le_trans (by norm_num) psum1016o2_454
  · exact le_trans (by norm_num) psum1016o2_455
  · exact le_trans (by norm_num) psum1016o2_456
  · exact le_trans (by norm_num) psum1016o2_457
  · exact le_trans (by norm_num) psum1016o2_458
  · exact le_trans (by norm_num) psum1016o2_459
  · exact le_trans (by norm_num) psum1016o2_460
  · exact le_trans (by norm_num) psum1016o2_461
  · exact le_trans (by norm_num) psum1016o2_462
  · exact le_trans (by norm_num) psum1016o2_463
  · exact le_trans (by norm_num) psum1016o2_464
  · exact le_trans (by norm_num) psum1016o2_465
  · exact le_trans (by norm_num) psum1016o2_466
  · exact le_trans (by norm_num) psum1016o2_467
  · exact le_trans (by norm_num) psum1016o2_468
  · exact le_trans (by norm_num) psum1016o2_469
  · exact le_trans (by norm_num) psum1016o2_470
  · exact le_trans (by norm_num) psum1016o2_471
  · exact le_trans (by norm_num) psum1016o2_472
  · exact le_trans (by norm_num) psum1016o2_473
  · exact le_trans (by norm_num) psum1016o2_474
  · exact le_trans (by norm_num) psum1016o2_475
  · exact le_trans (by norm_num) psum1016o2_476
  · exact le_trans (by norm_num) psum1016o2_477
  · exact le_trans (by norm_num) psum1016o2_478
  · exact le_trans (by norm_num) psum1016o2_479
  · exact le_trans (by norm_num) psum1016o2_480
  · exact le_trans (by norm_num) psum1016o2_481
  · exact le_trans (by norm_num) psum1016o2_482
  · exact le_trans (by norm_num) psum1016o2_483
  · exact le_trans (by norm_num) psum1016o2_484
  · exact le_trans (by norm_num) psum1016o2_485
  · exact le_trans (by norm_num) psum1016o2_486
  · exact le_trans (by norm_num) psum1016o2_487
  · exact le_trans (by norm_num) psum1016o2_488
  · exact le_trans (by norm_num) psum1016o2_489
  · exact le_trans (by norm_num) psum1016o2_490
  · exact le_trans (by norm_num) psum1016o2_491
  · exact le_trans (by norm_num) psum1016o2_492
  · exact le_trans (by norm_num) psum1016o2_493
  · exact le_trans (by norm_num) psum1016o2_494
  · exact le_trans (by norm_num) psum1016o2_495
  · exact le_trans (by norm_num) psum1016o2_496
  · exact le_trans (by norm_num) psum1016o2_497
  · exact le_trans (by norm_num) psum1016o2_498
  · exact le_trans (by norm_num) psum1016o2_499
  · exact le_trans (by norm_num) psum1016o2_500
  · exact le_trans (by norm_num) psum1016o2_501
  · exact le_trans (by norm_num) psum1016o2_502
  · exact le_trans (by norm_num) psum1016o2_503
  · exact le_trans (by norm_num) psum1016o2_504
  · exact le_trans (by norm_num) psum1016o2_505
  · exact le_trans (by norm_num) psum1016o2_506
  · exact le_trans (by norm_num) psum1016o2_507
  · exact le_trans (by norm_num) psum1016o2_508
  · exact le_trans (by norm_num) psum1016o2_509
  · exact le_trans (by norm_num) psum1016o2_510
  · exact le_trans (by norm_num) psum1016o2_511
  · exact le_trans (by norm_num) psum1016o2_512
  · exact le_trans (by norm_num) psum1016o2_513
  · exact le_trans (by norm_num) psum1016o2_514
  · exact le_trans (by norm_num) psum1016o2_515
  · exact le_trans (by norm_num) psum1016o2_516
  · exact le_trans (by norm_num) psum1016o2_517
  · exact le_trans (by norm_num) psum1016o2_518
  · exact le_trans (by norm_num) psum1016o2_519
  · exact le_trans (by norm_num) psum1016o2_520
  · exact le_trans (by norm_num) psum1016o2_521
  · exact le_trans (by norm_num) psum1016o2_522
  · exact le_trans (by norm_num) psum1016o2_523
  · exact le_trans (by norm_num) psum1016o2_524
  · exact le_trans (by norm_num) psum1016o2_525
  · exact le_trans (by norm_num) psum1016o2_526
  · exact le_trans (by norm_num) psum1016o2_527
  · exact le_trans (by norm_num) psum1016o2_528
  · exact le_trans (by norm_num) psum1016o2_529
  · exact le_trans (by norm_num) psum1016o2_530
  · exact le_trans (by norm_num) psum1016o2_531
  · exact le_trans (by norm_num) psum1016o2_532
  · exact le_trans (by norm_num) psum1016o2_533
  · exact le_trans (by norm_num) psum1016o2_534
  · exact le_trans (by norm_num) psum1016o2_535
  · exact le_trans (by norm_num) psum1016o2_536
  · exact le_trans (by norm_num) psum1016o2_537
  · exact le_trans (by norm_num) psum1016o2_538
  · exact le_trans (by norm_num) psum1016o2_539
  · exact le_trans (by norm_num) psum1016o2_540
  · exact le_trans (by norm_num) psum1016o2_541
  · exact le_trans (by norm_num) psum1016o2_542
  · exact le_trans (by norm_num) psum1016o2_543
  · exact le_trans (by norm_num) psum1016o2_544
  · exact le_trans (by norm_num) psum1016o2_545
  · exact le_trans (by norm_num) psum1016o2_546
  · exact le_trans (by norm_num) psum1016o2_547
  · exact le_trans (by norm_num) psum1016o2_548
  · exact le_trans (by norm_num) psum1016o2_549
  · exact le_trans (by norm_num) psum1016o2_550
  · exact le_trans (by norm_num) psum1016o2_551
  · exact le_trans (by norm_num) psum1016o2_552
  · exact le_trans (by norm_num) psum1016o2_553
  · exact le_trans (by norm_num) psum1016o2_554
  · exact le_trans (by norm_num) psum1016o2_555
  · exact le_trans (by norm_num) psum1016o2_556
  · exact le_trans (by norm_num) psum1016o2_557
  · exact le_trans (by norm_num) psum1016o2_558
  · exact le_trans (by norm_num) psum1016o2_559
  · exact le_trans (by norm_num) psum1016o2_560
  · exact le_trans (by norm_num) psum1016o2_561
  · exact le_trans (by norm_num) psum1016o2_562
  · exact le_trans (by norm_num) psum1016o2_563
  · exact le_trans (by norm_num) psum1016o2_564
  · exact le_trans (by norm_num) psum1016o2_565
  · exact le_trans (by norm_num) psum1016o2_566
  · exact le_trans (by norm_num) psum1016o2_567
  · exact le_trans (by norm_num) psum1016o2_568
  · exact le_trans (by norm_num) psum1016o2_569
  · exact le_trans (by norm_num) psum1016o2_570
  · exact le_trans (by norm_num) psum1016o2_571
  · exact le_trans (by norm_num) psum1016o2_572
  · exact le_trans (by norm_num) psum1016o2_573
  · exact le_trans (by norm_num) psum1016o2_574
  · exact le_trans (by norm_num) psum1016o2_575
  · exact le_trans (by norm_num) psum1016o2_576
  · exact le_trans (by norm_num) psum1016o2_577
  · exact le_trans (by norm_num) psum1016o2_578
  · exact le_trans (by norm_num) psum1016o2_579
  · exact le_trans (by norm_num) psum1016o2_580
  · exact le_trans (by norm_num) psum1016o2_581
  · exact le_trans (by norm_num) psum1016o2_582
  · exact le_trans (by norm_num) psum1016o2_583
  · exact le_trans (by norm_num) psum1016o2_584
  · exact le_trans (by norm_num) psum1016o2_585
  · exact le_trans (by norm_num) psum1016o2_586
  · exact le_trans (by norm_num) psum1016o2_587
  · exact le_trans (by norm_num) psum1016o2_588
  · exact le_trans (by norm_num) psum1016o2_589
  · exact le_trans (by norm_num) psum1016o2_590
  · exact le_trans (by norm_num) psum1016o2_591
  · exact le_trans (by norm_num) psum1016o2_592
  · exact le_trans (by norm_num) psum1016o2_593
  · exact le_trans (by norm_num) psum1016o2_594
  · exact le_trans (by norm_num) psum1016o2_595
  · exact le_trans (by norm_num) psum1016o2_596
  · exact le_trans (by norm_num) psum1016o2_597
  · exact le_trans (by norm_num) psum1016o2_598
  · exact le_trans (by norm_num) psum1016o2_599
  · exact le_trans (by norm_num) psum1016o2_600
  · exact le_trans (by norm_num) psum1016o2_601
  · exact le_trans (by norm_num) psum1016o2_602
  · exact le_trans (by norm_num) psum1016o2_603
  · exact le_trans (by norm_num) psum1016o2_604
  · exact le_trans (by norm_num) psum1016o2_605
  · exact le_trans (by norm_num) psum1016o2_606
  · exact le_trans (by norm_num) psum1016o2_607
  · exact le_trans (by norm_num) psum1016o2_608
  · exact le_trans (by norm_num) psum1016o2_609
  · exact le_trans (by norm_num) psum1016o2_610
  · exact le_trans (by norm_num) psum1016o2_611
  · exact le_trans (by norm_num) psum1016o2_612
  · exact le_trans (by norm_num) psum1016o2_613
  · exact le_trans (by norm_num) psum1016o2_614
  · exact le_trans (by norm_num) psum1016o2_615
  · exact le_trans (by norm_num) psum1016o2_616
  · exact le_trans (by norm_num) psum1016o2_617
  · exact le_trans (by norm_num) psum1016o2_618
  · exact le_trans (by norm_num) psum1016o2_619
  · exact le_trans (by norm_num) psum1016o2_620
  · exact le_trans (by norm_num) psum1016o2_621
  · exact le_trans (by norm_num) psum1016o2_622
  · exact le_trans (by norm_num) psum1016o2_623
  · exact le_trans (by norm_num) psum1016o2_624
  · exact le_trans (by norm_num) psum1016o2_625
  · exact le_trans (by norm_num) psum1016o2_626
  · exact le_trans (by norm_num) psum1016o2_627
  · exact le_trans (by norm_num) psum1016o2_628
  · exact le_trans (by norm_num) psum1016o2_629
  · exact le_trans (by norm_num) psum1016o2_630
  · exact le_trans (by norm_num) psum1016o2_631
  · exact le_trans (by norm_num) psum1016o2_632
  · exact le_trans (by norm_num) psum1016o2_633
  · exact le_trans (by norm_num) psum1016o2_634
  · exact le_trans (by norm_num) psum1016o2_635
  · exact le_trans (by norm_num) psum1016o2_636
  · exact le_trans (by norm_num) psum1016o2_637
  · exact le_trans (by norm_num) psum1016o2_638
  · exact le_trans (by norm_num) psum1016o2_639
  · exact le_trans (by norm_num) psum1016o2_640
  · exact le_trans (by norm_num) psum1016o2_641
  · exact le_trans (by norm_num) psum1016o2_642
  · exact le_trans (by norm_num) psum1016o2_643
  · exact le_trans (by norm_num) psum1016o2_644
  · exact le_trans (by norm_num) psum1016o2_645
  · exact le_trans (by norm_num) psum1016o2_646
  · exact le_trans (by norm_num) psum1016o2_647
  · exact le_trans (by norm_num) psum1016o2_648
  · exact le_trans (by norm_num) psum1016o2_649
  · exact le_trans (by norm_num) psum1016o2_650
  · exact le_trans (by norm_num) psum1016o2_651
  · exact le_trans (by norm_num) psum1016o2_652
  · exact le_trans (by norm_num) psum1016o2_653
  · exact le_trans (by norm_num) psum1016o2_654
  · exact le_trans (by norm_num) psum1016o2_655
  · exact le_trans (by norm_num) psum1016o2_656
  · exact le_trans (by norm_num) psum1016o2_657
  · exact le_trans (by norm_num) psum1016o2_658
  · exact le_trans (by norm_num) psum1016o2_659
  · exact le_trans (by norm_num) psum1016o2_660
  · exact le_trans (by norm_num) psum1016o2_661
  · exact le_trans (by norm_num) psum1016o2_662
  · exact le_trans (by norm_num) psum1016o2_663
  · exact le_trans (by norm_num) psum1016o2_664
  · exact le_trans (by norm_num) psum1016o2_665
  · exact le_trans (by norm_num) psum1016o2_666
  · exact le_trans (by norm_num) psum1016o2_667
  · exact le_trans (by norm_num) psum1016o2_668
  · exact le_trans (by norm_num) psum1016o2_669
  · exact le_trans (by norm_num) psum1016o2_670
  · exact le_trans (by norm_num) psum1016o2_671
  · exact le_trans (by norm_num) psum1016o2_672
  · exact le_trans (by norm_num) psum1016o2_673
  · exact le_trans (by norm_num) psum1016o2_674
  · exact le_trans (by norm_num) psum1016o2_675
  · exact le_trans (by norm_num) psum1016o2_676
  · exact le_trans (by norm_num) psum1016o2_677
  · exact le_trans (by norm_num) psum1016o2_678
  · exact le_trans (by norm_num) psum1016o2_679
  · exact le_trans (by norm_num) psum1016o2_680
  · exact le_trans (by norm_num) psum1016o2_681
  · exact le_trans (by norm_num) psum1016o2_682
  · exact le_trans (by norm_num) psum1016o2_683
  · exact le_trans (by norm_num) psum1016o2_684
  · exact le_trans (by norm_num) psum1016o2_685
  · exact le_trans (by norm_num) psum1016o2_686
  · exact le_trans (by norm_num) psum1016o2_687
  · exact le_trans (by norm_num) psum1016o2_688
  · exact le_trans (by norm_num) psum1016o2_689
  · exact le_trans (by norm_num) psum1016o2_690
  · exact le_trans (by norm_num) psum1016o2_691
  · exact le_trans (by norm_num) psum1016o2_692
  · exact le_trans (by norm_num) psum1016o2_693
  · exact le_trans (by norm_num) psum1016o2_694
  · exact le_trans (by norm_num) psum1016o2_695
  · exact le_trans (by norm_num) psum1016o2_696
  · exact le_trans (by norm_num) psum1016o2_697
  · exact le_trans (by norm_num) psum1016o2_698
  · exact le_trans (by norm_num) psum1016o2_699
  · exact le_trans (by norm_num) psum1016o2_700
  · exact le_trans (by norm_num) psum1016o2_701
  · exact le_trans (by norm_num) psum1016o2_702
  · exact le_trans (by norm_num) psum1016o2_703
  · exact le_trans (by norm_num) psum1016o2_704
  · exact le_trans (by norm_num) psum1016o2_705
  · exact le_trans (by norm_num) psum1016o2_706
  · exact le_trans (by norm_num) psum1016o2_707
  · exact le_trans (by norm_num) psum1016o2_708
  · exact le_trans (by norm_num) psum1016o2_709
  · exact le_trans (by norm_num) psum1016o2_710
  · exact le_trans (by norm_num) psum1016o2_711
  · exact le_trans (by norm_num) psum1016o2_712
  · exact le_trans (by norm_num) psum1016o2_713
  · exact le_trans (by norm_num) psum1016o2_714
  · exact le_trans (by norm_num) psum1016o2_715
  · exact le_trans (by norm_num) psum1016o2_716
  · exact le_trans (by norm_num) psum1016o2_717
  · exact le_trans (by norm_num) psum1016o2_718
  · exact le_trans (by norm_num) psum1016o2_719
  · exact le_trans (by norm_num) psum1016o2_720
  · exact le_trans (by norm_num) psum1016o2_721
  · exact le_trans (by norm_num) psum1016o2_722
  · exact le_trans (by norm_num) psum1016o2_723
  · exact le_trans (by norm_num) psum1016o2_724
  · exact le_trans (by norm_num) psum1016o2_725
  · exact le_trans (by norm_num) psum1016o2_726
  · exact le_trans (by norm_num) psum1016o2_727
  · exact le_trans (by norm_num) psum1016o2_728
  · exact le_trans (by norm_num) psum1016o2_729
  · exact le_trans (by norm_num) psum1016o2_730
  · exact le_trans (by norm_num) psum1016o2_731
  · exact le_trans (by norm_num) psum1016o2_732
  · exact le_trans (by norm_num) psum1016o2_733
  · exact le_trans (by norm_num) psum1016o2_734
  · exact le_trans (by norm_num) psum1016o2_735
  · exact le_trans (by norm_num) psum1016o2_736
  · exact le_trans (by norm_num) psum1016o2_737
  · exact le_trans (by norm_num) psum1016o2_738
  · exact le_trans (by norm_num) psum1016o2_739
  · exact le_trans (by norm_num) psum1016o2_740
  · exact le_trans (by norm_num) psum1016o2_741
  · exact le_trans (by norm_num) psum1016o2_742
  · exact le_trans (by norm_num) psum1016o2_743
  · exact le_trans (by norm_num) psum1016o2_744
  · exact le_trans (by norm_num) psum1016o2_745
  · exact le_trans (by norm_num) psum1016o2_746
  · exact le_trans (by norm_num) psum1016o2_747
  · exact le_trans (by norm_num) psum1016o2_748
  · exact le_trans (by norm_num) psum1016o2_749
  · exact le_trans (by norm_num) psum1016o2_750
  · exact le_trans (by norm_num) psum1016o2_751
  · exact le_trans (by norm_num) psum1016o2_752
  · exact le_trans (by norm_num) psum1016o2_753
  · exact le_trans (by norm_num) psum1016o2_754
  · exact le_trans (by norm_num) psum1016o2_755
  · exact le_trans (by norm_num) psum1016o2_756
  · exact le_trans (by norm_num) psum1016o2_757
  · exact le_trans (by norm_num) psum1016o2_758
  · exact le_trans (by norm_num) psum1016o2_759
  · exact le_trans (by norm_num) psum1016o2_760
  · exact le_trans (by norm_num) psum1016o2_761
  · exact le_trans (by norm_num) psum1016o2_762
  · exact le_trans (by norm_num) psum1016o2_763
  · exact le_trans (by norm_num) psum1016o2_764
  · exact le_trans (by norm_num) psum1016o2_765
  · exact le_trans (by norm_num) psum1016o2_766
  · exact le_trans (by norm_num) psum1016o2_767
  · exact le_trans (by norm_num) psum1016o2_768
  · exact le_trans (by norm_num) psum1016o2_769
  · exact le_trans (by norm_num) psum1016o2_770
  · exact le_trans (by norm_num) psum1016o2_771
  · exact le_trans (by norm_num) psum1016o2_772
  · exact le_trans (by norm_num) psum1016o2_773
  · exact le_trans (by norm_num) psum1016o2_774
  · exact le_trans (by norm_num) psum1016o2_775
  · exact le_trans (by norm_num) psum1016o2_776
  · exact le_trans (by norm_num) psum1016o2_777
  · exact le_trans (by norm_num) psum1016o2_778
  · exact le_trans (by norm_num) psum1016o2_779
  · exact le_trans (by norm_num) psum1016o2_780
  · exact le_trans (by norm_num) psum1016o2_781
  · exact le_trans (by norm_num) psum1016o2_782
  · exact le_trans (by norm_num) psum1016o2_783
  · exact le_trans (by norm_num) psum1016o2_784
  · exact le_trans (by norm_num) psum1016o2_785
  · exact le_trans (by norm_num) psum1016o2_786
  · exact le_trans (by norm_num) psum1016o2_787
  · exact le_trans (by norm_num) psum1016o2_788
  · exact le_trans (by norm_num) psum1016o2_789
  · exact le_trans (by norm_num) psum1016o2_790
  · exact le_trans (by norm_num) psum1016o2_791
  · exact le_trans (by norm_num) psum1016o2_792
  · exact le_trans (by norm_num) psum1016o2_793
  · exact le_trans (by norm_num) psum1016o2_794
  · exact le_trans (by norm_num) psum1016o2_795
  · exact le_trans (by norm_num) psum1016o2_796
  · exact le_trans (by norm_num) psum1016o2_797
  · exact le_trans (by norm_num) psum1016o2_798
  · exact le_trans (by norm_num) psum1016o2_799
  · exact le_trans (by norm_num) psum1016o2_800
  · exact le_trans (by norm_num) psum1016o2_801
  · exact le_trans (by norm_num) psum1016o2_802
  · exact le_trans (by norm_num) psum1016o2_803
  · exact le_trans (by norm_num) psum1016o2_804
  · exact le_trans (by norm_num) psum1016o2_805
  · exact le_trans (by norm_num) psum1016o2_806
  · exact le_trans (by norm_num) psum1016o2_807
  · exact le_trans (by norm_num) psum1016o2_808
  · exact le_trans (by norm_num) psum1016o2_809
  · exact le_trans (by norm_num) psum1016o2_810
  · exact le_trans (by norm_num) psum1016o2_811
  · exact le_trans (by norm_num) psum1016o2_812
  · exact le_trans (by norm_num) psum1016o2_813
  · exact le_trans (by norm_num) psum1016o2_814
  · exact le_trans (by norm_num) psum1016o2_815
  · exact le_trans (by norm_num) psum1016o2_816
  · exact le_trans (by norm_num) psum1016o2_817
  · exact le_trans (by norm_num) psum1016o2_818
  · exact le_trans (by norm_num) psum1016o2_819
  · exact le_trans (by norm_num) psum1016o2_820
  · exact le_trans (by norm_num) psum1016o2_821
  · exact le_trans (by norm_num) psum1016o2_822
  · exact le_trans (by norm_num) psum1016o2_823
  · exact le_trans (by norm_num) psum1016o2_824
  · exact le_trans (by norm_num) psum1016o2_825
  · exact le_trans (by norm_num) psum1016o2_826
  · exact le_trans (by norm_num) psum1016o2_827
  · exact le_trans (by norm_num) psum1016o2_828
  · exact le_trans (by norm_num) psum1016o2_829
  · exact le_trans (by norm_num) psum1016o2_830
  · exact le_trans (by norm_num) psum1016o2_831
  · exact le_trans (by norm_num) psum1016o2_832
  · exact le_trans (by norm_num) psum1016o2_833
  · exact le_trans (by norm_num) psum1016o2_834
  · exact le_trans (by norm_num) psum1016o2_835
  · exact le_trans (by norm_num) psum1016o2_836
  · exact le_trans (by norm_num) psum1016o2_837
  · exact le_trans (by norm_num) psum1016o2_838
  · exact le_trans (by norm_num) psum1016o2_839
  · exact le_trans (by norm_num) psum1016o2_840
  · exact le_trans (by norm_num) psum1016o2_841
  · exact le_trans (by norm_num) psum1016o2_842
  · exact le_trans (by norm_num) psum1016o2_843
  · exact le_trans (by norm_num) psum1016o2_844
  · exact le_trans (by norm_num) psum1016o2_845
  · exact le_trans (by norm_num) psum1016o2_846
  · exact le_trans (by norm_num) psum1016o2_847
  · exact le_trans (by norm_num) psum1016o2_848
  · exact le_trans (by norm_num) psum1016o2_849
  · exact le_trans (by norm_num) psum1016o2_850
  · exact le_trans (by norm_num) psum1016o2_851
  · exact le_trans (by norm_num) psum1016o2_852
  · exact le_trans (by norm_num) psum1016o2_853
  · exact le_trans (by norm_num) psum1016o2_854
  · exact le_trans (by norm_num) psum1016o2_855
  · exact le_trans (by norm_num) psum1016o2_856
  · exact le_trans (by norm_num) psum1016o2_857
  · exact le_trans (by norm_num) psum1016o2_858
  · exact le_trans (by norm_num) psum1016o2_859
  · exact le_trans (by norm_num) psum1016o2_860
  · exact le_trans (by norm_num) psum1016o2_861
  · exact le_trans (by norm_num) psum1016o2_862
  · exact le_trans (by norm_num) psum1016o2_863
  · exact le_trans (by norm_num) psum1016o2_864
  · exact le_trans (by norm_num) psum1016o2_865
  · exact le_trans (by norm_num) psum1016o2_866
  · exact le_trans (by norm_num) psum1016o2_867
  · exact le_trans (by norm_num) psum1016o2_868
  · exact le_trans (by norm_num) psum1016o2_869
  · exact le_trans (by norm_num) psum1016o2_870
  · exact le_trans (by norm_num) psum1016o2_871
  · exact le_trans (by norm_num) psum1016o2_872
  · exact le_trans (by norm_num) psum1016o2_873
  · exact le_trans (by norm_num) psum1016o2_874
  · exact le_trans (by norm_num) psum1016o2_875
  · exact le_trans (by norm_num) psum1016o2_876
  · exact le_trans (by norm_num) psum1016o2_877
  · exact le_trans (by norm_num) psum1016o2_878
  · exact le_trans (by norm_num) psum1016o2_879
  · exact le_trans (by norm_num) psum1016o2_880
  · exact le_trans (by norm_num) psum1016o2_881
  · exact le_trans (by norm_num) psum1016o2_882
  · exact le_trans (by norm_num) psum1016o2_883
  · exact le_trans (by norm_num) psum1016o2_884
  · exact le_trans (by norm_num) psum1016o2_885
  · exact le_trans (by norm_num) psum1016o2_886
  · exact le_trans (by norm_num) psum1016o2_887
  · exact le_trans (by norm_num) psum1016o2_888
  · exact le_trans (by norm_num) psum1016o2_889
  · exact le_trans (by norm_num) psum1016o2_890
  · exact le_trans (by norm_num) psum1016o2_891
  · exact le_trans (by norm_num) psum1016o2_892
  · exact le_trans (by norm_num) psum1016o2_893
  · exact le_trans (by norm_num) psum1016o2_894
  · exact le_trans (by norm_num) psum1016o2_895
  · exact le_trans (by norm_num) psum1016o2_896
  · exact le_trans (by norm_num) psum1016o2_897
  · exact le_trans (by norm_num) psum1016o2_898
  · exact le_trans (by norm_num) psum1016o2_899
  · exact le_trans (by norm_num) psum1016o2_900
  · exact le_trans (by norm_num) psum1016o2_901
  · exact le_trans (by norm_num) psum1016o2_902
  · exact le_trans (by norm_num) psum1016o2_903
  · exact le_trans (by norm_num) psum1016o2_904
  · exact le_trans (by norm_num) psum1016o2_905
  · exact le_trans (by norm_num) psum1016o2_906
  · exact le_trans (by norm_num) psum1016o2_907
  · exact le_trans (by norm_num) psum1016o2_908
  · exact le_trans (by norm_num) psum1016o2_909
  · exact le_trans (by norm_num) psum1016o2_910
  · exact le_trans (by norm_num) psum1016o2_911
  · exact le_trans (by norm_num) psum1016o2_912
  · exact le_trans (by norm_num) psum1016o2_913
  · exact le_trans (by norm_num) psum1016o2_914
  · exact le_trans (by norm_num) psum1016o2_915
  · exact le_trans (by norm_num) psum1016o2_916
  · exact le_trans (by norm_num) psum1016o2_917
  · exact le_trans (by norm_num) psum1016o2_918
  · exact le_trans (by norm_num) psum1016o2_919
  · exact le_trans (by norm_num) psum1016o2_920
  · exact le_trans (by norm_num) psum1016o2_921
  · exact le_trans (by norm_num) psum1016o2_922
  · exact le_trans (by norm_num) psum1016o2_923
  · exact le_trans (by norm_num) psum1016o2_924
  · exact le_trans (by norm_num) psum1016o2_925
  · exact le_trans (by norm_num) psum1016o2_926
  · exact le_trans (by norm_num) psum1016o2_927
  · exact le_trans (by norm_num) psum1016o2_928
  · exact le_trans (by norm_num) psum1016o2_929
  · exact le_trans (by norm_num) psum1016o2_930
  · exact le_trans (by norm_num) psum1016o2_931
  · exact le_trans (by norm_num) psum1016o2_932
  · exact le_trans (by norm_num) psum1016o2_933
  · exact le_trans (by norm_num) psum1016o2_934
  · exact le_trans (by norm_num) psum1016o2_935
  · exact le_trans (by norm_num) psum1016o2_936
  · exact le_trans (by norm_num) psum1016o2_937
  · exact le_trans (by norm_num) psum1016o2_938
  · exact le_trans (by norm_num) psum1016o2_939
  · exact le_trans (by norm_num) psum1016o2_940
  · exact le_trans (by norm_num) psum1016o2_941
  · exact le_trans (by norm_num) psum1016o2_942
  · exact le_trans (by norm_num) psum1016o2_943
  · exact le_trans (by norm_num) psum1016o2_944
  · exact le_trans (by norm_num) psum1016o2_945
  · exact le_trans (by norm_num) psum1016o2_946
  · exact le_trans (by norm_num) psum1016o2_947
  · exact le_trans (by norm_num) psum1016o2_948
  · exact le_trans (by norm_num) psum1016o2_949
  · exact le_trans (by norm_num) psum1016o2_950
  · exact le_trans (by norm_num) psum1016o2_951
  · exact le_trans (by norm_num) psum1016o2_952
  · exact le_trans (by norm_num) psum1016o2_953
  · exact le_trans (by norm_num) psum1016o2_954
  · exact le_trans (by norm_num) psum1016o2_955
  · exact le_trans (by norm_num) psum1016o2_956
  · exact le_trans (by norm_num) psum1016o2_957
  · exact le_trans (by norm_num) psum1016o2_958
  · exact le_trans (by norm_num) psum1016o2_959
  · exact le_trans (by norm_num) psum1016o2_960
  · exact le_trans (by norm_num) psum1016o2_961
  · exact le_trans (by norm_num) psum1016o2_962
  · exact le_trans (by norm_num) psum1016o2_963
  · exact le_trans (by norm_num) psum1016o2_964
  · exact le_trans (by norm_num) psum1016o2_965
  · exact le_trans (by norm_num) psum1016o2_966
  · exact le_trans (by norm_num) psum1016o2_967
  · exact le_trans (by norm_num) psum1016o2_968
  · exact le_trans (by norm_num) psum1016o2_969
  · exact le_trans (by norm_num) psum1016o2_970
  · exact le_trans (by norm_num) psum1016o2_971
  · exact le_trans (by norm_num) psum1016o2_972
  · exact le_trans (by norm_num) psum1016o2_973
  · exact le_trans (by norm_num) psum1016o2_974
  · exact le_trans (by norm_num) psum1016o2_975
  · exact le_trans (by norm_num) psum1016o2_976
  · exact le_trans (by norm_num) psum1016o2_977
  · exact le_trans (by norm_num) psum1016o2_978
  · exact le_trans (by norm_num) psum1016o2_979
  · exact le_trans (by norm_num) psum1016o2_980
  · exact le_trans (by norm_num) psum1016o2_981
  · exact le_trans (by norm_num) psum1016o2_982
  · exact le_trans (by norm_num) psum1016o2_983
  · exact le_trans (by norm_num) psum1016o2_984
  · exact le_trans (by norm_num) psum1016o2_985
  · exact le_trans (by norm_num) psum1016o2_986
  · exact le_trans (by norm_num) psum1016o2_987
  · exact le_trans (by norm_num) psum1016o2_988
  · exact le_trans (by norm_num) psum1016o2_989
  · exact le_trans (by norm_num) psum1016o2_990
  · exact le_trans (by norm_num) psum1016o2_991
  · exact le_trans (by norm_num) psum1016o2_992
  · exact le_trans (by norm_num) psum1016o2_993
  · exact le_trans (by norm_num) psum1016o2_994
  · exact le_trans (by norm_num) psum1016o2_995
  · exact le_trans (by norm_num) psum1016o2_996
  · exact le_trans (by norm_num) psum1016o2_997
  · exact le_trans (by norm_num) psum1016o2_998
  · exact le_trans (by norm_num) psum1016o2_999
  · exact le_trans (by norm_num) psum1016o2_1000

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum1016o2_floor
#print axioms CriticalLinePhasor.DVP.psum1016o2_1000
end AxiomAudit
