import RequestProject.DVPCos906o2Table

/-!
# The cosine partial-sum floor, `t = 906/2` (N = 500)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 906/2` segment certificate. -/
def cos906o2c (n : ℕ) : ℝ := Real.cos (((906:ℕ):ℝ) * (Real.log n / 2))

theorem psum906o2_11 : ((18383/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos906o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 11 - ((36771/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum906o2_12 : ((1298421/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos906o2c k) + cos906o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_11
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 12 - ((563201/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_13 : ((1095571/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos906o2c k) + cos906o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_12
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 13 - ((892821/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_14 : ((1037167/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos906o2c k) + cos906o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_13
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 14 - ((-29177/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_15 : ((2119387/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos906o2c k) + cos906o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_14
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 15 - ((45153/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_16 : ((1456363/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos906o2c k) + cos906o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_15
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 16 - ((793439/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_17 : ((2807771/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos906o2c k) + cos906o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_16
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 17 - ((-20971/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_18 : ((409307/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos906o2c k) + cos906o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_17
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 18 - ((-47571/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_19 : ((45589/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos906o2c k) + cos906o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_18
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 19 - ((-1783/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_20 : ((704583/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos906o2c k) + cos906o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_19
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 20 - ((124359/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_21 : ((1818277/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos906o2c k) + cos906o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_20
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 21 - ((-199991/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_22 : ((2433427/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos906o2c k) + cos906o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_21
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 22 - ((2461/4000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_23 : ((840589/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos906o2c k) + cos906o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_22
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 23 - ((929029/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_24 : ((1013127/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos906o2c k) + cos906o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_23
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 24 - ((172563/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_25 : ((1238021/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos906o2c k) + cos906o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_24
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 25 - ((224919/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_26 : ((2879767/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos906o2c k) + cos906o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_25
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 26 - ((16151/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_27 : ((1006587/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos906o2c k) + cos906o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_26
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 27 - ((-726499/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_28 : ((5079427/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos906o2c k) + cos906o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_27
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 28 - ((728/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_29 : ((5220639/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos906o2c k) + cos906o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_28
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 29 - ((2208/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_30 : ((2713911/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos906o2c k) + cos906o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_29
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 30 - ((207283/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_31 : ((910787/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos906o2c k) + cos906o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_30
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 31 - ((-873787/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_32 : ((130939/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos906o2c k) + cos906o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_31
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 32 - ((27349/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_33 : ((6087243/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos906o2c k) + cos906o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_32
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 33 - ((849783/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_34 : ((1229129/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos906o2c k) + cos906o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_33
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 34 - ((29251/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_35 : ((1132097/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos906o2c k) + cos906o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_34
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 35 - ((-24253/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_36 : ((5015037/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos906o2c k) + cos906o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_35
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 36 - ((-161337/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_37 : ((4494933/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos906o2c k) + cos906o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_36
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 37 - ((-130001/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_38 : ((1108423/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos906o2c k) + cos906o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_37
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 38 - ((-61141/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_39 : ((638327/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos906o2c k) + cos906o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_38
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 39 - ((10516/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_40 : ((3035817/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos906o2c k) + cos906o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_39
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 40 - ((482559/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_41 : ((1499219/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos906o2c k) + cos906o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_40
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 41 - ((-37329/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_42 : ((313039/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos906o2c k) + cos906o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_41
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 42 - ((-123519/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_43 : ((171233/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos906o2c k) + cos906o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_42
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 43 - ((117733/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_44 : ((744751/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos906o2c k) + cos906o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_43
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 44 - ((119663/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_45 : ((1251877/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos906o2c k) + cos906o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_44
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 45 - ((-594/625 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_46 : ((2992151/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos906o2c k) + cos906o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_45
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 46 - ((488447/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_47 : ((320181/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos906o2c k) + cos906o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_46
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 47 - ((-430653/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_48 : ((592167/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos906o2c k) + cos906o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_47
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 48 - ((399437/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_49 : ((5074897/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos906o2c k) + cos906o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_48
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 49 - ((-846673/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_50 : ((3016779/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos906o2c k) + cos906o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_49
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 50 - ((958761/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_51 : ((5047207/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos906o2c k) + cos906o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_50
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 51 - ((-986251/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_52 : ((229913/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos906o2c k) + cos906o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_51
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 52 - ((350359/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_53 : ((180227/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos906o2c k) + cos906o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_52
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 53 - ((19539/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_54 : ((987691/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos906o2c k) + cos906o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_53
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 54 - ((-828709/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_55 : ((5806851/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos906o2c k) + cos906o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_54
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 55 - ((54281/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_56 : ((1503861/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos906o2c k) + cos906o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_55
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 56 - ((208693/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_57 : ((156763/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos906o2c k) + cos906o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_56
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 57 - ((-62433/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_58 : ((4994521/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos906o2c k) + cos906o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_57
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 58 - ((-4359/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_59 : ((149643/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos906o2c k) + cos906o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_58
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 59 - ((991299/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_60 : ((3174727/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos906o2c k) + cos906o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_59
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 60 - ((181917/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_61 : ((1121987/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos906o2c k) + cos906o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_60
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 61 - ((-739419/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_62 : ((9337/2000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos906o2c k) + cos906o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_61
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 62 - ((-188267/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_63 : ((1102451/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos906o2c k) + cos906o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_62
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 63 - ((-64649/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_64 : ((2482711/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos906o2c k) + cos906o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_63
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 64 - ((277859/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_65 : ((5936337/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos906o2c k) + cos906o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_64
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 65 - ((194203/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_66 : ((3430261/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos906o2c k) + cos906o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_65
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 66 - ((184857/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_67 : ((7465747/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos906o2c k) + cos906o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_66
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 67 - ((24213/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_68 : ((960743/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos906o2c k) + cos906o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_67
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 68 - ((220297/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_69 : ((7578101/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos906o2c k) + cos906o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_68
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 69 - ((-107743/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_70 : ((724183/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos906o2c k) + cos906o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_69
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 70 - ((-336171/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_71 : ((1693817/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos906o2c k) + cos906o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_70
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 71 - ((-233231/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_72 : ((6262839/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos906o2c k) + cos906o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_71
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 72 - ((-512329/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_73 : ((2890309/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos906o2c k) + cos906o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_72
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 73 - ((-482121/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_74 : ((1351651/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos906o2c k) + cos906o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_73
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 74 - ((-186957/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_75 : ((5226781/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos906o2c k) + cos906o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_74
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 75 - ((-179723/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_76 : ((5328907/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos906o2c k) + cos906o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_75
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 76 - ((51113/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_77 : ((361017/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos906o2c k) + cos906o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_76
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 77 - ((89493/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_78 : ((3280331/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos906o2c k) + cos906o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_77
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 78 - ((78449/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_79 : ((377417/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos906o2c k) + cos906o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_78
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 79 - ((493889/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_80 : ((2114459/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos906o2c k) + cos906o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_79
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 80 - ((227399/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_81 : ((8925287/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos906o2c k) + cos906o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_80
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 81 - ((467551/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_82 : ((69513/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos906o2c k) + cos906o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_81
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 82 - ((-118031/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_83 : ((1957867/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos906o2c k) + cos906o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_82
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 83 - ((-857557/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_84 : ((688141/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos906o2c k) + cos906o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_83
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 84 - ((-474979/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_85 : ((1311279/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos906o2c k) + cos906o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_84
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 85 - ((-64983/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_86 : ((7164641/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos906o2c k) + cos906o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_85
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 86 - ((304173/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_87 : ((2039049/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos906o2c k) + cos906o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_86
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 87 - ((198331/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_88 : ((8485371/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos906o2c k) + cos906o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_87
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 88 - ((13171/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_89 : ((7748031/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos906o2c k) + cos906o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_88
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 89 - ((-18431/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_90 : ((857609/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos906o2c k) + cos906o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_89
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 90 - ((-887059/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_91 : ((7046357/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos906o2c k) + cos906o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_90
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 91 - ((37117/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_92 : ((2011229/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos906o2c k) + cos906o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_91
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 92 - ((998659/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_93 : ((4139681/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos906o2c k) + cos906o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_92
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 93 - ((117273/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_94 : ((3673347/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos906o2c k) + cos906o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_93
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 94 - ((-116571/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_95 : ((431941/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos906o2c k) + cos906o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_94
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 95 - ((-217769/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_96 : ((7797143/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos906o2c k) + cos906o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_95
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 96 - ((886187/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_97 : ((2061077/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos906o2c k) + cos906o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_96
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 97 - ((89453/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_98 : ((366109/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos906o2c k) + cos906o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_97
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 98 - ((-230507/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_99 : ((704173/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos906o2c k) + cos906o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_98
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 99 - ((-5607/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_100 : ((8033883/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos906o2c k) + cos906o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_99
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 100 - ((992253/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_101 : ((248549/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos906o2c k) + cos906o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_100
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 101 - ((-16043/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_102 : ((109489/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos906o2c k) + cos906o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_101
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 102 - ((-236543/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_103 : ((1897561/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos906o2c k) + cos906o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_102
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 103 - ((72881/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_104 : ((8165283/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos906o2c k) + cos906o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_103
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 104 - ((575139/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_105 : ((3596377/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos906o2c k) + cos906o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_104
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 105 - ((-972429/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_106 : ((7374801/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos906o2c k) + cos906o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_105
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 106 - ((182147/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_107 : ((8175613/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos906o2c k) + cos906o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_106
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 107 - ((50057/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_108 : ((45417/6250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos906o2c k) + cos906o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_107
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 108 - ((-908793/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_109 : ((7373271/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos906o2c k) + cos906o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_108
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 109 - ((106651/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_110 : ((4074673/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos906o2c k) + cos906o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_109
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 110 - ((31047/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_111 : ((1796759/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos906o2c k) + cos906o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_110
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 111 - ((-96221/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_112 : ((472007/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos906o2c k) + cos906o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_111
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 112 - ((45647/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_113 : ((4020663/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos906o2c k) + cos906o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_112
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 113 - ((244657/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_114 : ((7063171/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos906o2c k) + cos906o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_113
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 114 - ((-195611/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_115 : ((1971409/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos906o2c k) + cos906o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_114
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 115 - ((164513/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_116 : ((7701171/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos906o2c k) + cos906o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_115
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 116 - ((-36873/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_117 : ((7168663/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos906o2c k) + cos906o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_116
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 117 - ((-66551/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_118 : ((8125191/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos906o2c k) + cos906o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_117
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 118 - ((239157/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_119 : ((449907/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos906o2c k) + cos906o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_118
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 119 - ((-926579/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_120 : ((7709083/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos906o2c k) + cos906o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_119
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 120 - ((510671/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_121 : ((7790691/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos906o2c k) + cos906o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_120
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 121 - ((20427/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_122 : ((1434137/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos906o2c k) + cos906o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_121
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 122 - ((-309953/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_123 : ((8111393/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos906o2c k) + cos906o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_122
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 123 - ((117601/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_124 : ((1425513/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos906o2c k) + cos906o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_123
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 124 - ((-61483/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_125 : ((3953259/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos906o2c k) + cos906o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_124
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 125 - ((779053/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_126 : ((3746979/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos906o2c k) + cos906o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_125
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 126 - ((-20623/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_127 : ((7479593/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos906o2c k) + cos906o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_126
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 127 - ((-2853/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_128 : ((7892399/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos906o2c k) + cos906o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_127
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 128 - ((206453/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_129 : ((1433687/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos906o2c k) + cos906o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_128
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 129 - ((-90483/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_130 : ((4043731/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos906o2c k) + cos906o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_129
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 130 - ((919127/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_131 : ((7090191/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos906o2c k) + cos906o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_130
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 131 - ((-997171/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_132 : ((8064199/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos906o2c k) + cos906o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_131
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 132 - ((243527/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_133 : ((7189091/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos906o2c k) + cos906o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_132
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 133 - ((-13672/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_134 : ((197897/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos906o2c k) + cos906o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_133
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 134 - ((726889/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_135 : ((7361631/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos906o2c k) + cos906o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_134
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 135 - ((-554149/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_136 : ((7737783/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos906o2c k) + cos906o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_135
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 136 - ((94063/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_137 : ((470661/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos906o2c k) + cos906o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_136
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 137 - ((-207107/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_138 : ((1896531/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos906o2c k) + cos906o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_137
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 138 - ((1739/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_139 : ((1914871/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos906o2c k) + cos906o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_138
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 139 - ((3673/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_140 : ((7481079/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos906o2c k) + cos906o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_139
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 140 - ((-35661/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_141 : ((154797/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos906o2c k) + cos906o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_140
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 141 - ((258871/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_142 : ((463973/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos906o2c k) + cos906o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_141
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 142 - ((-158091/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_143 : ((1943721/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos906o2c k) + cos906o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_142
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 143 - ((43927/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_144 : ((3704597/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos906o2c k) + cos906o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_143
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 144 - ((-36559/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_145 : ((7768527/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos906o2c k) + cos906o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_144
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 145 - ((359433/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_146 : ((371771/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos906o2c k) + cos906o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_145
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 146 - ((-333007/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_147 : ((3860651/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos906o2c k) + cos906o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_146
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 147 - ((142991/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_148 : ((7503321/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos906o2c k) + cos906o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_147
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 148 - ((-217881/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_149 : ((953933/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos906o2c k) + cos906o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_148
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 149 - ((128243/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_150 : ((7614289/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos906o2c k) + cos906o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_149
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 150 - ((-683/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_151 : ((3749963/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos906o2c k) + cos906o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_150
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 151 - ((-114263/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_152 : ((7762689/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos906o2c k) + cos906o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_151
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 152 - ((262863/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_153 : ((3669647/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos906o2c k) + cos906o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_152
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 153 - ((-84659/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_154 : ((7926327/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos906o2c k) + cos906o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_153
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 154 - ((587133/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_155 : ((1795887/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos906o2c k) + cos906o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_154
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 155 - ((-742679/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_156 : ((8058459/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos906o2c k) + cos906o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_155
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 156 - ((875011/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_157 : ((354577/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos906o2c k) + cos906o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_156
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 157 - ((-966819/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_158 : ((1618283/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos906o2c k) + cos906o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_157
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 158 - ((39999/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_159 : ((1783311/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos906o2c k) + cos906o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_158
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 159 - ((-958071/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_160 : ((1990733/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos906o2c k) + cos906o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_159
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 160 - ((207447/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_161 : ((7350069/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos906o2c k) + cos906o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_160
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 161 - ((-612763/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_162 : ((191683/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos906o2c k) + cos906o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_161
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 162 - ((317351/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_163 : ((1924539/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos906o2c k) + cos906o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_162
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 163 - ((3867/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_164 : ((7306893/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos906o2c k) + cos906o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_163
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 164 - ((-391163/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_165 : ((1603387/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos906o2c k) + cos906o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_164
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 165 - ((355071/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_166 : ((7086939/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos906o2c k) + cos906o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_165
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 166 - ((-116237/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_167 : ((1010733/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos906o2c k) + cos906o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_166
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 167 - ((39961/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_168 : ((7199371/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos906o2c k) + cos906o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_167
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 168 - ((-886393/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_169 : ((1948387/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos906o2c k) + cos906o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_168
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 169 - ((594277/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_170 : ((762689/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos906o2c k) + cos906o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_169
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 170 - ((-83279/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_171 : ((3657363/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos906o2c k) + cos906o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_170
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 171 - ((-4876/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_172 : ((1608821/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos906o2c k) + cos906o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_171
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 172 - ((729479/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_173 : ((707213/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos906o2c k) + cos906o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_172
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 173 - ((-311/320 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_174 : ((8029439/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos906o2c k) + cos906o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_173
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 174 - ((957409/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_175 : ((3680377/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos906o2c k) + cos906o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_174
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 175 - ((-133717/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_176 : ((3765857/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos906o2c k) + cos906o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_175
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 176 - ((8553/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_177 : ((7923867/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos906o2c k) + cos906o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_176
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 177 - ((392253/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_178 : ((7086339/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos906o2c k) + cos906o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_177
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 178 - ((-209357/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_179 : ((4042957/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos906o2c k) + cos906o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_178
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 179 - ((39987/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_180 : ((364289/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos906o2c k) + cos906o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_179
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 180 - ((-400017/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_181 : ((7576869/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos906o2c k) + cos906o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_180
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 181 - ((291189/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_182 : ((1979981/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos906o2c k) + cos906o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_181
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 182 - ((68631/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_183 : ((7073177/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos906o2c k) + cos906o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_182
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 183 - ((-846647/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_184 : ((2016709/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos906o2c k) + cos906o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_183
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 184 - ((993759/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_185 : ((1473729/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos906o2c k) + cos906o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_184
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 185 - ((-698091/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_186 : ((465103/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos906o2c k) + cos906o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_185
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 186 - ((73103/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_187 : ((8038293/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos906o2c k) + cos906o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_186
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 187 - ((119349/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_188 : ((1411857/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos906o2c k) + cos906o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_187
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 188 - ((-244727/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_189 : ((3960329/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos906o2c k) + cos906o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_188
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 189 - ((861473/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_190 : ((954679/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos906o2c k) + cos906o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_189
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 190 - ((-141563/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_191 : ((1435721/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos906o2c k) + cos906o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_190
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 191 - ((-458727/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_192 : ((8128317/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos906o2c k) + cos906o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_191
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 192 - ((237453/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_193 : ((7236733/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos906o2c k) + cos906o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_192
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 193 - ((-222871/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_194 : ((7532269/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos906o2c k) + cos906o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_193
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 194 - ((73909/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_195 : ((4011227/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos906o2c k) + cos906o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_194
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 195 - ((98057/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_196 : ((704959/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos906o2c k) + cos906o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_195
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 196 - ((-243191/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_197 : ((7873523/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos906o2c k) + cos906o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_196
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 197 - ((824033/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_198 : ((387657/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos906o2c k) + cos906o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_197
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 198 - ((-120283/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_199 : ((7079569/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos906o2c k) + cos906o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_198
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 199 - ((-673471/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_200 : ((2019677/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos906o2c k) + cos906o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_199
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 200 - ((999239/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_201 : ((7473773/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos906o2c k) + cos906o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_200
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 201 - ((-120967/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_202 : ((3616077/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos906o2c k) + cos906o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_201
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 202 - ((-241519/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_203 : ((8144193/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos906o2c k) + cos906o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_202
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 203 - ((912139/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_204 : ((1815821/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos906o2c k) + cos906o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_203
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 204 - ((-880809/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_205 : ((1482751/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos906o2c k) + cos906o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_204
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 205 - ((150571/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_206 : ((2030307/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos906o2c k) + cos906o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_205
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 206 - ((707573/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_207 : ((7134409/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos906o2c k) + cos906o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_206
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 207 - ((-986719/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_208 : ((1513709/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos906o2c k) + cos906o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_207
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 208 - ((108559/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_209 : ((4032543/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos906o2c k) + cos906o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_208
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 209 - ((496641/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_210 : ((7067561/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos906o2c k) + cos906o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_209
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 210 - ((-39897/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_211 : ((47969/6250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos906o2c k) + cos906o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_210
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 211 - ((607579/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_212 : ((4007393/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos906o2c k) + cos906o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_211
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 212 - ((169923/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_213 : ((879693/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos906o2c k) + cos906o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_212
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 213 - ((-488571/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_214 : ((7730149/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos906o2c k) + cos906o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_213
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 214 - ((138541/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_215 : ((159829/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos906o2c k) + cos906o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_214
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 215 - ((261401/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_216 : ((7026739/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos906o2c k) + cos906o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_215
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 216 - ((-964611/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_217 : ((7735863/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos906o2c k) + cos906o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_216
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 217 - ((88653/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_218 : ((2000729/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos906o2c k) + cos906o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_217
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 218 - ((267153/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_219 : ((702961/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos906o2c k) + cos906o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_218
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 219 - ((-486603/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_220 : ((7692639/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos906o2c k) + cos906o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_219
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 220 - ((663129/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_221 : ((8046829/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos906o2c k) + cos906o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_220
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 221 - ((35429/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_222 : ((7053013/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos906o2c k) + cos906o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_221
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 222 - ((-248429/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_223 : ((7598701/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos906o2c k) + cos906o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_222
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 223 - ((136447/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_224 : ((811051/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos906o2c k) + cos906o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_223
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 224 - ((511909/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_225 : ((711449/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos906o2c k) + cos906o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_224
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 225 - ((-12449/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_226 : ((7455123/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos906o2c k) + cos906o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_225
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 226 - ((340733/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_227 : ((8168101/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos906o2c k) + cos906o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_226
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 227 - ((356539/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_228 : ((7236933/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos906o2c k) + cos906o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_227
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 228 - ((-232767/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_229 : ((1818767/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos906o2c k) + cos906o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_228
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 229 - ((7647/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_230 : ((8179163/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos906o2c k) + cos906o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_229
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 230 - ((180839/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_231 : ((7437227/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos906o2c k) + cos906o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_230
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 231 - ((-185459/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_232 : ((177379/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos906o2c k) + cos906o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_231
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 232 - ((-341967/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_233 : ((8094651/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos906o2c k) + cos906o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_232
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 233 - ((999591/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_234 : ((3853553/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos906o2c k) + cos906o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_233
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 234 - ((-77489/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_235 : ((872671/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos906o2c k) + cos906o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_234
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 235 - ((-362819/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_236 : ((7877683/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos906o2c k) + cos906o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_235
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 236 - ((179283/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_237 : ((1997973/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos906o2c k) + cos906o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_236
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 237 - ((114309/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_238 : ((7016333/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos906o2c k) + cos906o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_237
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 238 - ((-975459/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_239 : ((3769711/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos906o2c k) + cos906o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_238
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 239 - ((523189/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_240 : ((4091597/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos906o2c k) + cos906o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_239
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 240 - ((20121/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_241 : ((3628481/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos906o2c k) + cos906o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_240
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 241 - ((-231533/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_242 : ((7175169/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos906o2c k) + cos906o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_241
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 242 - ((-81693/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_243 : ((2037987/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos906o2c k) + cos906o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_242
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 243 - ((976879/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_244 : ((3834003/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos906o2c k) + cos906o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_243
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 244 - ((-241921/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_245 : ((3480963/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos906o2c k) + cos906o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_244
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 245 - ((-35299/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_246 : ((1958719/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos906o2c k) + cos906o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_245
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 246 - ((17461/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_247 : ((8074849/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos906o2c k) + cos906o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_246
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 247 - ((240073/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_248 : ((1414979/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos906o2c k) + cos906o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_247
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 248 - ((-499927/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_249 : ((7340741/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos906o2c k) + cos906o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_248
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 249 - ((132973/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_250 : ((8211397/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos906o2c k) + cos906o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_249
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 250 - ((217689/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_251 : ((7528461/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 251, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 251, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 250, cos906o2c k) + cos906o2c 251 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 250) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_250
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 251 - ((-170709/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_251).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_252 : ((6973013/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 252, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 252, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 251, cos906o2c k) + cos906o2c 252 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 251) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_251
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 252 - ((-138837/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_252).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_253 : ((1976713/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 253, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 253, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 252, cos906o2c k) + cos906o2c 253 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 252) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_252
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 253 - ((933939/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_253).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_254 : ((2013879/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 254, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 254, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 253, cos906o2c k) + cos906o2c 254 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 253) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_253
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 254 - ((37191/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_254).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_255 : ((7057207/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 255, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 255, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 254, cos906o2c k) + cos906o2c 255 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 254) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_254
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 255 - ((-998209/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_255).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_256 : ((457261/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 256, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 256, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 255, cos906o2c k) + cos906o2c 256 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 255) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_255
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 256 - ((259069/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_256).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_257 : ((128333/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 257, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 257, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 256, cos906o2c k) + cos906o2c 257 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 256) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_256
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 257 - ((224309/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_257).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_258 : ((7611409/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 258, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 258, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 257, cos906o2c k) + cos906o2c 258 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 257) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_257
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 258 - ((-601803/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_258).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_259 : ((693451/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 259, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 259, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 258, cos906o2c k) + cos906o2c 259 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 258) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_258
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 259 - ((-676799/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_259).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_260 : ((1944277/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 260, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 260, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 259, cos906o2c k) + cos906o2c 260 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 259) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_259
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 260 - ((421349/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_260).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_261 : ((408337/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 261, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 261, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 260, cos906o2c k) + cos906o2c 261 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 260) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_260
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 261 - ((97433/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_261).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_262 : ((3597511/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 262, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 262, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 261, cos906o2c k) + cos906o2c 262 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 261) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_261
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 262 - ((-485809/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_262).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_263 : ((1777777/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 263, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 263, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 262, cos906o2c k) + cos906o2c 263 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 262) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_262
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 263 - ((-41907/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_263).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_264 : ((810893/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 264, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 264, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 263, cos906o2c k) + cos906o2c 264 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 263) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_263
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 264 - ((498961/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_264).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_265 : ((7903959/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 265, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 265, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 264, cos906o2c k) + cos906o2c 265 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 264) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_264
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 265 - ((-204871/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_265).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_266 : ((6961693/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 266, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 266, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 265, cos906o2c k) + cos906o2c 266 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 265) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_265
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 266 - ((-471083/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_266).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_267 : ((7415153/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 267, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 267, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 266, cos906o2c k) + cos906o2c 267 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 266) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_266
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 267 - ((11339/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_267).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_268 : ((2061023/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 268, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 268, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 267, cos906o2c k) + cos906o2c 268 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 267) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_267
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 268 - ((829039/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_268).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_269 : ((1518467/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 269, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 269, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 268, cos906o2c k) + cos906o2c 269 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 268) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_268
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 269 - ((-651657/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_269).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_270 : ((43187/6250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 270, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 270, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 269, cos906o2c k) + cos906o2c 270 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 269) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_269
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 270 - ((-136463/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_270).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_271 : ((7707701/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 271, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 271, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 270, cos906o2c k) + cos906o2c 271 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 270) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_270
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 271 - ((797881/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_271).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_272 : ((8229719/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 272, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 272, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 271, cos906o2c k) + cos906o2c 272 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 271) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_271
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 272 - ((261059/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_272).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_273 : ((1833143/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 273, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 273, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 272, cos906o2c k) + cos906o2c 273 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 272) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_272
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 273 - ((-897047/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_273).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_274 : ((1393761/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 274, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 274, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 273, cos906o2c k) + cos906o2c 274 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 273) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_273
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 274 - ((-363667/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_274).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_275 : ((1585231/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 275, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 275, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 274, cos906o2c k) + cos906o2c 275 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 274) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_274
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 275 - ((19149/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_275).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_276 : ((8143563/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 276, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 276, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 275, cos906o2c k) + cos906o2c 276 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 275) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_275
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 276 - ((54377/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_276).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_277 : ((3577473/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 277, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 277, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 276, cos906o2c k) + cos906o2c 277 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 276) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_276
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 277 - ((-988517/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_277).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_278 : ((706491/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 278, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 278, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 277, cos906o2c k) + cos906o2c 278 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 277) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_277
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 278 - ((-5621/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_278).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_279 : ((8064221/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 279, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 279, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 278, cos906o2c k) + cos906o2c 279 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 278) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_278
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 279 - ((999411/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_279).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_280 : ((8048441/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 280, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 280, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 279, cos906o2c k) + cos906o2c 280 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 279) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_279
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 280 - ((-49/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_280).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_281 : ((705013/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 281, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 281, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 280, cos906o2c k) + cos906o2c 281 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 280) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_280
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 281 - ((-998211/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_281).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_282 : ((3574071/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 282, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 282, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 281, cos906o2c k) + cos906o2c 282 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 281) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_281
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 282 - ((1533/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_282).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_283 : ((8139473/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 283, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 283, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 282, cos906o2c k) + cos906o2c 283 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 282) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_282
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 283 - ((991431/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_283).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_284 : ((997739/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 284, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 284, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 283, cos906o2c k) + cos906o2c 284 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 283) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_283
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 284 - ((-157461/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_284).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_285 : ((1749473/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 285, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 285, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 284, cos906o2c k) + cos906o2c 285 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 284) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_284
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 285 - ((-12299/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_285).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_286 : ((449503/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 286, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 286, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 285, cos906o2c k) + cos906o2c 286 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 285) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_285
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 286 - ((12141/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_286).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_287 : ((1634167/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 287, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 287, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 286, cos906o2c k) + cos906o2c 287 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 286) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_286
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 287 - ((978887/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_287).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_288 : ((995201/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 288, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 288, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 287, cos906o2c k) + cos906o2c 288 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 287) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_287
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 288 - ((-209127/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_288).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_289 : ((6983493/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 289, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 289, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 288, cos906o2c k) + cos906o2c 289 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 288) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_288
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 289 - ((-195603/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_289).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_290 : ((1437211/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 290, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 290, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 289, cos906o2c k) + cos906o2c 290 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 289) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_289
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 290 - ((101331/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_290).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_291 : ((8167457/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 291, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 291, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 290, cos906o2c k) + cos906o2c 291 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 290) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_290
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 291 - ((490751/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_291).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_292 : ((1998089/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 292, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 292, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 291, cos906o2c k) + cos906o2c 292 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 291) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_291
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 292 - ((-175001/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_292).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_293 : ((218877/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 293, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 293, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 292, cos906o2c k) + cos906o2c 293 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 292) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_292
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 293 - ((-30881/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_293).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_294 : ((3565037/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 294, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 294, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 293, cos906o2c k) + cos906o2c 294 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 293) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_293
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 294 - ((12611/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_294).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_295 : ((8125573/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 295, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 295, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 294, cos906o2c k) + cos906o2c 295 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 294) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_294
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 295 - ((995599/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_295).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_296 : ((2017361/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 296, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 296, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 295, cos906o2c k) + cos906o2c 296 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 295) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_295
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 296 - ((-56029/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_296).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_297 : ((706943/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 297, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 297, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 296, cos906o2c k) + cos906o2c 297 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 296) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_296
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 297 - ((-499957/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_297).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_298 : ((1406861/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 298, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 298, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 297, cos906o2c k) + cos906o2c 298 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 297) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_297
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 298 - ((-1401/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_298).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_299 : ((1606063/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 299, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 299, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 298, cos906o2c k) + cos906o2c 299 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 298) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_298
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 299 - ((99611/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_299).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_300 : ((8176199/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 300, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 300, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 299, cos906o2c k) + cos906o2c 300 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 299) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_299
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 300 - ((2281/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_300).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_301 : ((7198029/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 301, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 301, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 300, cos906o2c k) + cos906o2c 301 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 300) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_300
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 301 - ((-97807/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_301).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_302 : ((6923403/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 302, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 302, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 301, cos906o2c k) + cos906o2c 302 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 301) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_301
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 302 - ((-137263/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_302).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_303 : ((7862207/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 303, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 303, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 302, cos906o2c k) + cos906o2c 303 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 302) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_302
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 303 - ((117363/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_303).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_304 : ((8278589/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 304, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 304, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 303, cos906o2c k) + cos906o2c 304 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 303) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_303
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 304 - ((208241/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_304).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_305 : ((3703537/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 305, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 305, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 304, cos906o2c k) + cos906o2c 305 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 304) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_304
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 305 - ((-174283/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_305).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_306 : ((1368357/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 306, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 306, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 305, cos906o2c k) + cos906o2c 306 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 305) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_305
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 306 - ((-565189/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_306).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_307 : ((3805349/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 307, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 307, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 306, cos906o2c k) + cos906o2c 307 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 306) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_306
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 307 - ((769013/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_307).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_308 : ((4160877/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 308, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 308, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 307, cos906o2c k) + cos906o2c 308 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 307) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_307
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 308 - ((177789/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_308).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_309 : ((1538999/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 309, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 309, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 308, cos906o2c k) + cos906o2c 309 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 308) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_308
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 309 - ((-626659/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_309).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_310 : ((6853051/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 310, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 310, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 309, cos906o2c k) + cos906o2c 310 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 309) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_309
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 310 - ((-210461/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_310).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_311 : ((3647681/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 311, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 311, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 310, cos906o2c k) + cos906o2c 311 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 310) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_310
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 311 - ((442411/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_311).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_312 : ((1647489/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 312, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 312, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 311, cos906o2c k) + cos906o2c 312 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 311) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_311
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 312 - ((942183/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_312).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_313 : ((1603723/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 313, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 313, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 312, cos906o2c k) + cos906o2c 313 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 312) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_312
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 313 - ((-21873/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_313).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_314 : ((1404599/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 314, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 314, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 313, cos906o2c k) + cos906o2c 314 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 313) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_313
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 314 - ((-3111/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_314).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_315 : ((6987207/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 315, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 315, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 314, cos906o2c k) + cos906o2c 315 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 314) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_314
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 315 - ((-4461/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_315).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_316 : ((7972579/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 316, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 316, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 315, cos906o2c k) + cos906o2c 316 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 315) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_315
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 316 - ((15398/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_316).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_317 : ((4138867/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 317, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 317, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 316, cos906o2c k) + cos906o2c 317 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 316) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_316
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 317 - ((61051/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_317).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_318 : ((1844759/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 318, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 318, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 317, cos906o2c k) + cos906o2c 318 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 317) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_317
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 318 - ((-449299/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_318).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_319 : ((6812067/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 319, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 319, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 318, cos906o2c k) + cos906o2c 319 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 318) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_318
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 319 - ((-566869/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_319).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_320 : ((94247/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 320, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 320, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 319, cos906o2c k) + cos906o2c 320 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 319) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_319
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 320 - ((727793/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_320).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_321 : ((2082757/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 321, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 321, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 320, cos906o2c k) + cos906o2c 321 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 320) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_320
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 321 - ((98921/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_321).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_322 : ((1571009/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 322, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 322, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 321, cos906o2c k) + cos906o2c 322 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 321) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_321
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 322 - ((-475883/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_322).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_323 : ((6908849/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 323, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 323, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 322, cos906o2c k) + cos906o2c 323 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 322) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_322
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 323 - ((-59131/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_323).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_324 : ((7067427/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 324, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 324, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 323, cos906o2c k) + cos906o2c 324 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 323) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_323
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 324 - ((79339/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_324).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_325 : ((8067207/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 325, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 325, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 324, cos906o2c k) + cos906o2c 325 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 324) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_324
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 325 - ((24997/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_325).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_326 : ((2065113/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 326, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 326, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 325, cos906o2c k) + cos906o2c 326 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 325) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_325
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 326 - ((38669/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_326).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_327 : ((7330917/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 327, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 327, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 326, cos906o2c k) + cos906o2c 327 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 326) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_326
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 327 - ((-185887/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_327).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_328 : ((6794997/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 328, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 328, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 327, cos906o2c k) + cos906o2c 328 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 327) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_327
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 328 - ((-26791/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_328).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_329 : ((940199/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 329, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 329, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 328, cos906o2c k) + cos906o2c 329 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 328) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_328
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 329 - ((145339/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_329).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_330 : ((4168407/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 330, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 330, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 329, cos906o2c k) + cos906o2c 330 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 329) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_329
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 330 - ((407661/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_330).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_331 : ((991421/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 331, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 331, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 330, cos906o2c k) + cos906o2c 331 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 330) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_330
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 331 - ((-202673/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_331).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_332 : ((1738471/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 332, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 332, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 331, cos906o2c k) + cos906o2c 332 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 331) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_331
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 332 - ((-122173/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_332).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_333 : ((3479233/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 333, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 333, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 332, cos906o2c k) + cos906o2c 333 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 332) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_332
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 333 - ((2341/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_333).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_334 : ((1587371/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 334, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 334, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 333, cos906o2c k) + cos906o2c 334 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 333) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_333
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 334 - ((978489/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_334).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_335 : ((8348439/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 335, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 335, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 334, cos906o2c k) + cos906o2c 335 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 334) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_334
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 335 - ((102921/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_335).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_336 : ((754917/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 336, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 336, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 335, cos906o2c k) + cos906o2c 336 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 335) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_335
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 336 - ((-799169/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_336).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_337 : ((1696273/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 337, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 337, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 336, cos906o2c k) + cos906o2c 337 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 336) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_336
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 337 - ((-381989/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_337).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_338 : ((7240317/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 338, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 338, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 337, cos906o2c k) + cos906o2c 338 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 337) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_337
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 338 - ((18213/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_338).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_339 : ((4105749/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 339, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 339, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 338, cos906o2c k) + cos906o2c 339 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 338) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_338
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 339 - ((971281/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_339).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_340 : ((2051911/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 340, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 340, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 339, cos906o2c k) + cos906o2c 340 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 339) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_339
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 340 - ((-1877/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_340).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_341 : ((361771/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 341, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 341, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 340, cos906o2c k) + cos906o2c 341 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 340) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_340
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 341 - ((-243031/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_341).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_342 : ((67727/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 342, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 342, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 341, cos906o2c k) + cos906o2c 342 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 341) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_341
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 342 - ((-23131/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_342).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_343 : ((7518361/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 343, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 343, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 342, cos906o2c k) + cos906o2c 343 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 342) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_342
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 343 - ((745761/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_343).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_344 : ((1669879/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 344, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 344, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 343, cos906o2c k) + cos906o2c 344 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 343) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_343
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 344 - ((415567/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_344).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_345 : ((1604327/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 345, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 345, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 344, cos906o2c k) + cos906o2c 345 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 344) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_344
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 345 - ((-16383/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_345).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_346 : ((7024283/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 346, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 346, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 345, cos906o2c k) + cos906o2c 346 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 345) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_345
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 346 - ((-249313/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_346).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_347 : ((341801/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 347, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 347, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 346, cos906o2c k) + cos906o2c 347 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 346) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_346
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 347 - ((-188163/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_347).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_348 : ((309341/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 348, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 348, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 347, cos906o2c k) + cos906o2c 348 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 347) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_347
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 348 - ((179521/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_348).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_349 : ((8398357/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 349, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 349, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 348, cos906o2c k) + cos906o2c 349 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 348) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_348
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 349 - ((166233/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_349).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_350 : ((3929851/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 350, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 350, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 349, cos906o2c k) + cos906o2c 350 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 349) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_349
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 350 - ((-107711/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_350).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_351 : ((6901467/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 351, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 351, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 350, cos906o2c k) + cos906o2c 351 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 350) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_350
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 351 - ((-191627/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_351).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_352 : ((6909689/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 352, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 352, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 351, cos906o2c k) + cos906o2c 352 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 351) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_351
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 352 - ((4161/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_352).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_353 : ((7871371/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 353, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 353, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 352, cos906o2c k) + cos906o2c 353 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 352) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_352
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 353 - ((480891/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_353).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_354 : ((840809/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 354, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 354, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 353, cos906o2c k) + cos906o2c 354 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 353) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_353
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 354 - ((536819/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_354).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_355 : ((7755277/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 355, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 355, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 354, cos906o2c k) + cos906o2c 355 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 354) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_354
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 355 - ((-652713/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_355).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_356 : ((6839921/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 356, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 356, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 355, cos906o2c k) + cos906o2c 356 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 355) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_355
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 356 - ((-114407/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_356).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_357 : ((1738523/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 357, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 357, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 356, cos906o2c k) + cos906o2c 357 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 356) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_356
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 357 - ((114271/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_357).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_358 : ((3968079/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 358, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 358, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 357, cos906o2c k) + cos906o2c 358 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 357) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_357
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 358 - ((491083/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_358).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_359 : ((841227/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 359, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 359, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 358, cos906o2c k) + cos906o2c 359 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 358) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_358
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 359 - ((119053/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_359).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_360 : ((3860261/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 360, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 360, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 359, cos906o2c k) + cos906o2c 360 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 359) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_359
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 360 - ((-10807/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_360).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_361 : ((3409889/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 361, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 361, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 360, cos906o2c k) + cos906o2c 361 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 360) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_360
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 361 - ((-225161/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_361).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_362 : ((3475591/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 362, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 362, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 361, cos906o2c k) + cos906o2c 362 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 361) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_361
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 362 - ((8219/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_362).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_363 : ((317329/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 363, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 363, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 362, cos906o2c k) + cos906o2c 363 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 362) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_362
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 363 - ((982143/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_363).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_364 : ((4212333/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 364, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 364, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 363, cos906o2c k) + cos906o2c 364 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 363) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_363
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 364 - ((491541/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_364).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_365 : ((7758481/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 365, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 365, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 364, cos906o2c k) + cos906o2c 365 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 364) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_364
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 365 - ((-133217/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_365).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_366 : ((1709093/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 366, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 366, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 365, cos906o2c k) + cos906o2c 366 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 365) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_365
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 366 - ((-922009/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_366).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_367 : ((1724751/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 367, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 367, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 366, cos906o2c k) + cos906o2c 367 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 366) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_366
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 367 - ((15683/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_367).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_368 : ((786123/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 368, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 368, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 367, cos906o2c k) + cos906o2c 368 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 367) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_367
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 368 - ((481163/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_368).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_369 : ((4219801/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 369, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 369, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 368, cos906o2c k) + cos906o2c 369 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 368) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_368
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 369 - ((72309/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_369).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_370 : ((983417/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 370, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 370, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 369, cos906o2c k) + cos906o2c 370 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 369) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_369
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 370 - ((-286083/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_370).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_371 : ((3450551/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 371, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 371, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 370, cos906o2c k) + cos906o2c 371 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 370) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_370
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 371 - ((-483067/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_371).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_372 : ((6810709/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 372, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 372, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 371, cos906o2c k) + cos906o2c 372 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 371) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_371
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 372 - ((-90293/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_372).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_373 : ((3856591/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 373, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 373, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 372, cos906o2c k) + cos906o2c 373 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 372) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_372
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 373 - ((902573/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_373).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_374 : ((2108143/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 374, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 374, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 373, cos906o2c k) + cos906o2c 374 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 373) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_373
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 374 - ((71949/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_374).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_375 : ((8037003/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 375, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 375, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 374, cos906o2c k) + cos906o2c 375 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 374) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_374
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 375 - ((-395469/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_375).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_376 : ((219931/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 376, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 376, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 375, cos906o2c k) + cos906o2c 376 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 375) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_375
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 376 - ((-999111/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_376).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_377 : ((1343589/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 377, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 377, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 376, cos906o2c k) + cos906o2c 377 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 376) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_376
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 377 - ((-319747/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_377).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_378 : ((748509/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 378, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 378, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 377, cos906o2c k) + cos906o2c 378 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 377) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_377
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 378 - ((153449/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_378).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_379 : ((209057/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 379, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 379, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 378, cos906o2c k) + cos906o2c 379 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 378) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_378
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 379 - ((87729/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_379).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_380 : ((329561/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 380, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 380, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 379, cos906o2c k) + cos906o2c 380 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 379) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_379
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 380 - ((-24631/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_380).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_381 : ((7271717/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 381, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 381, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 380, cos906o2c k) + cos906o2c 381 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 380) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_380
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 381 - ((-120901/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_381).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_382 : ((104286/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 382, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 382, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 381, cos906o2c k) + cos906o2c 382 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 381) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_381
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 382 - ((-597313/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_382).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_383 : ((179797/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 383, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 383, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 382, cos906o2c k) + cos906o2c 383 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 382) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_382
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 383 - ((129419/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_383).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_384 : ((8179857/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 384, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 384, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 383, cos906o2c k) + cos906o2c 384 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 383) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_383
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 384 - ((988077/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_384).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_385 : ((841557/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 385, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 385, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 384, cos906o2c k) + cos906o2c 385 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 384) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_384
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 385 - ((235813/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_385).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_386 : ((7609669/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 386, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 386, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 385, cos906o2c k) + cos906o2c 386 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 385) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_385
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 386 - ((-805801/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_386).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_387 : ((105484/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 387, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 387, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 386, cos906o2c k) + cos906o2c 387 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 386) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_386
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 387 - ((-858593/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_387).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_388 : ((688699/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 388, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 388, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 387, cos906o2c k) + cos906o2c 388 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 387) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_387
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 388 - ((68057/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_388).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_389 : ((785113/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 389, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 389, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 388, cos906o2c k) + cos906o2c 389 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 388) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_388
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 389 - ((12053/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_389).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_390 : ((2119177/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 390, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 390, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 389, cos906o2c k) + cos906o2c 390 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 389) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_389
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 390 - ((312839/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_390).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_391 : ((500703/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 391, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 391, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 390, cos906o2c k) + cos906o2c 391 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 390) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_390
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 391 - ((-5817/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_391).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_392 : ((7013621/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 392, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 392, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 391, cos906o2c k) + cos906o2c 392 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 391) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_391
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 392 - ((-997527/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_392).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_393 : ((3337051/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 393, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 393, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 392, cos906o2c k) + cos906o2c 393 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 392) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_392
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 393 - ((-339419/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_393).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_394 : ((739477/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 394, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 394, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 393, cos906o2c k) + cos906o2c 394 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 393) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_393
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 394 - ((11262/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_394).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_395 : ((166449/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 395, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 395, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 394, cos906o2c k) + cos906o2c 395 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 394) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_394
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 395 - ((46389/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_395).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_396 : ((1673069/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 396, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 396, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 395, cos906o2c k) + cos906o2c 396 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 395) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_395
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 396 - ((8599/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_396).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_397 : ((1868571/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 397, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 397, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 396, cos906o2c k) + cos906o2c 397 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 396) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_396
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 397 - ((-890961/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_397).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_398 : ((6689319/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 398, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 398, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 397, cos906o2c k) + cos906o2c 398 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 397) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_397
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 398 - ((-156973/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_398).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_399 : ((3460681/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 399, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 399, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 398, cos906o2c k) + cos906o2c 399 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 398) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_398
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 399 - ((232143/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_399).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_400 : ((3950403/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 400, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 400, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 399, cos906o2c k) + cos906o2c 400 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 399) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_399
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 400 - ((122443/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_400).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_401 : ((1699951/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 401, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 401, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 400, cos906o2c k) + cos906o2c 401 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 400) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_400
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 401 - ((599049/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_401).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_402 : ((502039/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 402, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 402, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 401, cos906o2c k) + cos906o2c 402 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 401) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_401
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 402 - ((-467031/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_402).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_403 : ((7033349/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 403, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 403, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 402, cos906o2c k) + cos906o2c 403 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 402) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_402
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 403 - ((-39967/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_403).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_404 : ((165923/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 404, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 404, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 403, cos906o2c k) + cos906o2c 404 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 403) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_403
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 404 - ((-396329/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_404).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_405 : ((3645233/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 405, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 405, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 404, cos906o2c k) + cos906o2c 405 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 404) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_404
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 405 - ((326823/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_405).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_406 : ((8257079/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 406, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 406, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 405, cos906o2c k) + cos906o2c 406 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 405) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_405
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 406 - ((966713/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_406).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_407 : ((2113343/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 407, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 407, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 406, cos906o2c k) + cos906o2c 407 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 406) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_406
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 407 - ((196393/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_407).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_408 : ((7661329/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 408, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 408, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 407, cos906o2c k) + cos906o2c 408 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 407) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_407
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 408 - ((-791943/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_408).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_409 : ((6761711/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 409, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 409, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 408, cos906o2c k) + cos906o2c 409 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 408) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_408
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 409 - ((-449759/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_409).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_410 : ((6749173/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 410, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 410, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 409, cos906o2c k) + cos906o2c 410 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 409) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_409
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 410 - ((-6219/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_410).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_411 : ((1527243/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 411, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 411, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 410, cos906o2c k) + cos906o2c 411 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 410) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_410
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 411 - ((443571/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_411).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_412 : ((4224661/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 412, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 412, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 411, cos906o2c k) + cos906o2c 412 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 411) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_411
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 412 - ((813207/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_412).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_413 : ((8301247/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 413, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 413, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 412, cos906o2c k) + cos906o2c 413 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 412) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_412
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 413 - ((-5919/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_413).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_414 : ((3677027/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 414, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 414, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 413, cos906o2c k) + cos906o2c 414 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 413) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_413
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 414 - ((-947093/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_414).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_415 : ((331669/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 415, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 415, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 414, cos906o2c k) + cos906o2c 415 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 414) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_414
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 415 - ((-360287/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_415).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_416 : ((6915019/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 416, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 416, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 415, cos906o2c k) + cos906o2c 416 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 415) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_415
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 416 - ((281739/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_416).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_417 : ((493467/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 417, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 417, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 416, cos906o2c k) + cos906o2c 417 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 416) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_416
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 417 - ((980553/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_417).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_418 : ((4263367/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 418, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 418, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 417, cos906o2c k) + cos906o2c 418 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 417) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_417
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 418 - ((315681/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_418).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_419 : ((2034503/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 419, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 419, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 418, cos906o2c k) + cos906o2c 419 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 418) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_418
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 419 - ((-194311/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_419).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_420 : ((7142123/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 420, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 420, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 419, cos906o2c k) + cos906o2c 420 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 419) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_419
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 420 - ((-995789/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_420).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_421 : ((164739/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 421, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 421, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 420, cos906o2c k) + cos906o2c 421 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 420) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_420
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 421 - ((-552463/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_421).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_422 : ((7059579/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 422, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 422, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 421, cos906o2c k) + cos906o2c 422 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 421) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_421
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 422 - ((470119/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_422).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_423 : ((8059437/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 423, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 423, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 422, cos906o2c k) + cos906o2c 423 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 422) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_422
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 423 - ((499979/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_423).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_424 : ((8547809/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 424, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 424, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 423, cos906o2c k) + cos906o2c 424 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 423) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_423
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 424 - ((61059/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_424).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_425 : ((8019241/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 425, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 425, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 424, cos906o2c k) + cos906o2c 425 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 424) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_424
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 425 - ((-132117/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_425).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_426 : ((7020423/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 426, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 426, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 425, cos906o2c k) + cos906o2c 426 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 425) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_425
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 426 - ((-499359/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_426).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_427 : ((6578161/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 427, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 427, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 426, cos906o2c k) + cos906o2c 427 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 426) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_426
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 427 - ((-221081/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_427).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_428 : ((7144027/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 428, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 428, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 427, cos906o2c k) + cos906o2c 428 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 427) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_427
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 428 - ((282983/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_428).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_429 : ((1017507/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 429, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 429, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 428, cos906o2c k) + cos906o2c 429 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 428) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_428
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 429 - ((996129/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_429).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_430 : ((427753/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 430, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 430, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 429, cos906o2c k) + cos906o2c 430 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 429) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_429
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 430 - ((6486/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_430).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_431 : ((1594107/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 431, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 431, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 430, cos906o2c k) + cos906o2c 431 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 430) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_430
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 431 - ((-23377/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_431).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_432 : ((1743939/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 432, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 432, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 431, cos906o2c k) + cos906o2c 432 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 431) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_431
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 432 - ((-994679/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_432).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_433 : ((6567743/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 433, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 433, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 432, cos906o2c k) + cos906o2c 433 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 432) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_432
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 433 - ((-407913/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_433).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_434 : ((7152589/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 434, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 434, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 433, cos906o2c k) + cos906o2c 434 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 433) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_433
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 434 - ((292473/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_434).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_435 : ((8147827/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 435, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 435, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 434, cos906o2c k) + cos906o2c 435 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 434) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_434
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 435 - ((497669/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_435).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_436 : ((34273/4000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 436, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 436, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 435, cos906o2c k) + cos906o2c 436 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 435) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_435
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 436 - ((420523/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_436).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_437 : ((8000411/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 437, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 437, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 436, cos906o2c k) + cos906o2c 437 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 436) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_436
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 437 - ((-567739/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_437).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_438 : ((7002651/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 438, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 438, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 437, cos906o2c k) + cos906o2c 438 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 437) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_437
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 438 - ((-49883/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_438).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_439 : ((3275143/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 439, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 439, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 438, cos906o2c k) + cos906o2c 439 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 438) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_438
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 439 - ((-90453/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_439).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_440 : ((1416513/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 440, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 440, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 439, cos906o2c k) + cos906o2c 440 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 439) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_439
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 440 - ((532379/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_440).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_441 : ((1616457/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 441, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 441, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 440, cos906o2c k) + cos906o2c 441 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 440) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_440
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 441 - ((49991/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_441).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_442 : ((8584077/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 442, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 442, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 441, cos906o2c k) + cos906o2c 442 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 441) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_441
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 442 - ((125473/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_442).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_443 : ((8106351/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 443, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 443, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 442, cos906o2c k) + cos906o2c 443 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 442) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_442
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 443 - ((-238813/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_443).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_444 : ((7107573/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 444, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 444, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 443, cos906o2c k) + cos906o2c 444 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 443) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_443
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 444 - ((-499339/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_444).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_445 : ((408767/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 445, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 445, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 444, cos906o2c k) + cos906o2c 445 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 444) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_444
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 445 - ((-567201/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_445).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_446 : ((3471107/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 446, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 446, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 445, cos906o2c k) + cos906o2c 446 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 445) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_445
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 446 - ((201021/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_446).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_447 : ((991497/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 447, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 447, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 446, cos906o2c k) + cos906o2c 447 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 446) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_446
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 447 - ((494931/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_447).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_448 : ((171537/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 448, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 448, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 447, cos906o2c k) + cos906o2c 448 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 447) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_447
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 448 - ((322487/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_448).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_449 : ((66181/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 449, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 449, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 448, cos906o2c k) + cos906o2c 449 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 448) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_448
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 449 - ((-2433/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_449).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_450 : ((7304607/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 450, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 450, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 449, cos906o2c k) + cos906o2c 450 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 449) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_449
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 450 - ((-483959/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_450).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_451 : ((6573897/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 451, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 451, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 450, cos906o2c k) + cos906o2c 451 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 450) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_450
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 451 - ((-73061/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_451).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_452 : ((6756849/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 452, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 452, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 451, cos906o2c k) + cos906o2c 452 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 451) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_451
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 452 - ((45763/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_452).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_453 : ((7683331/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 453, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 453, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 452, cos906o2c k) + cos906o2c 453 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 452) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_452
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 453 - ((463291/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_453).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_454 : ((8500991/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 454, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 454, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 453, cos906o2c k) + cos906o2c 454 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 453) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_453
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 454 - ((5111/6250 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_454).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_455 : ((8461673/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 455, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 455, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 454, cos906o2c k) + cos906o2c 455 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 454) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_454
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 455 - ((-19609/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_455).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_456 : ((7602353/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 456, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 456, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 455, cos906o2c k) + cos906o2c 456 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 455) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_455
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 456 - ((-42961/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_456).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_457 : ((6704099/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 457, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 457, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 456, cos906o2c k) + cos906o2c 457 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 456) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_456
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 457 - ((-449077/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_457).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_458 : ((6578943/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 458, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 458, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 457, cos906o2c k) + cos906o2c 458 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 457) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_457
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 458 - ((-1954/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_458).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_459 : ((3669207/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 459, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 459, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 458, cos906o2c k) + cos906o2c 459 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 458) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_458
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 459 - ((759571/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_459).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_460 : ((8300009/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 460, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 460, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 459, cos906o2c k) + cos906o2c 460 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 459) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_459
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 460 - ((192339/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_460).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_461 : ((4302191/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 461, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 461, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 460, cos906o2c k) + cos906o2c 461 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 460) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_460
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 461 - ((304473/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_461).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_462 : ((7981593/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 462, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 462, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 461, cos906o2c k) + cos906o2c 462 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 461) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_461
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 462 - ((-622689/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_462).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_463 : ((174619/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 463, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 463, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 462, cos906o2c k) + cos906o2c 463 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 462) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_462
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 463 - ((-996733/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_463).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_464 : ((6494221/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 464, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 464, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 463, cos906o2c k) + cos906o2c 464 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 463) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_463
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 464 - ((-490439/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_464).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_465 : ((347023/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 465, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 465, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 464, cos906o2c k) + cos906o2c 465 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 464) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_464
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 465 - ((446339/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_465).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_466 : ((3965631/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 466, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 466, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 465, cos906o2c k) + cos906o2c 466 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 465) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_465
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 466 - ((495451/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_466).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_467 : ((4300777/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 467, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 467, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 466, cos906o2c k) + cos906o2c 467 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 466) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_466
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 467 - ((83799/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_467).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_468 : ((104617/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 468, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 468, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 467, cos906o2c k) + cos906o2c 468 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 467) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_467
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 468 - ((-116047/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_468).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_469 : ((3718401/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 469, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 469, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 468, cos906o2c k) + cos906o2c 469 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 468) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_468
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 469 - ((-466229/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_469).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_470 : ((6608669/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 470, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 470, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 469, cos906o2c k) + cos906o2c 470 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 469) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_469
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 470 - ((-828033/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_470).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_471 : ((3297893/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 471, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 471, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 470, cos906o2c k) + cos906o2c 471 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 470) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_470
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 471 - ((-12783/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_471).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_472 : ((7407927/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 472, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 472, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 471, cos906o2c k) + cos906o2c 472 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 471) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_471
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 472 - ((812241/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_472).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_473 : ((1670387/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 473, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 473, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 472, cos906o2c k) + cos906o2c 473 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 472) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_472
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 473 - ((236027/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_473).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_474 : ((4313203/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 474, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 474, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 473, cos906o2c k) + cos906o2c 474 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 473) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_473
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 474 - ((274571/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_474).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_475 : ((2000049/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 475, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 475, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 474, cos906o2c k) + cos906o2c 475 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 474) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_474
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 475 - ((-62611/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_475).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_476 : ((3500901/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 476, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 476, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 475, cos906o2c k) + cos906o2c 476 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 475) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_475
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 476 - ((-499147/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_476).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_477 : ((1293813/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 477, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 477, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 476, cos906o2c k) + cos906o2c 477 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 476) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_476
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 477 - ((-532637/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_477).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_478 : ((6846381/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 478, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 478, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 477, cos906o2c k) + cos906o2c 478 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 477) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_477
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 478 - ((47177/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_478).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_479 : ((7818301/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 479, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 479, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 478, cos906o2c k) + cos906o2c 479 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 478) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_478
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 479 - ((48601/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_479).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_480 : ((8578083/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 480, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 480, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 479, cos906o2c k) + cos906o2c 480 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 479) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_479
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 480 - ((379941/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_480).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_481 : ((8498461/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 481, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 481, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 480, cos906o2c k) + cos906o2c 481 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 480) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_480
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 481 - ((-39761/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_481).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_482 : ((3823011/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 482, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 482, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 481, cos906o2c k) + cos906o2c 482 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 481) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_481
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 482 - ((-852339/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_482).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_483 : ((6720439/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 483, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 483, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 482, cos906o2c k) + cos906o2c 483 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 482) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_482
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 483 - ((-925483/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_483).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_484 : ((259097/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 484, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 484, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 483, cos906o2c k) + cos906o2c 484 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 483) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_483
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 484 - ((-121457/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_484).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_485 : ((7113537/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 485, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 485, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 484, cos906o2c k) + cos906o2c 485 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 484) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_484
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 485 - ((159053/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_485).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_486 : ((2028023/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 486, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 486, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 485, cos906o2c k) + cos906o2c 486 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 485) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_485
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 486 - ((199731/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_486).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_487 : ((866651/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 487, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 487, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 486, cos906o2c k) + cos906o2c 487 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 486) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_486
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 487 - ((277259/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_487).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_488 : ((8331551/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 488, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 488, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 487, cos906o2c k) + cos906o2c 488 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 487) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_487
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 488 - ((-334859/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_488).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_489 : ((3688361/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 489, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 489, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 488, cos906o2c k) + cos906o2c 489 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 488) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_488
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 489 - ((-954729/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_489).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_490 : ((3282357/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 490, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 490, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 489, cos906o2c k) + cos906o2c 490 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 489) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_489
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 490 - ((-202977/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_490).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_491 : ((327039/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 491, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 491, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 490, cos906o2c k) + cos906o2c 491 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 490) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_490
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 491 - ((-11917/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_491).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_492 : ((7322661/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 492, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 492, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 491, cos906o2c k) + cos906o2c 492 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 491) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_491
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 492 - ((781981/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_492).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_493 : ((8292257/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 493, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 493, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 492, cos906o2c k) + cos906o2c 493 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 492) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_492
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 493 - ((30303/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_493).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_494 : ((8687117/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 494, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 494, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 493, cos906o2c k) + cos906o2c 494 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 493) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_493
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 494 - ((4937/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_494).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_495 : ((2049703/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 495, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 495, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 494, cos906o2c k) + cos906o2c 495 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 494) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_494
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 495 - ((-97641/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_495).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_496 : ((7209427/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 496, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 496, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 495, cos906o2c k) + cos906o2c 496 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 495) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_495
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 496 - ((-197857/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_496).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_497 : ((3244273/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 497, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 497, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 496, cos906o2c k) + cos906o2c 497 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 496) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_496
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 497 - ((-720781/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_497).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_498 : ((6593851/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 498, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 498, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 497, cos906o2c k) + cos906o2c 498 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 497) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_497
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 498 - ((21081/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_498).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_499 : ((930359/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 499, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 499, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 498, cos906o2c k) + cos906o2c 499 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 498) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_498
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 499 - ((849121/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_499).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum906o2_500 : ((8381997/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 500, cos906o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 500, cos906o2c k)
      = (∑ k ∈ Finset.Icc 11 499, cos906o2c k) + cos906o2c 500 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 499) (by norm_num) cos906o2c
    simpa using h
  have hprev := psum906o2_499
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos906o2c 500 - ((37569/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos906o2_br_500).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 16384 in
theorem psum906o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 500 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos906o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum906o2_11
  · exact le_trans (by norm_num) psum906o2_12
  · exact le_trans (by norm_num) psum906o2_13
  · exact le_trans (by norm_num) psum906o2_14
  · exact le_trans (by norm_num) psum906o2_15
  · exact le_trans (by norm_num) psum906o2_16
  · exact le_trans (by norm_num) psum906o2_17
  · exact le_trans (by norm_num) psum906o2_18
  · exact le_trans (by norm_num) psum906o2_19
  · exact le_trans (by norm_num) psum906o2_20
  · exact le_trans (by norm_num) psum906o2_21
  · exact le_trans (by norm_num) psum906o2_22
  · exact le_trans (by norm_num) psum906o2_23
  · exact le_trans (by norm_num) psum906o2_24
  · exact le_trans (by norm_num) psum906o2_25
  · exact le_trans (by norm_num) psum906o2_26
  · exact le_trans (by norm_num) psum906o2_27
  · exact le_trans (by norm_num) psum906o2_28
  · exact le_trans (by norm_num) psum906o2_29
  · exact le_trans (by norm_num) psum906o2_30
  · exact le_trans (by norm_num) psum906o2_31
  · exact le_trans (by norm_num) psum906o2_32
  · exact le_trans (by norm_num) psum906o2_33
  · exact le_trans (by norm_num) psum906o2_34
  · exact le_trans (by norm_num) psum906o2_35
  · exact le_trans (by norm_num) psum906o2_36
  · exact le_trans (by norm_num) psum906o2_37
  · exact le_trans (by norm_num) psum906o2_38
  · exact le_trans (by norm_num) psum906o2_39
  · exact le_trans (by norm_num) psum906o2_40
  · exact le_trans (by norm_num) psum906o2_41
  · exact le_trans (by norm_num) psum906o2_42
  · exact le_trans (by norm_num) psum906o2_43
  · exact le_trans (by norm_num) psum906o2_44
  · exact le_trans (by norm_num) psum906o2_45
  · exact le_trans (by norm_num) psum906o2_46
  · exact le_trans (by norm_num) psum906o2_47
  · exact le_trans (by norm_num) psum906o2_48
  · exact le_trans (by norm_num) psum906o2_49
  · exact le_trans (by norm_num) psum906o2_50
  · exact le_trans (by norm_num) psum906o2_51
  · exact le_trans (by norm_num) psum906o2_52
  · exact le_trans (by norm_num) psum906o2_53
  · exact le_trans (by norm_num) psum906o2_54
  · exact le_trans (by norm_num) psum906o2_55
  · exact le_trans (by norm_num) psum906o2_56
  · exact le_trans (by norm_num) psum906o2_57
  · exact le_trans (by norm_num) psum906o2_58
  · exact le_trans (by norm_num) psum906o2_59
  · exact le_trans (by norm_num) psum906o2_60
  · exact le_trans (by norm_num) psum906o2_61
  · exact le_trans (by norm_num) psum906o2_62
  · exact le_trans (by norm_num) psum906o2_63
  · exact le_trans (by norm_num) psum906o2_64
  · exact le_trans (by norm_num) psum906o2_65
  · exact le_trans (by norm_num) psum906o2_66
  · exact le_trans (by norm_num) psum906o2_67
  · exact le_trans (by norm_num) psum906o2_68
  · exact le_trans (by norm_num) psum906o2_69
  · exact le_trans (by norm_num) psum906o2_70
  · exact le_trans (by norm_num) psum906o2_71
  · exact le_trans (by norm_num) psum906o2_72
  · exact le_trans (by norm_num) psum906o2_73
  · exact le_trans (by norm_num) psum906o2_74
  · exact le_trans (by norm_num) psum906o2_75
  · exact le_trans (by norm_num) psum906o2_76
  · exact le_trans (by norm_num) psum906o2_77
  · exact le_trans (by norm_num) psum906o2_78
  · exact le_trans (by norm_num) psum906o2_79
  · exact le_trans (by norm_num) psum906o2_80
  · exact le_trans (by norm_num) psum906o2_81
  · exact le_trans (by norm_num) psum906o2_82
  · exact le_trans (by norm_num) psum906o2_83
  · exact le_trans (by norm_num) psum906o2_84
  · exact le_trans (by norm_num) psum906o2_85
  · exact le_trans (by norm_num) psum906o2_86
  · exact le_trans (by norm_num) psum906o2_87
  · exact le_trans (by norm_num) psum906o2_88
  · exact le_trans (by norm_num) psum906o2_89
  · exact le_trans (by norm_num) psum906o2_90
  · exact le_trans (by norm_num) psum906o2_91
  · exact le_trans (by norm_num) psum906o2_92
  · exact le_trans (by norm_num) psum906o2_93
  · exact le_trans (by norm_num) psum906o2_94
  · exact le_trans (by norm_num) psum906o2_95
  · exact le_trans (by norm_num) psum906o2_96
  · exact le_trans (by norm_num) psum906o2_97
  · exact le_trans (by norm_num) psum906o2_98
  · exact le_trans (by norm_num) psum906o2_99
  · exact le_trans (by norm_num) psum906o2_100
  · exact le_trans (by norm_num) psum906o2_101
  · exact le_trans (by norm_num) psum906o2_102
  · exact le_trans (by norm_num) psum906o2_103
  · exact le_trans (by norm_num) psum906o2_104
  · exact le_trans (by norm_num) psum906o2_105
  · exact le_trans (by norm_num) psum906o2_106
  · exact le_trans (by norm_num) psum906o2_107
  · exact le_trans (by norm_num) psum906o2_108
  · exact le_trans (by norm_num) psum906o2_109
  · exact le_trans (by norm_num) psum906o2_110
  · exact le_trans (by norm_num) psum906o2_111
  · exact le_trans (by norm_num) psum906o2_112
  · exact le_trans (by norm_num) psum906o2_113
  · exact le_trans (by norm_num) psum906o2_114
  · exact le_trans (by norm_num) psum906o2_115
  · exact le_trans (by norm_num) psum906o2_116
  · exact le_trans (by norm_num) psum906o2_117
  · exact le_trans (by norm_num) psum906o2_118
  · exact le_trans (by norm_num) psum906o2_119
  · exact le_trans (by norm_num) psum906o2_120
  · exact le_trans (by norm_num) psum906o2_121
  · exact le_trans (by norm_num) psum906o2_122
  · exact le_trans (by norm_num) psum906o2_123
  · exact le_trans (by norm_num) psum906o2_124
  · exact le_trans (by norm_num) psum906o2_125
  · exact le_trans (by norm_num) psum906o2_126
  · exact le_trans (by norm_num) psum906o2_127
  · exact le_trans (by norm_num) psum906o2_128
  · exact le_trans (by norm_num) psum906o2_129
  · exact le_trans (by norm_num) psum906o2_130
  · exact le_trans (by norm_num) psum906o2_131
  · exact le_trans (by norm_num) psum906o2_132
  · exact le_trans (by norm_num) psum906o2_133
  · exact le_trans (by norm_num) psum906o2_134
  · exact le_trans (by norm_num) psum906o2_135
  · exact le_trans (by norm_num) psum906o2_136
  · exact le_trans (by norm_num) psum906o2_137
  · exact le_trans (by norm_num) psum906o2_138
  · exact le_trans (by norm_num) psum906o2_139
  · exact le_trans (by norm_num) psum906o2_140
  · exact le_trans (by norm_num) psum906o2_141
  · exact le_trans (by norm_num) psum906o2_142
  · exact le_trans (by norm_num) psum906o2_143
  · exact le_trans (by norm_num) psum906o2_144
  · exact le_trans (by norm_num) psum906o2_145
  · exact le_trans (by norm_num) psum906o2_146
  · exact le_trans (by norm_num) psum906o2_147
  · exact le_trans (by norm_num) psum906o2_148
  · exact le_trans (by norm_num) psum906o2_149
  · exact le_trans (by norm_num) psum906o2_150
  · exact le_trans (by norm_num) psum906o2_151
  · exact le_trans (by norm_num) psum906o2_152
  · exact le_trans (by norm_num) psum906o2_153
  · exact le_trans (by norm_num) psum906o2_154
  · exact le_trans (by norm_num) psum906o2_155
  · exact le_trans (by norm_num) psum906o2_156
  · exact le_trans (by norm_num) psum906o2_157
  · exact le_trans (by norm_num) psum906o2_158
  · exact le_trans (by norm_num) psum906o2_159
  · exact le_trans (by norm_num) psum906o2_160
  · exact le_trans (by norm_num) psum906o2_161
  · exact le_trans (by norm_num) psum906o2_162
  · exact le_trans (by norm_num) psum906o2_163
  · exact le_trans (by norm_num) psum906o2_164
  · exact le_trans (by norm_num) psum906o2_165
  · exact le_trans (by norm_num) psum906o2_166
  · exact le_trans (by norm_num) psum906o2_167
  · exact le_trans (by norm_num) psum906o2_168
  · exact le_trans (by norm_num) psum906o2_169
  · exact le_trans (by norm_num) psum906o2_170
  · exact le_trans (by norm_num) psum906o2_171
  · exact le_trans (by norm_num) psum906o2_172
  · exact le_trans (by norm_num) psum906o2_173
  · exact le_trans (by norm_num) psum906o2_174
  · exact le_trans (by norm_num) psum906o2_175
  · exact le_trans (by norm_num) psum906o2_176
  · exact le_trans (by norm_num) psum906o2_177
  · exact le_trans (by norm_num) psum906o2_178
  · exact le_trans (by norm_num) psum906o2_179
  · exact le_trans (by norm_num) psum906o2_180
  · exact le_trans (by norm_num) psum906o2_181
  · exact le_trans (by norm_num) psum906o2_182
  · exact le_trans (by norm_num) psum906o2_183
  · exact le_trans (by norm_num) psum906o2_184
  · exact le_trans (by norm_num) psum906o2_185
  · exact le_trans (by norm_num) psum906o2_186
  · exact le_trans (by norm_num) psum906o2_187
  · exact le_trans (by norm_num) psum906o2_188
  · exact le_trans (by norm_num) psum906o2_189
  · exact le_trans (by norm_num) psum906o2_190
  · exact le_trans (by norm_num) psum906o2_191
  · exact le_trans (by norm_num) psum906o2_192
  · exact le_trans (by norm_num) psum906o2_193
  · exact le_trans (by norm_num) psum906o2_194
  · exact le_trans (by norm_num) psum906o2_195
  · exact le_trans (by norm_num) psum906o2_196
  · exact le_trans (by norm_num) psum906o2_197
  · exact le_trans (by norm_num) psum906o2_198
  · exact le_trans (by norm_num) psum906o2_199
  · exact le_trans (by norm_num) psum906o2_200
  · exact le_trans (by norm_num) psum906o2_201
  · exact le_trans (by norm_num) psum906o2_202
  · exact le_trans (by norm_num) psum906o2_203
  · exact le_trans (by norm_num) psum906o2_204
  · exact le_trans (by norm_num) psum906o2_205
  · exact le_trans (by norm_num) psum906o2_206
  · exact le_trans (by norm_num) psum906o2_207
  · exact le_trans (by norm_num) psum906o2_208
  · exact le_trans (by norm_num) psum906o2_209
  · exact le_trans (by norm_num) psum906o2_210
  · exact le_trans (by norm_num) psum906o2_211
  · exact le_trans (by norm_num) psum906o2_212
  · exact le_trans (by norm_num) psum906o2_213
  · exact le_trans (by norm_num) psum906o2_214
  · exact le_trans (by norm_num) psum906o2_215
  · exact le_trans (by norm_num) psum906o2_216
  · exact le_trans (by norm_num) psum906o2_217
  · exact le_trans (by norm_num) psum906o2_218
  · exact le_trans (by norm_num) psum906o2_219
  · exact le_trans (by norm_num) psum906o2_220
  · exact le_trans (by norm_num) psum906o2_221
  · exact le_trans (by norm_num) psum906o2_222
  · exact le_trans (by norm_num) psum906o2_223
  · exact le_trans (by norm_num) psum906o2_224
  · exact le_trans (by norm_num) psum906o2_225
  · exact le_trans (by norm_num) psum906o2_226
  · exact le_trans (by norm_num) psum906o2_227
  · exact le_trans (by norm_num) psum906o2_228
  · exact le_trans (by norm_num) psum906o2_229
  · exact le_trans (by norm_num) psum906o2_230
  · exact le_trans (by norm_num) psum906o2_231
  · exact le_trans (by norm_num) psum906o2_232
  · exact le_trans (by norm_num) psum906o2_233
  · exact le_trans (by norm_num) psum906o2_234
  · exact le_trans (by norm_num) psum906o2_235
  · exact le_trans (by norm_num) psum906o2_236
  · exact le_trans (by norm_num) psum906o2_237
  · exact le_trans (by norm_num) psum906o2_238
  · exact le_trans (by norm_num) psum906o2_239
  · exact le_trans (by norm_num) psum906o2_240
  · exact le_trans (by norm_num) psum906o2_241
  · exact le_trans (by norm_num) psum906o2_242
  · exact le_trans (by norm_num) psum906o2_243
  · exact le_trans (by norm_num) psum906o2_244
  · exact le_trans (by norm_num) psum906o2_245
  · exact le_trans (by norm_num) psum906o2_246
  · exact le_trans (by norm_num) psum906o2_247
  · exact le_trans (by norm_num) psum906o2_248
  · exact le_trans (by norm_num) psum906o2_249
  · exact le_trans (by norm_num) psum906o2_250
  · exact le_trans (by norm_num) psum906o2_251
  · exact le_trans (by norm_num) psum906o2_252
  · exact le_trans (by norm_num) psum906o2_253
  · exact le_trans (by norm_num) psum906o2_254
  · exact le_trans (by norm_num) psum906o2_255
  · exact le_trans (by norm_num) psum906o2_256
  · exact le_trans (by norm_num) psum906o2_257
  · exact le_trans (by norm_num) psum906o2_258
  · exact le_trans (by norm_num) psum906o2_259
  · exact le_trans (by norm_num) psum906o2_260
  · exact le_trans (by norm_num) psum906o2_261
  · exact le_trans (by norm_num) psum906o2_262
  · exact le_trans (by norm_num) psum906o2_263
  · exact le_trans (by norm_num) psum906o2_264
  · exact le_trans (by norm_num) psum906o2_265
  · exact le_trans (by norm_num) psum906o2_266
  · exact le_trans (by norm_num) psum906o2_267
  · exact le_trans (by norm_num) psum906o2_268
  · exact le_trans (by norm_num) psum906o2_269
  · exact le_trans (by norm_num) psum906o2_270
  · exact le_trans (by norm_num) psum906o2_271
  · exact le_trans (by norm_num) psum906o2_272
  · exact le_trans (by norm_num) psum906o2_273
  · exact le_trans (by norm_num) psum906o2_274
  · exact le_trans (by norm_num) psum906o2_275
  · exact le_trans (by norm_num) psum906o2_276
  · exact le_trans (by norm_num) psum906o2_277
  · exact le_trans (by norm_num) psum906o2_278
  · exact le_trans (by norm_num) psum906o2_279
  · exact le_trans (by norm_num) psum906o2_280
  · exact le_trans (by norm_num) psum906o2_281
  · exact le_trans (by norm_num) psum906o2_282
  · exact le_trans (by norm_num) psum906o2_283
  · exact le_trans (by norm_num) psum906o2_284
  · exact le_trans (by norm_num) psum906o2_285
  · exact le_trans (by norm_num) psum906o2_286
  · exact le_trans (by norm_num) psum906o2_287
  · exact le_trans (by norm_num) psum906o2_288
  · exact le_trans (by norm_num) psum906o2_289
  · exact le_trans (by norm_num) psum906o2_290
  · exact le_trans (by norm_num) psum906o2_291
  · exact le_trans (by norm_num) psum906o2_292
  · exact le_trans (by norm_num) psum906o2_293
  · exact le_trans (by norm_num) psum906o2_294
  · exact le_trans (by norm_num) psum906o2_295
  · exact le_trans (by norm_num) psum906o2_296
  · exact le_trans (by norm_num) psum906o2_297
  · exact le_trans (by norm_num) psum906o2_298
  · exact le_trans (by norm_num) psum906o2_299
  · exact le_trans (by norm_num) psum906o2_300
  · exact le_trans (by norm_num) psum906o2_301
  · exact le_trans (by norm_num) psum906o2_302
  · exact le_trans (by norm_num) psum906o2_303
  · exact le_trans (by norm_num) psum906o2_304
  · exact le_trans (by norm_num) psum906o2_305
  · exact le_trans (by norm_num) psum906o2_306
  · exact le_trans (by norm_num) psum906o2_307
  · exact le_trans (by norm_num) psum906o2_308
  · exact le_trans (by norm_num) psum906o2_309
  · exact le_trans (by norm_num) psum906o2_310
  · exact le_trans (by norm_num) psum906o2_311
  · exact le_trans (by norm_num) psum906o2_312
  · exact le_trans (by norm_num) psum906o2_313
  · exact le_trans (by norm_num) psum906o2_314
  · exact le_trans (by norm_num) psum906o2_315
  · exact le_trans (by norm_num) psum906o2_316
  · exact le_trans (by norm_num) psum906o2_317
  · exact le_trans (by norm_num) psum906o2_318
  · exact le_trans (by norm_num) psum906o2_319
  · exact le_trans (by norm_num) psum906o2_320
  · exact le_trans (by norm_num) psum906o2_321
  · exact le_trans (by norm_num) psum906o2_322
  · exact le_trans (by norm_num) psum906o2_323
  · exact le_trans (by norm_num) psum906o2_324
  · exact le_trans (by norm_num) psum906o2_325
  · exact le_trans (by norm_num) psum906o2_326
  · exact le_trans (by norm_num) psum906o2_327
  · exact le_trans (by norm_num) psum906o2_328
  · exact le_trans (by norm_num) psum906o2_329
  · exact le_trans (by norm_num) psum906o2_330
  · exact le_trans (by norm_num) psum906o2_331
  · exact le_trans (by norm_num) psum906o2_332
  · exact le_trans (by norm_num) psum906o2_333
  · exact le_trans (by norm_num) psum906o2_334
  · exact le_trans (by norm_num) psum906o2_335
  · exact le_trans (by norm_num) psum906o2_336
  · exact le_trans (by norm_num) psum906o2_337
  · exact le_trans (by norm_num) psum906o2_338
  · exact le_trans (by norm_num) psum906o2_339
  · exact le_trans (by norm_num) psum906o2_340
  · exact le_trans (by norm_num) psum906o2_341
  · exact le_trans (by norm_num) psum906o2_342
  · exact le_trans (by norm_num) psum906o2_343
  · exact le_trans (by norm_num) psum906o2_344
  · exact le_trans (by norm_num) psum906o2_345
  · exact le_trans (by norm_num) psum906o2_346
  · exact le_trans (by norm_num) psum906o2_347
  · exact le_trans (by norm_num) psum906o2_348
  · exact le_trans (by norm_num) psum906o2_349
  · exact le_trans (by norm_num) psum906o2_350
  · exact le_trans (by norm_num) psum906o2_351
  · exact le_trans (by norm_num) psum906o2_352
  · exact le_trans (by norm_num) psum906o2_353
  · exact le_trans (by norm_num) psum906o2_354
  · exact le_trans (by norm_num) psum906o2_355
  · exact le_trans (by norm_num) psum906o2_356
  · exact le_trans (by norm_num) psum906o2_357
  · exact le_trans (by norm_num) psum906o2_358
  · exact le_trans (by norm_num) psum906o2_359
  · exact le_trans (by norm_num) psum906o2_360
  · exact le_trans (by norm_num) psum906o2_361
  · exact le_trans (by norm_num) psum906o2_362
  · exact le_trans (by norm_num) psum906o2_363
  · exact le_trans (by norm_num) psum906o2_364
  · exact le_trans (by norm_num) psum906o2_365
  · exact le_trans (by norm_num) psum906o2_366
  · exact le_trans (by norm_num) psum906o2_367
  · exact le_trans (by norm_num) psum906o2_368
  · exact le_trans (by norm_num) psum906o2_369
  · exact le_trans (by norm_num) psum906o2_370
  · exact le_trans (by norm_num) psum906o2_371
  · exact le_trans (by norm_num) psum906o2_372
  · exact le_trans (by norm_num) psum906o2_373
  · exact le_trans (by norm_num) psum906o2_374
  · exact le_trans (by norm_num) psum906o2_375
  · exact le_trans (by norm_num) psum906o2_376
  · exact le_trans (by norm_num) psum906o2_377
  · exact le_trans (by norm_num) psum906o2_378
  · exact le_trans (by norm_num) psum906o2_379
  · exact le_trans (by norm_num) psum906o2_380
  · exact le_trans (by norm_num) psum906o2_381
  · exact le_trans (by norm_num) psum906o2_382
  · exact le_trans (by norm_num) psum906o2_383
  · exact le_trans (by norm_num) psum906o2_384
  · exact le_trans (by norm_num) psum906o2_385
  · exact le_trans (by norm_num) psum906o2_386
  · exact le_trans (by norm_num) psum906o2_387
  · exact le_trans (by norm_num) psum906o2_388
  · exact le_trans (by norm_num) psum906o2_389
  · exact le_trans (by norm_num) psum906o2_390
  · exact le_trans (by norm_num) psum906o2_391
  · exact le_trans (by norm_num) psum906o2_392
  · exact le_trans (by norm_num) psum906o2_393
  · exact le_trans (by norm_num) psum906o2_394
  · exact le_trans (by norm_num) psum906o2_395
  · exact le_trans (by norm_num) psum906o2_396
  · exact le_trans (by norm_num) psum906o2_397
  · exact le_trans (by norm_num) psum906o2_398
  · exact le_trans (by norm_num) psum906o2_399
  · exact le_trans (by norm_num) psum906o2_400
  · exact le_trans (by norm_num) psum906o2_401
  · exact le_trans (by norm_num) psum906o2_402
  · exact le_trans (by norm_num) psum906o2_403
  · exact le_trans (by norm_num) psum906o2_404
  · exact le_trans (by norm_num) psum906o2_405
  · exact le_trans (by norm_num) psum906o2_406
  · exact le_trans (by norm_num) psum906o2_407
  · exact le_trans (by norm_num) psum906o2_408
  · exact le_trans (by norm_num) psum906o2_409
  · exact le_trans (by norm_num) psum906o2_410
  · exact le_trans (by norm_num) psum906o2_411
  · exact le_trans (by norm_num) psum906o2_412
  · exact le_trans (by norm_num) psum906o2_413
  · exact le_trans (by norm_num) psum906o2_414
  · exact le_trans (by norm_num) psum906o2_415
  · exact le_trans (by norm_num) psum906o2_416
  · exact le_trans (by norm_num) psum906o2_417
  · exact le_trans (by norm_num) psum906o2_418
  · exact le_trans (by norm_num) psum906o2_419
  · exact le_trans (by norm_num) psum906o2_420
  · exact le_trans (by norm_num) psum906o2_421
  · exact le_trans (by norm_num) psum906o2_422
  · exact le_trans (by norm_num) psum906o2_423
  · exact le_trans (by norm_num) psum906o2_424
  · exact le_trans (by norm_num) psum906o2_425
  · exact le_trans (by norm_num) psum906o2_426
  · exact le_trans (by norm_num) psum906o2_427
  · exact le_trans (by norm_num) psum906o2_428
  · exact le_trans (by norm_num) psum906o2_429
  · exact le_trans (by norm_num) psum906o2_430
  · exact le_trans (by norm_num) psum906o2_431
  · exact le_trans (by norm_num) psum906o2_432
  · exact le_trans (by norm_num) psum906o2_433
  · exact le_trans (by norm_num) psum906o2_434
  · exact le_trans (by norm_num) psum906o2_435
  · exact le_trans (by norm_num) psum906o2_436
  · exact le_trans (by norm_num) psum906o2_437
  · exact le_trans (by norm_num) psum906o2_438
  · exact le_trans (by norm_num) psum906o2_439
  · exact le_trans (by norm_num) psum906o2_440
  · exact le_trans (by norm_num) psum906o2_441
  · exact le_trans (by norm_num) psum906o2_442
  · exact le_trans (by norm_num) psum906o2_443
  · exact le_trans (by norm_num) psum906o2_444
  · exact le_trans (by norm_num) psum906o2_445
  · exact le_trans (by norm_num) psum906o2_446
  · exact le_trans (by norm_num) psum906o2_447
  · exact le_trans (by norm_num) psum906o2_448
  · exact le_trans (by norm_num) psum906o2_449
  · exact le_trans (by norm_num) psum906o2_450
  · exact le_trans (by norm_num) psum906o2_451
  · exact le_trans (by norm_num) psum906o2_452
  · exact le_trans (by norm_num) psum906o2_453
  · exact le_trans (by norm_num) psum906o2_454
  · exact le_trans (by norm_num) psum906o2_455
  · exact le_trans (by norm_num) psum906o2_456
  · exact le_trans (by norm_num) psum906o2_457
  · exact le_trans (by norm_num) psum906o2_458
  · exact le_trans (by norm_num) psum906o2_459
  · exact le_trans (by norm_num) psum906o2_460
  · exact le_trans (by norm_num) psum906o2_461
  · exact le_trans (by norm_num) psum906o2_462
  · exact le_trans (by norm_num) psum906o2_463
  · exact le_trans (by norm_num) psum906o2_464
  · exact le_trans (by norm_num) psum906o2_465
  · exact le_trans (by norm_num) psum906o2_466
  · exact le_trans (by norm_num) psum906o2_467
  · exact le_trans (by norm_num) psum906o2_468
  · exact le_trans (by norm_num) psum906o2_469
  · exact le_trans (by norm_num) psum906o2_470
  · exact le_trans (by norm_num) psum906o2_471
  · exact le_trans (by norm_num) psum906o2_472
  · exact le_trans (by norm_num) psum906o2_473
  · exact le_trans (by norm_num) psum906o2_474
  · exact le_trans (by norm_num) psum906o2_475
  · exact le_trans (by norm_num) psum906o2_476
  · exact le_trans (by norm_num) psum906o2_477
  · exact le_trans (by norm_num) psum906o2_478
  · exact le_trans (by norm_num) psum906o2_479
  · exact le_trans (by norm_num) psum906o2_480
  · exact le_trans (by norm_num) psum906o2_481
  · exact le_trans (by norm_num) psum906o2_482
  · exact le_trans (by norm_num) psum906o2_483
  · exact le_trans (by norm_num) psum906o2_484
  · exact le_trans (by norm_num) psum906o2_485
  · exact le_trans (by norm_num) psum906o2_486
  · exact le_trans (by norm_num) psum906o2_487
  · exact le_trans (by norm_num) psum906o2_488
  · exact le_trans (by norm_num) psum906o2_489
  · exact le_trans (by norm_num) psum906o2_490
  · exact le_trans (by norm_num) psum906o2_491
  · exact le_trans (by norm_num) psum906o2_492
  · exact le_trans (by norm_num) psum906o2_493
  · exact le_trans (by norm_num) psum906o2_494
  · exact le_trans (by norm_num) psum906o2_495
  · exact le_trans (by norm_num) psum906o2_496
  · exact le_trans (by norm_num) psum906o2_497
  · exact le_trans (by norm_num) psum906o2_498
  · exact le_trans (by norm_num) psum906o2_499
  · exact le_trans (by norm_num) psum906o2_500

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum906o2_floor
#print axioms CriticalLinePhasor.DVP.psum906o2_500
end AxiomAudit
