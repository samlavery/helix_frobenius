import RequestProject.DVPCos960o2Table

/-!
# The cosine partial-sum floor, `t = 960/2` (N = 500)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 960/2` segment certificate. -/
def cos960o2c (n : ℕ) : ℝ := Real.cos (((960:ℕ):ℝ) * (Real.log n / 2))

theorem psum960o2_11 : ((98247/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos960o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 11 - ((6142/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum960o2_12 : ((178089/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos960o2c k) + cos960o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_11
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 12 - ((497557/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_13 : ((183683/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos960o2c k) + cos960o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_12
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 13 - ((189297/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_14 : ((1062747/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos960o2c k) + cos960o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_13
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 14 - ((-773983/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_15 : ((358151/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos960o2c k) + cos960o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_14
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 15 - ((182027/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_16 : ((2159821/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos960o2c k) + cos960o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_15
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 16 - ((184583/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_17 : ((1226389/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos960o2c k) + cos960o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_16
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 17 - ((-233333/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_18 : ((1583503/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos960o2c k) + cos960o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_17
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 18 - ((178607/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_19 : ((1254913/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos960o2c k) + cos960o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_18
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 19 - ((926423/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_20 : ((391617/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos960o2c k) + cos960o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_19
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 20 - ((62321/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_21 : ((1135063/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos960o2c k) + cos960o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_20
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 21 - ((-86271/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_22 : ((2915889/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos960o2c k) + cos960o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_21
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 22 - ((645863/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_23 : ((484669/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos960o2c k) + cos960o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_22
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 23 - ((-977113/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_24 : ((2159357/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos960o2c k) + cos960o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_23
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 24 - ((220781/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_25 : ((1491397/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos960o2c k) + cos960o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_24
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 25 - ((823537/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_26 : ((948151/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos960o2c k) + cos960o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_25
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 26 - ((80991/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_27 : ((800151/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos960o2c k) + cos960o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_26
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 27 - ((208251/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_28 : ((3074807/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos960o2c k) + cos960o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_27
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 28 - ((-115731/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_29 : ((1561051/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos960o2c k) + cos960o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_28
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 29 - ((9479/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_30 : ((56509/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos960o2c k) + cos960o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_29
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 30 - ((247287/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_31 : ((9672/3125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos960o2c k) + cos960o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_30
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 31 - ((-130359/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_32 : ((3174801/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos960o2c k) + cos960o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_31
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 32 - ((79861/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_33 : ((61422/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos960o2c k) + cos960o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_32
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 33 - ((756307/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_34 : ((3144223/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos960o2c k) + cos960o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_33
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 34 - ((-157337/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_35 : ((2367969/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos960o2c k) + cos960o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_34
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 35 - ((-388077/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_36 : ((2434937/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos960o2c k) + cos960o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_35
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 36 - ((16767/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_37 : ((3041827/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos960o2c k) + cos960o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_36
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 37 - ((60699/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_38 : ((152667/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos960o2c k) + cos960o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_37
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 38 - ((193737/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_39 : ((4525873/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos960o2c k) + cos960o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_38
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 39 - ((354649/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_40 : ((152867/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos960o2c k) + cos960o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_39
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 40 - ((365971/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_41 : ((4558867/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos960o2c k) + cos960o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_40
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 41 - ((-332777/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_42 : ((717113/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos960o2c k) + cos960o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_41
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 42 - ((-486601/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_43 : ((3078989/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos960o2c k) + cos960o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_42
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 43 - ((-126619/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_44 : ((980133/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos960o2c k) + cos960o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_43
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 44 - ((841643/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_45 : ((854887/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos960o2c k) + cos960o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_44
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 45 - ((354003/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_46 : ((3277849/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos960o2c k) + cos960o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_45
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 46 - ((-498243/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_47 : ((198203/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos960o2c k) + cos960o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_46
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 47 - ((686311/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_48 : ((3888481/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos960o2c k) + cos960o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_47
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 48 - ((-75479/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_49 : ((437729/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos960o2c k) + cos960o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_48
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 49 - ((-386549/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_50 : ((412229/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos960o2c k) + cos960o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_49
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 50 - ((310279/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_51 : ((3440607/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos960o2c k) + cos960o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_50
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 51 - ((-681583/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_52 : ((4042371/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos960o2c k) + cos960o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_51
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 52 - ((75233/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_53 : ((3686077/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos960o2c k) + cos960o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_52
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 53 - ((-178097/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_54 : ((1798857/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos960o2c k) + cos960o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_53
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 54 - ((-88263/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_55 : ((265381/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos960o2c k) + cos960o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_54
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 55 - ((324241/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_56 : ((3249981/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos960o2c k) + cos960o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_55
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 56 - ((-199203/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_57 : ((3917597/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos960o2c k) + cos960o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_56
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 57 - ((166929/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_58 : ((4256237/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos960o2c k) + cos960o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_57
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 58 - ((16937/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_59 : ((1628077/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos960o2c k) + cos960o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_58
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 59 - ((-999983/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_60 : ((1736741/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos960o2c k) + cos960o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_59
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 60 - ((54357/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_61 : ((553617/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos960o2c k) + cos960o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_60
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 61 - ((477777/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_62 : ((2090561/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos960o2c k) + cos960o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_61
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 62 - ((-123857/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_63 : ((3183949/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos960o2c k) + cos960o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_62
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 63 - ((-997073/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_64 : ((2967311/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos960o2c k) + cos960o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_63
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 64 - ((-108269/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_65 : ((3775101/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos960o2c k) + cos960o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_64
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 65 - ((80789/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_66 : ((37521/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos960o2c k) + cos960o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_65
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 66 - ((228781/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_67 : ((4909043/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos960o2c k) + cos960o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_66
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 67 - ((109509/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_68 : ((542291/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos960o2c k) + cos960o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_67
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 68 - ((-114123/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_69 : ((134669/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos960o2c k) + cos960o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_68
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 69 - ((-971503/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_70 : ((609871/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos960o2c k) + cos960o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_69
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 70 - ((-927141/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_71 : ((456313/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos960o2c k) + cos960o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_70
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 71 - ((-153533/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_72 : ((319231/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos960o2c k) + cos960o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_71
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 72 - ((-228997/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_73 : ((340481/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos960o2c k) + cos960o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_72
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 73 - ((2127/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_74 : ((2049009/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos960o2c k) + cos960o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_73
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 74 - ((21669/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_75 : ((317567/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos960o2c k) + cos960o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_74
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 75 - ((491627/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_76 : ((3095523/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos960o2c k) + cos960o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_75
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 76 - ((555087/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_77 : ((728671/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos960o2c k) + cos960o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_76
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 77 - ((136983/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_78 : ((2057089/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos960o2c k) + cos960o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_77
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 78 - ((470923/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_79 : ((4430421/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos960o2c k) + cos960o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_78
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 79 - ((316343/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_80 : ((4506757/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos960o2c k) + cos960o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_79
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 80 - ((19109/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_81 : ((533149/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos960o2c k) + cos960o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_80
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 81 - ((-48293/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_82 : ((1834987/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos960o2c k) + cos960o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_81
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 82 - ((-297559/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_83 : ((1388807/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos960o2c k) + cos960o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_82
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 83 - ((-44613/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_84 : ((889851/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos960o2c k) + cos960o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_83
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 84 - ((-249453/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_85 : ((995043/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos960o2c k) + cos960o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_84
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 85 - ((-784559/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_86 : ((764163/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos960o2c k) + cos960o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_85
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 86 - ((-11539/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_87 : ((1244431/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos960o2c k) + cos960o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_86
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 87 - ((30023/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_88 : ((1103741/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos960o2c k) + cos960o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_87
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 88 - ((963151/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_89 : ((1519963/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos960o2c k) + cos960o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_88
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 89 - ((26017/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_90 : ((1551733/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos960o2c k) + cos960o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_89
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 90 - ((1591/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_91 : ((2310453/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos960o2c k) + cos960o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_90
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 91 - ((-792913/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_92 : ((1382439/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos960o2c k) + cos960o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_91
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 92 - ((-463957/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_93 : ((643829/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos960o2c k) + cos960o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_92
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 93 - ((-94681/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_94 : ((215727/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos960o2c k) + cos960o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_93
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 94 - ((54357/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_95 : ((1464971/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos960o2c k) + cos960o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_94
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 95 - ((193193/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_96 : ((32059/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos960o2c k) + cos960o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_95
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 96 - ((-182561/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_97 : ((785443/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos960o2c k) + cos960o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_96
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 97 - ((-496867/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_98 : ((46007/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos960o2c k) + cos960o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_97
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 98 - ((-49281/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_99 : ((1219323/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos960o2c k) + cos960o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_98
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 99 - ((483261/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_100 : ((1400659/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos960o2c k) + cos960o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_99
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 100 - ((90693/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_101 : ((947183/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos960o2c k) + cos960o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_100
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 101 - ((-226713/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_102 : ((728859/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos960o2c k) + cos960o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_101
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 102 - ((-109137/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_103 : ((296221/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos960o2c k) + cos960o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_102
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 103 - ((18243/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_104 : ((2710329/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos960o2c k) + cos960o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_103
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 104 - ((340661/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_105 : ((868121/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos960o2c k) + cos960o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_104
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 105 - ((-973987/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_106 : ((1670211/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos960o2c k) + cos960o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_105
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 106 - ((-65931/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_107 : ((2660423/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos960o2c k) + cos960o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_106
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 107 - ((123789/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_108 : ((1141667/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos960o2c k) + cos960o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_107
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 108 - ((-376989/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_109 : ((300501/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos960o2c k) + cos960o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_108
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 109 - ((-780729/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_110 : ((1172949/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos960o2c k) + cos960o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_109
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 110 - ((843493/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_111 : ((2543101/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos960o2c k) + cos960o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_110
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 111 - ((197303/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_112 : ((391183/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos960o2c k) + cos960o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_111
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 112 - ((-978269/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_113 : ((1086707/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos960o2c k) + cos960o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_112
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 113 - ((304391/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_114 : ((648221/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos960o2c k) + cos960o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_113
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 114 - ((41957/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_115 : ((1596587/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos960o2c k) + cos960o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_114
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 115 - ((-996197/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_116 : ((2196719/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos960o2c k) + cos960o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_115
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 116 - ((75029/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_117 : ((2525237/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos960o2c k) + cos960o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_116
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 117 - ((164309/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_118 : ((783793/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos960o2c k) + cos960o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_117
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 118 - ((-957551/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_119 : ((595831/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos960o2c k) + cos960o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_118
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 119 - ((407919/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_120 : ((7201/3125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos960o2c k) + cos960o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_119
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 120 - ((-9863/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_121 : ((1613239/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos960o2c k) + cos960o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_120
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 121 - ((-690981/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_122 : ((1306569/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos960o2c k) + cos960o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_121
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 122 - ((999999/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_123 : ((11879/6250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos960o2c k) + cos960o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_122
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 123 - ((-356199/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_124 : ((1948367/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos960o2c k) + cos960o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_123
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 124 - ((47827/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_125 : ((2566127/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos960o2c k) + cos960o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_124
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 125 - ((30893/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_126 : ((198811/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos960o2c k) + cos960o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_125
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 126 - ((-975539/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_127 : ((624711/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos960o2c k) + cos960o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_126
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 127 - ((113557/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_128 : ((2004963/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos960o2c k) + cos960o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_127
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 128 - ((-493781/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_129 : ((1927509/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos960o2c k) + cos960o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_128
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 129 - ((-38677/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_130 : ((1263263/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos960o2c k) + cos960o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_129
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 130 - ((599117/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_131 : ((801101/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos960o2c k) + cos960o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_130
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 131 - ((-14441/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_132 : ((2595287/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos960o2c k) + cos960o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_131
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 132 - ((198637/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_133 : ((110541/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos960o2c k) + cos960o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_132
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 133 - ((-826531/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_134 : ((1132283/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos960o2c k) + cos960o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_133
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 134 - ((49601/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_135 : ((2172781/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos960o2c k) + cos960o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_134
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 135 - ((-18337/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_136 : ((373707/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos960o2c k) + cos960o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_135
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 136 - ((-152073/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_137 : ((500063/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos960o2c k) + cos960o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_136
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 137 - ((15797/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_138 : ((102577/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos960o2c k) + cos960o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_137
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 138 - ((-858983/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_139 : ((327307/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos960o2c k) + cos960o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_138
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 139 - ((244331/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_140 : ((324409/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos960o2c k) + cos960o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_139
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 140 - ((-996311/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_141 : ((2557601/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos960o2c k) + cos960o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_140
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 141 - ((116957/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_142 : ((27166/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos960o2c k) + cos960o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_141
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 142 - ((-818877/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_143 : ((1203663/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos960o2c k) + cos960o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_142
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 143 - ((334401/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_144 : ((1902331/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos960o2c k) + cos960o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_143
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 144 - ((-100979/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_145 : ((1122101/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos960o2c k) + cos960o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_144
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 145 - ((341971/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_146 : ((2053659/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos960o2c k) + cos960o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_145
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 146 - ((-190443/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_147 : ((2110303/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos960o2c k) + cos960o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_146
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 147 - ((7093/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_148 : ((2166063/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos960o2c k) + cos960o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_147
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 148 - ((2793/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_149 : ((126239/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos960o2c k) + cos960o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_148
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 149 - ((-146139/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_150 : ((1116899/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos960o2c k) + cos960o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_149
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 150 - ((107037/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_151 : ((98659/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos960o2c k) + cos960o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_150
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 151 - ((-130259/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_152 : ((1129661/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos960o2c k) + cos960o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_151
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 152 - ((143121/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_153 : ((78691/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos960o2c k) + cos960o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_152
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 153 - ((-291947/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_154 : ((561297/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos960o2c k) + cos960o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_153
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 154 - ((278013/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_155 : ((2000657/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos960o2c k) + cos960o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_154
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 155 - ((-244431/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_156 : ((547887/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos960o2c k) + cos960o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_155
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 156 - ((190991/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_157 : ((518509/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos960o2c k) + cos960o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_156
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 157 - ((-29353/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_158 : ((52441/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos960o2c k) + cos960o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_157
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 158 - ((2963/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_159 : ((2186891/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos960o2c k) + cos960o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_158
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 159 - ((89351/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_160 : ((1966947/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos960o2c k) + cos960o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_159
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 160 - ((-54961/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_161 : ((582723/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos960o2c k) + cos960o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_160
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 161 - ((72809/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_162 : ((1814907/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos960o2c k) + cos960o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_161
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 162 - ((-103177/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_163 : ((1240749/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos960o2c k) + cos960o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_162
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 163 - ((666691/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_164 : ((209557/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos960o2c k) + cos960o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_163
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 164 - ((-402471/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_165 : ((2592859/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos960o2c k) + cos960o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_164
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 165 - ((916503/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_166 : ((803609/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos960o2c k) + cos960o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_165
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 166 - ((-985541/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_167 : ((2603213/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos960o2c k) + cos960o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_166
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 167 - ((199219/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_168 : ((834379/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos960o2c k) + cos960o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_167
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 168 - ((-186871/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_169 : ((2460339/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos960o2c k) + cos960o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_168
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 169 - ((791681/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_170 : ((59139/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos960o2c k) + cos960o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_169
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 170 - ((-567791/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_171 : ((541569/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos960o2c k) + cos960o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_170
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 171 - ((34241/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_172 : ((278927/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos960o2c k) + cos960o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_171
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 172 - ((1631/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_173 : ((90983/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos960o2c k) + cos960o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_172
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 173 - ((-51457/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_174 : ((126821/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos960o2c k) + cos960o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_173
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 174 - ((35843/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_175 : ((1607897/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos960o2c k) + cos960o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_174
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 175 - ((-928423/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_176 : ((1303731/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos960o2c k) + cos960o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_175
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 176 - ((199933/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_177 : ((1706007/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos960o2c k) + cos960o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_176
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 177 - ((-180271/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_178 : ((1169491/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos960o2c k) + cos960o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_177
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 178 - ((25323/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_179 : ((421591/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos960o2c k) + cos960o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_178
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 179 - ((-230927/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_180 : ((375103/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos960o2c k) + cos960o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_179
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 180 - ((-11617/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_181 : ((20259/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos960o2c k) + cos960o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_180
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 181 - ((2053/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_182 : ((1595337/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos960o2c k) + cos960o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_181
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 182 - ((-468469/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_183 : ((2583341/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos960o2c k) + cos960o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_182
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 183 - ((123513/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_184 : ((361157/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos960o2c k) + cos960o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_183
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 184 - ((-48591/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_185 : ((2149209/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos960o2c k) + cos960o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_184
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 185 - ((85881/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_186 : ((2351053/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos960o2c k) + cos960o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_185
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 186 - ((25243/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_187 : ((66159/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos960o2c k) + cos960o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_186
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 187 - ((-348489/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_188 : ((657551/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos960o2c k) + cos960o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_187
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 188 - ((976329/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_189 : ((1700379/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos960o2c k) + cos960o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_188
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 189 - ((-37189/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_190 : ((450501/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos960o2c k) + cos960o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_189
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 190 - ((276113/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_191 : ((457849/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos960o2c k) + cos960o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_190
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 191 - ((921/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_192 : ((208331/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos960o2c k) + cos960o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_191
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 192 - ((-622497/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_193 : ((658817/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos960o2c k) + cos960o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_192
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 193 - ((12109/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_194 : ((1718117/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos960o2c k) + cos960o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_193
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 194 - ((-917051/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_195 : ((2185907/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos960o2c k) + cos960o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_194
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 195 - ((46789/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_196 : ((2383931/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos960o2c k) + cos960o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_195
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 196 - ((49531/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_197 : ((800791/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos960o2c k) + cos960o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_196
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 197 - ((-782249/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_198 : ((1300367/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos960o2c k) + cos960o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_197
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 198 - ((249813/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_199 : ((938633/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos960o2c k) + cos960o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_198
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 199 - ((-90421/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_200 : ((60943/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos960o2c k) + cos960o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_199
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 200 - ((7301/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_201 : ((2574559/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos960o2c k) + cos960o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_200
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 201 - ((624483/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_202 : ((791903/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos960o2c k) + cos960o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_201
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 202 - ((-990653/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_203 : ((1194573/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos960o2c k) + cos960o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_202
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 203 - ((2517/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_204 : ((279513/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos960o2c k) + cos960o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_203
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 204 - ((-76471/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_205 : ((1638129/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos960o2c k) + cos960o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_204
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 205 - ((-4783/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_206 : ((526067/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos960o2c k) + cos960o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_205
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 206 - ((496153/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_207 : ((186091/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos960o2c k) + cos960o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_206
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 207 - ((-30773/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_208 : ((382049/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos960o2c k) + cos960o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_207
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 208 - ((9887/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_209 : ((2620471/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos960o2c k) + cos960o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_208
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 209 - ((355163/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_210 : ((162279/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos960o2c k) + cos960o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_209
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 210 - ((-997581/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_211 : ((2219819/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos960o2c k) + cos960o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_210
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 211 - ((597129/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_212 : ((1224913/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos960o2c k) + cos960o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_211
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 212 - ((230107/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_213 : ((775919/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos960o2c k) + cos960o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_212
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 213 - ((-28059/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_214 : ((614391/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos960o2c k) + cos960o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_213
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 214 - ((452913/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_215 : ((2229981/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos960o2c k) + cos960o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_214
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 215 - ((-227483/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_216 : ((1597433/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos960o2c k) + cos960o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_215
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 216 - ((-9882/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_217 : ((519319/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos960o2c k) + cos960o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_216
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 217 - ((499631/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_218 : ((101689/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos960o2c k) + cos960o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_217
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 218 - ((-112543/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_219 : ((846749/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos960o2c k) + cos960o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_218
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 219 - ((-170091/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_220 : ((664367/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos960o2c k) + cos960o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_219
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 220 - ((96407/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_221 : ((1889839/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos960o2c k) + cos960o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_220
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 221 - ((-767529/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_222 : ((223787/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos960o2c k) + cos960o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_221
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 222 - ((-99443/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_223 : ((133699/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos960o2c k) + cos960o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_222
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 223 - ((110473/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_224 : ((359937/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos960o2c k) + cos960o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_223
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 224 - ((-174839/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_225 : ((464961/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos960o2c k) + cos960o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_224
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 225 - ((60259/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_226 : ((534947/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos960o2c k) + cos960o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_225
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 226 - ((814991/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_227 : ((1755251/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos960o2c k) + cos960o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_226
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 227 - ((-114923/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_228 : ((1889549/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos960o2c k) + cos960o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_227
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 228 - ((67199/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_229 : ((1338281/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos960o2c k) + cos960o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_228
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 229 - ((787113/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_230 : ((1749817/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos960o2c k) + cos960o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_229
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 230 - ((-185329/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_231 : ((1875611/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos960o2c k) + cos960o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_230
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 231 - ((62947/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_232 : ((2684221/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos960o2c k) + cos960o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_231
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 232 - ((80871/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_233 : ((1782903/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos960o2c k) + cos960o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_232
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 233 - ((-450609/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_234 : ((181947/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos960o2c k) + cos960o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_233
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 234 - ((36667/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_235 : ((2690749/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos960o2c k) + cos960o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_234
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 235 - ((871379/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_236 : ((186003/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos960o2c k) + cos960o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_235
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 236 - ((-830619/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_237 : ((1728521/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos960o2c k) + cos960o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_236
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 237 - ((-131409/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_238 : ((1339071/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos960o2c k) + cos960o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_237
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 238 - ((949721/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_239 : ((99447/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos960o2c k) + cos960o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_238
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 239 - ((-344551/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_240 : ((1620567/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos960o2c k) + cos960o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_239
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 240 - ((-368273/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_241 : ((65483/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos960o2c k) + cos960o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_240
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 241 - ((998853/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_242 : ((2171083/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos960o2c k) + cos960o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_241
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 242 - ((-448137/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_243 : ((1528651/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos960o2c k) + cos960o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_242
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 243 - ((-160583/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_244 : ((2484749/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos960o2c k) + cos960o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_243
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 244 - ((478099/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_245 : ((2389483/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos960o2c k) + cos960o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_244
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 245 - ((-47583/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_246 : ((75113/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos960o2c k) + cos960o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_245
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 246 - ((-887123/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_247 : ((2257511/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos960o2c k) + cos960o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_246
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 247 - ((755351/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_248 : ((2596559/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos960o2c k) + cos960o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_247
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 248 - ((84787/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_249 : ((199571/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos960o2c k) + cos960o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_248
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 249 - ((-999891/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_250 : ((1956081/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos960o2c k) + cos960o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_249
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 250 - ((359613/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_251 : ((1356121/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 251, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 251, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 250, cos960o2c k) + cos960o2c 251 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 250) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_250
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 251 - ((756261/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_251).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_252 : ((1844247/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 252, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 252, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 251, cos960o2c k) + cos960o2c 252 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 251) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_251
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 252 - ((-173579/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_252).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_253 : ((1655629/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 253, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 253, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 252, cos960o2c k) + cos960o2c 253 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 252) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_252
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 253 - ((-94259/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_253).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_254 : ((264669/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 254, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 254, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 253, cos960o2c k) + cos960o2c 254 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 253) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_253
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 254 - ((991161/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_254).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_255 : ((442627/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 255, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 255, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 254, cos960o2c k) + cos960o2c 255 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 254) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_254
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 255 - ((-86691/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_255).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_256 : ((297117/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 256, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 256, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 255, cos960o2c k) + cos960o2c 256 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 255) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_255
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 256 - ((-14549/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_256).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_257 : ((2356237/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 257, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 257, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 256, cos960o2c k) + cos960o2c 257 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 256) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_256
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 257 - ((27211/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_257).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_258 : ((257513/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 258, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 258, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 257, cos960o2c k) + cos960o2c 258 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 257) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_257
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 258 - ((218993/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_258).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_259 : ((1577161/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 259, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 259, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 258, cos960o2c k) + cos960o2c 259 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 258) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_258
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 259 - ((-997869/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_259).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_260 : ((239317/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 260, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 260, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 259, cos960o2c k) + cos960o2c 260 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 259) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_259
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 260 - ((13499/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_260).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_261 : ((2730597/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 261, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 261, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 260, cos960o2c k) + cos960o2c 261 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 260) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_260
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 261 - ((816161/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_261).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_262 : ((489807/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 262, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 262, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 261, cos960o2c k) + cos960o2c 262 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 261) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_261
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 262 - ((-771269/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_262).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_263 : ((770129/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 263, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 263, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 262, cos960o2c k) + cos960o2c 263 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 262) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_262
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 263 - ((-41887/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_263).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_264 : ((2523759/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 264, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 264, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 263, cos960o2c k) + cos960o2c 264 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 263) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_263
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 264 - ((983601/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_264).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_265 : ((2461109/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 265, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 265, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 264, cos960o2c k) + cos960o2c 265 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 264) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_264
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 265 - ((-1251/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_265).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_266 : ((376397/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 266, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 266, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 265, cos960o2c k) + cos960o2c 266 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 265) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_265
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 266 - ((-955421/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_266).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_267 : ((2011041/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 267, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 267, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 266, cos960o2c k) + cos960o2c 267 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 266) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_266
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 267 - ((505553/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_267).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_268 : ((685041/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 268, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 268, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 267, cos960o2c k) + cos960o2c 268 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 267) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_267
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 268 - ((729223/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_268).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_269 : ((1914881/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 269, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 269, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 268, cos960o2c k) + cos960o2c 269 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 268) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_268
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 269 - ((-825183/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_269).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_270 : ((383653/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 270, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 270, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 269, cos960o2c k) + cos960o2c 270 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 269) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_269
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 270 - ((-380169/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_270).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_271 : ((503443/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 271, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 271, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 270, cos960o2c k) + cos960o2c 271 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 270) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_270
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 271 - ((982703/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_271).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_272 : ((2506239/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 272, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 272, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 271, cos960o2c k) + cos960o2c 272 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 271) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_271
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 272 - ((-2719/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_272).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_273 : ((1526379/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 273, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 273, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 272, cos960o2c k) + cos960o2c 273 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 272) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_272
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 273 - ((-12247/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_273).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_274 : ((190259/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 274, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 274, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 273, cos960o2c k) + cos960o2c 274 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 273) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_273
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 274 - ((376311/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_274).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_275 : ((171739/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 275, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 275, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 274, cos960o2c k) + cos960o2c 275 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 274) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_274
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 275 - ((422667/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_275).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_276 : ((519263/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 276, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 276, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 275, cos960o2c k) + cos960o2c 276 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 275) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_275
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 276 - ((-41917/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_276).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_277 : ((363901/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 277, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 277, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 276, cos960o2c k) + cos960o2c 277 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 276) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_276
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 277 - ((-155337/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_277).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_278 : ((2327501/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 278, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 278, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 277, cos960o2c k) + cos960o2c 278 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 277) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_277
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 278 - ((871997/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_278).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_279 : ((669647/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 279, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 279, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 278, cos960o2c k) + cos960o2c 279 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 278) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_278
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 279 - ((351187/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_279).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_280 : ((1700927/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 280, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 280, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 279, cos960o2c k) + cos960o2c 280 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 279) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_279
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 280 - ((-977561/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_280).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_281 : ((32581/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 281, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 281, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 280, cos960o2c k) + cos960o2c 281 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 280) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_280
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 281 - ((-71777/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_281).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_282 : ((656749/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 282, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 282, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 281, cos960o2c k) + cos960o2c 282 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 281) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_281
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 282 - ((499023/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_282).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_283 : ((609307/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 283, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 283, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 282, cos960o2c k) + cos960o2c 283 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 282) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_282
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 283 - ((-47417/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_283).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_284 : ((1485769/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 284, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 284, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 283, cos960o2c k) + cos960o2c 284 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 283) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_283
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 284 - ((-951359/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_284).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_285 : ((951059/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 285, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 285, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 284, cos960o2c k) + cos960o2c 285 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 284) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_284
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 285 - ((416449/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_285).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_286 : ((2759709/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 286, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 286, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 285, cos960o2c k) + cos960o2c 286 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 285) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_285
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 286 - ((857691/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_286).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_287 : ((1079353/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 287, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 287, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 286, cos960o2c k) + cos960o2c 287 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 286) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_286
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 287 - ((-600903/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_287).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_288 : ((711207/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 288, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 288, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 287, cos960o2c k) + cos960o2c 288 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 287) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_287
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 288 - ((-11503/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_288).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_289 : ((541129/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 289, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 289, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 288, cos960o2c k) + cos960o2c 289 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 288) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_288
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 289 - ((371101/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_289).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_290 : ((1383677/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 290, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 290, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 289, cos960o2c k) + cos960o2c 290 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 289) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_289
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 290 - ((301469/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_290).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_291 : ((76921/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 291, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 291, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 290, cos960o2c k) + cos960o2c 291 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 290) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_290
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 291 - ((-844229/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_291).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_292 : ((726247/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 292, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 292, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 291, cos960o2c k) + cos960o2c 292 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 291) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_291
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 292 - ((-470431/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_292).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_293 : ((1182833/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 293, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 293, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 292, cos960o2c k) + cos960o2c 293 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 292) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_292
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 293 - ((114159/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_293).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_294 : ((27131/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 294, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 294, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 293, cos960o2c k) + cos960o2c 294 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 293) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_293
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 294 - ((173767/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_294).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_295 : ((351289/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 295, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 295, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 294, cos960o2c k) + cos960o2c 295 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 294) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_294
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 295 - ((-191311/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_295).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_296 : ((94777/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 296, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 296, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 295, cos960o2c k) + cos960o2c 296 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 295) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_295
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 296 - ((-239913/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_296).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_297 : ((2497539/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 297, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 297, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 296, cos960o2c k) + cos960o2c 297 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 296) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_296
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 297 - ((981207/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_297).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_298 : ((2648409/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 298, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 298, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 297, cos960o2c k) + cos960o2c 298 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 297) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_297
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 298 - ((15097/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_298).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_299 : ((827417/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 299, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 299, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 298, cos960o2c k) + cos960o2c 299 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 298) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_298
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 299 - ((-39739/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_299).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_300 : ((786203/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 300, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 300, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 299, cos960o2c k) + cos960o2c 300 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 299) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_299
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 300 - ((-10291/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_300).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_301 : ((514149/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 301, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 301, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 300, cos960o2c k) + cos960o2c 301 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 300) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_300
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 301 - ((998439/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_301).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_302 : ((651311/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 302, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 302, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 301, cos960o2c k) + cos960o2c 302 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 301) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_301
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 302 - ((34599/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_302).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_303 : ((1605317/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 303, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 303, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 302, cos960o2c k) + cos960o2c 303 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 302) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_302
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 303 - ((-999827/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_303).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_304 : ((798677/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 304, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 304, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 303, cos960o2c k) + cos960o2c 304 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 303) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_303
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 304 - ((-7863/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_304).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_305 : ((2597251/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 305, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 305, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 304, cos960o2c k) + cos960o2c 305 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 304) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_304
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 305 - ((999997/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_305).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_306 : ((519811/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 306, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 306, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 305, cos960o2c k) + cos960o2c 306 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 305) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_305
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 306 - ((119/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_306).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_307 : ((1598977/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 307, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 307, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 306, cos960o2c k) + cos960o2c 307 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 306) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_306
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 307 - ((-499989/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_307).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_308 : ((158239/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 308, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 308, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 307, cos960o2c k) + cos960o2c 308 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 307) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_307
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 308 - ((-16487/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_308).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_309 : ((1290899/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 309, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 309, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 308, cos960o2c k) + cos960o2c 309 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 308) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_308
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 309 - ((249877/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_309).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_310 : ((658239/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 310, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 310, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 309, cos960o2c k) + cos960o2c 310 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 309) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_309
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 310 - ((25629/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_310).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_311 : ((1635753/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 311, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 311, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 310, cos960o2c k) + cos960o2c 311 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 310) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_310
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 311 - ((-997103/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_311).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_312 : ((152981/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 312, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 312, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 311, cos960o2c k) + cos960o2c 312 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 311) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_311
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 312 - ((-105843/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_312).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_313 : ((2519809/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 313, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 313, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 312, cos960o2c k) + cos960o2c 313 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 312) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_312
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 313 - ((990099/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_313).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_314 : ((134963/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 314, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 314, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 313, cos960o2c k) + cos960o2c 314 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 313) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_313
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 314 - ((179551/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_314).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_315 : ((862191/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 315, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 315, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 314, cos960o2c k) + cos960o2c 315 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 314) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_314
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 315 - ((-487389/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_315).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_316 : ((181657/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 316, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 316, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 315, cos960o2c k) + cos960o2c 316 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 315) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_315
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 316 - ((-135513/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_316).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_317 : ((119981/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 317, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 317, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 316, cos960o2c k) + cos960o2c 317 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 316) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_316
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 317 - ((29577/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_317).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_318 : ((555513/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 318, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 318, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 317, cos960o2c k) + cos960o2c 318 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 317) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_317
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 318 - ((75609/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_318).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_319 : ((1877617/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 319, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 319, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 318, cos960o2c k) + cos960o2c 319 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 318) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_318
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 319 - ((-112481/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_319).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_320 : ((1380751/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 320, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 320, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 319, cos960o2c k) + cos960o2c 320 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 319) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_319
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 320 - ((-248383/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_320).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_321 : ((2209937/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 321, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 321, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 320, cos960o2c k) + cos960o2c 321 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 320) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_320
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 321 - ((414643/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_321).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_322 : ((707857/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 322, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 322, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 321, cos960o2c k) + cos960o2c 322 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 321) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_321
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 322 - ((621591/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_322).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_323 : ((1050907/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 323, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 323, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 322, cos960o2c k) + cos960o2c 323 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 322) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_322
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 323 - ((-364757/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_323).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_324 : ((678467/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 324, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 324, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 323, cos960o2c k) + cos960o2c 324 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 323) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_323
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 324 - ((-37239/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_324).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_325 : ((1953197/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 325, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 325, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 324, cos960o2c k) + cos960o2c 325 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 324) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_324
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 325 - ((596363/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_325).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_326 : ((2809351/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 326, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 326, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 325, cos960o2c k) + cos960o2c 326 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 325) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_325
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 326 - ((428127/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_326).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_327 : ((2381349/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 327, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 327, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 326, cos960o2c k) + cos960o2c 327 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 326) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_326
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 327 - ((-213951/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_327).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_328 : ((359379/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 328, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 328, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 327, cos960o2c k) + cos960o2c 328 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 327) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_327
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 328 - ((-943733/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_328).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_329 : ((831443/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 329, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 329, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 328, cos960o2c k) + cos960o2c 329 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 328) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_328
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 329 - ((22547/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_329).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_330 : ((531273/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 330, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 330, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 329, cos960o2c k) + cos960o2c 330 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 329) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_329
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 330 - ((993579/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_330).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_331 : ((532269/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 331, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 331, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 330, cos960o2c k) + cos960o2c 331 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 330) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_330
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 331 - ((127/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_331).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_332 : ((834707/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 332, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 332, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 331, cos960o2c k) + cos960o2c 332 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 331) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_331
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 332 - ((-991831/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_332).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_333 : ((177121/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 333, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 333, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 332, cos960o2c k) + cos960o2c 333 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 332) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_332
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 333 - ((-126173/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_333).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_334 : ((2343057/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 334, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 334, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 333, cos960o2c k) + cos960o2c 334 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 333) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_333
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 334 - ((926189/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_334).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_335 : ((1420963/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 335, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 335, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 334, cos960o2c k) + cos960o2c 335 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 334) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_334
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 335 - ((498969/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_335).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_336 : ((102669/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 336, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 336, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 335, cos960o2c k) + cos960o2c 336 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 335) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_335
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 336 - ((-394223/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_336).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_337 : ((1331169/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 337, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 337, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 336, cos960o2c k) + cos960o2c 337 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 336) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_336
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 337 - ((-722111/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_337).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_338 : ((1908307/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 338, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 338, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 337, cos960o2c k) + cos960o2c 338 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 337) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_337
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 338 - ((288619/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_338).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_339 : ((1401549/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 339, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 339, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 338, cos960o2c k) + cos960o2c 339 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 338) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_338
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 339 - ((894891/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_339).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_340 : ((2502081/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 340, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 340, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 339, cos960o2c k) + cos960o2c 340 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 339) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_339
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 340 - ((-300917/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_340).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_341 : ((756203/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 341, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 341, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 340, cos960o2c k) + cos960o2c 341 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 340) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_340
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 341 - ((-39583/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_341).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_342 : ((1491617/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 342, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 342, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 341, cos960o2c k) + cos960o2c 342 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 341) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_341
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 342 - ((-20689/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_342).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_343 : ((494703/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 343, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 343, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 342, cos960o2c k) + cos960o2c 343 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 342) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_342
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 343 - ((490999/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_343).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_344 : ((2828917/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 344, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 344, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 343, cos960o2c k) + cos960o2c 344 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 343) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_343
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 344 - ((177751/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_344).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_345 : ((1971573/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 345, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 345, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 344, cos960o2c k) + cos960o2c 345 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 344) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_344
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 345 - ((-214311/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_345).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_346 : ((1310259/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 346, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 346, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 345, cos960o2c k) + cos960o2c 346 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 345) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_345
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 346 - ((-330607/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_346).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_347 : ((24069/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 347, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 347, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 346, cos960o2c k) + cos960o2c 347 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 346) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_346
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 347 - ((615361/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_347).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_348 : ((2815469/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 348, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 348, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 347, cos960o2c k) + cos960o2c 348 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 347) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_347
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 348 - ((890049/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_348).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_349 : ((1269551/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 349, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 349, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 348, cos960o2c k) + cos960o2c 349 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 348) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_348
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 349 - ((-276267/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_349).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_350 : ((771201/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 350, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 350, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 349, cos960o2c k) + cos960o2c 350 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 349) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_349
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 350 - ((-4983/5000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_350).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_351 : ((17797/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 351, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 351, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 350, cos960o2c k) + cos960o2c 351 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 350) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_350
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 351 - ((-59271/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_351).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_352 : ((2371609/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 352, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 352, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 351, cos960o2c k) + cos960o2c 352 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 351) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_351
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 352 - ((947949/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_352).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_353 : ((1439879/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 353, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 353, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 352, cos960o2c k) + cos960o2c 353 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 352) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_352
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 353 - ((508249/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_353).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_354 : ((2145299/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 354, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 354, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 353, cos960o2c k) + cos960o2c 354 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 353) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_353
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 354 - ((-734359/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_354).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_355 : ((264871/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 355, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 355, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 354, cos960o2c k) + cos960o2c 355 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 354) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_354
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 355 - ((-205211/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_355).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_356 : ((850997/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 356, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 356, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 355, cos960o2c k) + cos960o2c 356 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 355) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_355
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 356 - ((377739/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_356).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_357 : ((1344323/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 357, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 357, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 356, cos960o2c k) + cos960o2c 357 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 356) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_356
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 357 - ((15418/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_357).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_358 : ((2753683/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 358, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 358, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 357, cos960o2c k) + cos960o2c 358 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 357) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_357
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 358 - ((65137/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_358).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_359 : ((224673/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 359, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 359, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 358, cos960o2c k) + cos960o2c 359 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 358) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_358
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 359 - ((-956199/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_359).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_360 : ((322367/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 360, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 360, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 359, cos960o2c k) + cos960o2c 360 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 359) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_359
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 360 - ((-63477/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_360).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_361 : ((125369/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 361, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 361, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 360, cos960o2c k) + cos960o2c 361 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 360) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_360
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 361 - ((89567/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_361).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_362 : ((571051/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 362, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 362, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 361, cos960o2c k) + cos960o2c 362 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 361) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_361
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 362 - ((849451/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_362).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_363 : ((1275437/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 363, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 363, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 362, cos960o2c k) + cos960o2c 363 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 362) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_362
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 363 - ((-304281/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_363).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_364 : ((776253/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 364, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 364, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 363, cos960o2c k) + cos960o2c 364 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 363) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_363
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 364 - ((-249567/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_364).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_365 : ((1358591/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 365, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 365, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 364, cos960o2c k) + cos960o2c 365 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 364) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_364
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 365 - ((-38763/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_365).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_366 : ((2257819/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 366, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 366, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 365, cos960o2c k) + cos960o2c 366 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 365) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_365
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 366 - ((14052/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_366).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_367 : ((2912341/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 367, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 367, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 366, cos960o2c k) + cos960o2c 367 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 366) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_366
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 367 - ((327311/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_367).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_368 : ((2353849/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 368, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 368, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 367, cos960o2c k) + cos960o2c 368 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 367) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_367
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 368 - ((-69799/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_368).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_369 : ((1405851/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 369, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 369, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 368, cos960o2c k) + cos960o2c 369 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 368) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_368
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 369 - ((-473949/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_369).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_370 : ((364557/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 370, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 370, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 369, cos960o2c k) + cos960o2c 370 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 369) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_369
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 370 - ((52477/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_370).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_371 : ((304177/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 371, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 371, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 370, cos960o2c k) + cos960o2c 371 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 370) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_370
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 371 - ((121911/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_371).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_372 : ((182129/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 372, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 372, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 371, cos960o2c k) + cos960o2c 372 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 371) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_371
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 372 - ((120187/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_372).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_373 : ((1102827/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 373, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 373, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 372, cos960o2c k) + cos960o2c 373 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 372) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_372
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 373 - ((-70831/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_373).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_374 : ((166081/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 374, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 374, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 373, cos960o2c k) + cos960o2c 374 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 373) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_373
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 374 - ((-438453/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_374).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_375 : ((96207/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 375, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 375, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 374, cos960o2c k) + cos960o2c 375 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 374) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_374
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 375 - ((52691/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_375).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_376 : ((1268001/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 376, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 376, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 375, cos960o2c k) + cos960o2c 376 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 375) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_375
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 376 - ((99679/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_376).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_377 : ((45362/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 377, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 377, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 376, cos960o2c k) + cos960o2c 377 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 376) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_376
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 377 - ((183633/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_377).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_378 : ((132661/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 378, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 378, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 377, cos960o2c k) + cos960o2c 378 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 377) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_377
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 378 - ((-195123/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_378).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_379 : ((323283/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 379, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 379, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 378, cos960o2c k) + cos960o2c 379 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 378) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_378
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 379 - ((-25917/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_379).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_380 : ((78799/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 380, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 380, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 379, cos960o2c k) + cos960o2c 380 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 379) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_379
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 380 - ((70737/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_380).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_381 : ((643907/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 381, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 381, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 380, cos960o2c k) + cos960o2c 381 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 380) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_380
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 381 - ((249937/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_381).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_382 : ((290431/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 382, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 382, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 381, cos960o2c k) + cos960o2c 382 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 381) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_381
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 382 - ((164391/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_382).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_383 : ((2108699/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 383, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 383, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 382, cos960o2c k) + cos960o2c 383 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 382) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_382
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 383 - ((-795511/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_383).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_384 : ((64183/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 384, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 384, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 383, cos960o2c k) + cos960o2c 384 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 383) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_383
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 384 - ((-824939/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_384).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_385 : ((1558271/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 385, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 385, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 384, cos960o2c k) + cos960o2c 385 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 384) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_384
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 385 - ((274711/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_385).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_386 : ((319631/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 386, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 386, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 385, cos960o2c k) + cos960o2c 386 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 385) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_385
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 386 - ((998877/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_386).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_387 : ((292441/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 387, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 387, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 386, cos960o2c k) + cos960o2c 387 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 386) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_386
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 387 - ((183731/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_387).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_388 : ((2164867/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 388, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 388, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 387, cos960o2c k) + cos960o2c 388 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 387) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_387
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 388 - ((-759443/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_388).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_389 : ((650269/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 389, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 389, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 388, cos960o2c k) + cos960o2c 389 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 388) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_388
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 389 - ((-864229/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_389).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_390 : ((186007/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 390, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 390, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 389, cos960o2c k) + cos960o2c 390 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 389) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_389
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 390 - ((93809/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_390).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_391 : ((2476293/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 391, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 391, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 390, cos960o2c k) + cos960o2c 391 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 390) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_390
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 391 - ((988337/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_391).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_392 : ((1476759/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 392, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 392, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 391, cos960o2c k) + cos960o2c 392 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 391) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_391
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 392 - ((19093/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_392).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_393 : ((2290031/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 393, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 393, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 392, cos960o2c k) + cos960o2c 393 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 392) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_392
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 393 - ((-663387/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_393).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_394 : ((135919/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 394, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 394, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 393, cos960o2c k) + cos960o2c 394 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 393) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_393
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 394 - ((-930741/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_394).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_395 : ((8621/6250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 395, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 395, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 394, cos960o2c k) + cos960o2c 395 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 394) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_394
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 395 - ((2027/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_395).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_396 : ((1161531/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 396, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 396, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 395, cos960o2c k) + cos960o2c 396 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 395) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_395
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 396 - ((471901/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_396).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_397 : ((592989/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 397, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 397, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 396, cos960o2c k) + cos960o2c 397 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 396) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_396
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 397 - ((641983/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_397).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_398 : ((2476229/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 398, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 398, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 397, cos960o2c k) + cos960o2c 398 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 397) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_397
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 398 - ((-61077/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_398).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_399 : ((148651/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 399, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 399, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 398, cos960o2c k) + cos960o2c 399 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 398) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_398
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 399 - ((-989619/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_399).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_400 : ((252643/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 400, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 400, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 399, cos960o2c k) + cos960o2c 400 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 399) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_399
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 400 - ((-44639/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_400).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_401 : ((208993/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 401, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 401, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 400, cos960o2c k) + cos960o2c 401 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 400) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_400
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 401 - ((165363/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_401).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_402 : ((291623/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 402, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 402, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 401, cos960o2c k) + cos960o2c 402 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 401) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_401
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 402 - ((1033/1250 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_402).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_403 : ((2698021/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 403, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 403, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 402, cos960o2c k) + cos960o2c 403 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 402) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_402
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 403 - ((-218109/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_403).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_404 : ((1710907/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 404, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 404, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 403, cos960o2c k) + cos960o2c 404 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 403) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_403
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 404 - ((-493507/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_404).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_405 : ((595991/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 405, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 405, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 404, cos960o2c k) + cos960o2c 405 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 404) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_404
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 405 - ((-20753/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_405).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_406 : ((71507/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 406, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 406, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 405, cos960o2c k) + cos960o2c 406 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 405) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_405
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 406 - ((595793/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_406).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_407 : ((2756917/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 407, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 407, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 406, cos960o2c k) + cos960o2c 407 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 406) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_406
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 407 - ((484671/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_407).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_408 : ((1450467/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 408, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 408, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 407, cos960o2c k) + cos960o2c 408 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 407) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_407
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 408 - ((144117/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_408).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_409 : ((2043319/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 409, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 409, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 408, cos960o2c k) + cos960o2c 409 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 408) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_408
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 409 - ((-171503/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_409).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_410 : ((1236243/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 410, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 410, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 409, cos960o2c k) + cos960o2c 410 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 409) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_409
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 410 - ((-12609/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_410).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_411 : ((1464427/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 411, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 411, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 410, cos960o2c k) + cos960o2c 411 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 410) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_410
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 411 - ((57071/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_411).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_412 : ((2449221/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 412, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 412, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 411, cos960o2c k) + cos960o2c 412 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 411) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_411
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 412 - ((492447/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_412).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_413 : ((37477/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 413, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 413, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 412, cos960o2c k) + cos960o2c 413 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 412) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_412
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 413 - ((549039/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_413).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_414 : ((490071/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 414, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 414, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 413, cos960o2c k) + cos960o2c 414 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 413) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_413
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 414 - ((-109541/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_414).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_415 : ((292829/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 415, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 415, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 414, cos960o2c k) + cos960o2c 415 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 414) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_414
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 415 - ((-98611/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_415).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_416 : ((1217891/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 416, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 416, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 415, cos960o2c k) + cos960o2c 416 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 415) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_415
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 416 - ((-123077/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_416).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_417 : ((31304/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 417, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 417, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 416, cos960o2c k) + cos960o2c 417 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 416) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_416
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 417 - ((157133/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_417).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_418 : ((577823/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 418, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 418, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 417, cos960o2c k) + cos960o2c 418 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 417) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_417
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 418 - ((885759/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_418).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_419 : ((353777/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 419, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 419, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 418, cos960o2c k) + cos960o2c 419 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 418) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_418
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 419 - ((-58799/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_419).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_420 : ((948487/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 420, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 420, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 419, cos960o2c k) + cos960o2c 420 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 419) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_419
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 420 - ((-466571/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_420).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_421 : ((590789/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 421, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 421, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 420, cos960o2c k) + cos960o2c 421 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 420) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_420
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 421 - ((-22353/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_421).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_422 : ((1516617/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 422, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 422, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 421, cos960o2c k) + cos960o2c 422 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 421) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_421
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 422 - ((335139/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_422).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_423 : ((2512197/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 423, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 423, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 422, cos960o2c k) + cos960o2c 423 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 422) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_422
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 423 - ((6223/6250 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_423).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_424 : ((1508967/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 424, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 424, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 423, cos960o2c k) + cos960o2c 424 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 423) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_423
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 424 - ((505837/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_424).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_425 : ((19623/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 425, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 425, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 424, cos960o2c k) + cos960o2c 425 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 424) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_424
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 425 - ((-564959/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_425).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_426 : ((1465181/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 426, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 426, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 425, cos960o2c k) + cos960o2c 426 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 425) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_425
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 426 - ((-493797/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_426).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_427 : ((9451/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 427, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 427, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 426, cos960o2c k) + cos960o2c 427 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 426) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_426
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 427 - ((-141853/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_427).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_428 : ((961323/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 428, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 428, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 427, cos960o2c k) + cos960o2c 428 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 427) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_427
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 428 - ((741371/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_428).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_429 : ((1424759/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 429, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 429, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 428, cos960o2c k) + cos960o2c 429 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 428) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_428
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 429 - ((231743/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_429).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_430 : ((1459019/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 430, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 430, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 429, cos960o2c k) + cos960o2c 430 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 429) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_429
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 430 - ((3431/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_430).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_431 : ((2052377/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 431, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 431, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 430, cos960o2c k) + cos960o2c 431 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 430) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_430
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 431 - ((-865561/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_431).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_432 : ((305039/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 432, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 432, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 431, cos960o2c k) + cos960o2c 432 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 431) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_431
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 432 - ((-832121/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_432).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_433 : ((1346649/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 433, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 433, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 432, cos960o2c k) + cos960o2c 433 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 432) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_432
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 433 - ((126593/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_433).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_434 : ((2290433/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 434, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 434, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 433, cos960o2c k) + cos960o2c 434 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 433) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_433
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 434 - ((235971/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_434).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_435 : ((60191/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 435, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 435, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 434, cos960o2c k) + cos960o2c 435 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 434) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_434
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 435 - ((719217/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_435).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_436 : ((1357203/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 436, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 436, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 435, cos960o2c k) + cos960o2c 436 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 435) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_435
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 436 - ((-73761/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_436).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_437 : ((432251/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 437, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 437, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 436, cos960o2c k) + cos960o2c 437 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 436) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_436
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 437 - ((-492651/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_437).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_438 : ((225497/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 438, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 438, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 437, cos960o2c k) + cos960o2c 438 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 437) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_437
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 438 - ((-601419/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_438).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_439 : ((780889/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 439, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 439, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 438, cos960o2c k) + cos960o2c 439 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 438) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_438
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 439 - ((434393/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_439).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_440 : ((2561249/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 440, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 440, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 439, cos960o2c k) + cos960o2c 440 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 439) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_439
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 440 - ((999571/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_440).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_441 : ((3049707/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 441, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 441, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 440, cos960o2c k) + cos960o2c 441 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 440) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_440
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 441 - ((244279/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_441).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_442 : ((2504293/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 442, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 442, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 441, cos960o2c k) + cos960o2c 442 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 441) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_441
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 442 - ((-272657/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_442).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_443 : ((301661/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 443, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 443, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 442, cos960o2c k) + cos960o2c 443 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 442) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_442
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 443 - ((-62243/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_443).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_444 : ((1120839/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 444, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 444, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 443, cos960o2c k) + cos960o2c 444 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 443) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_443
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 444 - ((-193683/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_444).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_445 : ((35023/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 445, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 445, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 444, cos960o2c k) + cos960o2c 445 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 444) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_444
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 445 - ((630411/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_445).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_446 : ((2733291/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 446, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 446, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 445, cos960o2c k) + cos960o2c 446 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 445) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_445
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 446 - ((982241/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_446).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_447 : ((607087/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 447, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 447, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 446, cos960o2c k) + cos960o2c 447 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 446) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_446
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 447 - ((75561/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_447).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_448 : ((1171179/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 448, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 448, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 447, cos960o2c k) + cos960o2c 448 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 447) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_447
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 448 - ((-692977/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_448).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_449 : ((1377171/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 449, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 449, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 448, cos960o2c k) + cos960o2c 449 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 448) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_448
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 449 - ((-965087/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_449).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_450 : ((1141391/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 450, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 450, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 449, cos960o2c k) + cos960o2c 450 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 449) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_449
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 450 - ((-1473/6250 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_450).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_451 : ((1877591/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 451, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 451, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 450, cos960o2c k) + cos960o2c 451 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 450) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_450
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 451 - ((7363/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_451).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_452 : ((70669/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 452, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 452, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 451, cos960o2c k) + cos960o2c 452 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 451) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_451
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 452 - ((949269/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_452).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_453 : ((150781/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 453, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 453, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 452, cos960o2c k) + cos960o2c 453 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 452) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_452
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 453 - ((1181/6250 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_453).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_454 : ((225229/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 454, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 454, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 453, cos960o2c k) + cos960o2c 454 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 453) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_453
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 454 - ((-76323/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_454).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_455 : ((1314073/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 455, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 455, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 454, cos960o2c k) + cos960o2c 455 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 454) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_454
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 455 - ((-938117/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_455).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_456 : ((1151339/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 456, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 456, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 455, cos960o2c k) + cos960o2c 456 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 455) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_455
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 456 - ((-81317/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_456).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_457 : ((1927101/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 457, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 457, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 456, cos960o2c k) + cos960o2c 457 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 456) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_456
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 457 - ((387931/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_457).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_458 : ((14303/5000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 458, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 458, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 457, cos960o2c k) + cos960o2c 458 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 457) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_457
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 458 - ((933599/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_458).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_459 : ((3017251/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 459, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 459, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 458, cos960o2c k) + cos960o2c 459 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 458) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_458
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 459 - ((156751/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_459).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_460 : ((112093/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 460, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 460, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 459, cos960o2c k) + cos960o2c 460 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 459) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_459
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 460 - ((-775291/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_460).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_461 : ((1305423/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 461, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 461, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 460, cos960o2c k) + cos960o2c 461 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 460) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_460
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 461 - ((-936337/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_461).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_462 : ((226837/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 462, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 462, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 461, cos960o2c k) + cos960o2c 462 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 461) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_461
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 462 - ((-85569/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_462).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_463 : ((379149/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 463, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 463, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 462, cos960o2c k) + cos960o2c 463 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 462) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_462
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 463 - ((38083/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_463).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_464 : ((710367/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 464, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 464, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 463, cos960o2c k) + cos960o2c 464 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 463) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_463
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 464 - ((945823/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_464).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_465 : ((761657/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 465, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 465, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 464, cos960o2c k) + cos960o2c 465 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 464) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_464
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 465 - ((10263/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_465).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_466 : ((2312383/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 466, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 466, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 465, cos960o2c k) + cos960o2c 466 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 465) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_465
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 466 - ((-146829/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_466).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_467 : ((337983/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 467, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 467, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 466, cos960o2c k) + cos960o2c 467 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 466) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_466
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 467 - ((-960351/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_467).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_468 : ((218653/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 468, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 468, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 467, cos960o2c k) + cos960o2c 468 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 467) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_467
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 468 - ((-258567/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_468).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_469 : ((892137/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 469, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 469, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 468, cos960o2c k) + cos960o2c 469 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 468) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_468
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 469 - ((691109/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_469).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_470 : ((69031/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 470, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 470, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 469, cos960o2c k) + cos960o2c 470 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 469) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_469
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 470 - ((488533/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_470).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_471 : ((3090879/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 471, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 471, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 470, cos960o2c k) + cos960o2c 471 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 470) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_470
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 471 - ((329739/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_471).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_472 : ((615107/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 472, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 472, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 471, cos960o2c k) + cos960o2c 472 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 471) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_471
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 472 - ((-630351/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_472).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_473 : ((183549/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 473, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 473, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 472, cos960o2c k) + cos960o2c 473 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 472) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_472
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 473 - ((-15499/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_473).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_474 : ((525731/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 474, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 474, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 473, cos960o2c k) + cos960o2c 474 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 473) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_473
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 474 - ((-41683/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_474).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_475 : ((1600761/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 475, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 475, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 474, cos960o2c k) + cos960o2c 475 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 474) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_474
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 475 - ((549399/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_475).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_476 : ((520091/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 476, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 476, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 475, cos960o2c k) + cos960o2c 476 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 475) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_475
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 476 - ((499897/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_476).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_477 : ((97413/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 477, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 477, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 476, cos960o2c k) + cos960o2c 477 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 476) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_476
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 477 - ((516861/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_477).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_478 : ((2671301/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 478, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 478, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 477, cos960o2c k) + cos960o2c 478 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 477) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_477
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 478 - ((-89163/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_478).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_479 : ((419193/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 479, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 479, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 478, cos960o2c k) + cos960o2c 479 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 478) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_478
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 479 - ((-994429/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_479).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_480 : ((131441/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 480, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 480, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 479, cos960o2c k) + cos960o2c 480 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 479) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_479
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 480 - ((-78143/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_480).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_481 : ((1369421/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 481, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 481, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 480, cos960o2c k) + cos960o2c 481 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 480) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_480
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 481 - ((317993/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_481).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_482 : ((1169083/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 482, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 482, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 481, cos960o2c k) + cos960o2c 482 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 481) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_481
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 482 - ((193769/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_482).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_483 : ((1536737/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 483, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 483, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 482, cos960o2c k) + cos960o2c 483 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 482) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_482
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 483 - ((45963/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_483).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_484 : ((726907/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 484, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 484, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 483, cos960o2c k) + cos960o2c 484 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 483) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_483
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 484 - ((-82873/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_484).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_485 : ((497963/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 485, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 485, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 484, cos960o2c k) + cos960o2c 485 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 484) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_484
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 485 - ((-228919/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_485).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_486 : ((1152611/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 486, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 486, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 485, cos960o2c k) + cos960o2c 486 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 485) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_485
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 486 - ((-839141/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_486).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_487 : ((1143449/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 487, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 487, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 486, cos960o2c k) + cos960o2c 487 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 486) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_486
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 487 - ((-4531/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_487).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_488 : ((985683/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 488, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 488, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 487, cos960o2c k) + cos960o2c 488 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 487) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_487
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 488 - ((828017/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_488).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_489 : ((2897189/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 489, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 489, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 488, cos960o2c k) + cos960o2c 489 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 488) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_488
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 489 - ((925923/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_489).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_490 : ((3098579/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 490, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 490, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 489, cos960o2c k) + cos960o2c 490 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 489) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_489
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 490 - ((20149/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_490).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_491 : ((2398231/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 491, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 491, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 490, cos960o2c k) + cos960o2c 491 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 490) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_490
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 491 - ((-87531/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_491).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_492 : ((1414567/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 492, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 492, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 491, cos960o2c k) + cos960o2c 492 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 491) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_491
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 492 - ((-245891/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_492).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_493 : ((2529/2500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 493, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 493, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 492, cos960o2c k) + cos960o2c 493 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 492) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_492
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 493 - ((-402867/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_493).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_494 : ((385253/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 494, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 494, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 493, cos960o2c k) + cos960o2c 494 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 493) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_493
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 494 - ((66189/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_494).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_495 : ((101601/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 495, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 495, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 494, cos960o2c k) + cos960o2c 495 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 494) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_494
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 495 - ((999113/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_495).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_496 : ((628093/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 496, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 496, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 495, cos960o2c k) + cos960o2c 496 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 495) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_495
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 496 - ((30027/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_496).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_497 : ((2823339/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 497, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 497, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 496, cos960o2c k) + cos960o2c 497 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 496) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_496
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 497 - ((-158513/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_497).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_498 : ((186313/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 498, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 498, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 497, cos960o2c k) + cos960o2c 498 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 497) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_497
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 498 - ((-960109/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_498).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_499 : ((135641/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 499, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 499, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 498, cos960o2c k) + cos960o2c 499 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 498) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_498
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 499 - ((-388951/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_499).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum960o2_500 : ((1154611/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 500, cos960o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 500, cos960o2c k)
      = (∑ k ∈ Finset.Icc 11 499, cos960o2c k) + cos960o2c 500 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 499) (by norm_num) cos960o2c
    simpa using h
  have hprev := psum960o2_499
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos960o2c 500 - ((69583/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos960o2_br_500).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 16384 in
theorem psum960o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 500 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos960o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum960o2_11
  · exact le_trans (by norm_num) psum960o2_12
  · exact le_trans (by norm_num) psum960o2_13
  · exact le_trans (by norm_num) psum960o2_14
  · exact le_trans (by norm_num) psum960o2_15
  · exact le_trans (by norm_num) psum960o2_16
  · exact le_trans (by norm_num) psum960o2_17
  · exact le_trans (by norm_num) psum960o2_18
  · exact le_trans (by norm_num) psum960o2_19
  · exact le_trans (by norm_num) psum960o2_20
  · exact le_trans (by norm_num) psum960o2_21
  · exact le_trans (by norm_num) psum960o2_22
  · exact le_trans (by norm_num) psum960o2_23
  · exact le_trans (by norm_num) psum960o2_24
  · exact le_trans (by norm_num) psum960o2_25
  · exact le_trans (by norm_num) psum960o2_26
  · exact le_trans (by norm_num) psum960o2_27
  · exact le_trans (by norm_num) psum960o2_28
  · exact le_trans (by norm_num) psum960o2_29
  · exact le_trans (by norm_num) psum960o2_30
  · exact le_trans (by norm_num) psum960o2_31
  · exact le_trans (by norm_num) psum960o2_32
  · exact le_trans (by norm_num) psum960o2_33
  · exact le_trans (by norm_num) psum960o2_34
  · exact le_trans (by norm_num) psum960o2_35
  · exact le_trans (by norm_num) psum960o2_36
  · exact le_trans (by norm_num) psum960o2_37
  · exact le_trans (by norm_num) psum960o2_38
  · exact le_trans (by norm_num) psum960o2_39
  · exact le_trans (by norm_num) psum960o2_40
  · exact le_trans (by norm_num) psum960o2_41
  · exact le_trans (by norm_num) psum960o2_42
  · exact le_trans (by norm_num) psum960o2_43
  · exact le_trans (by norm_num) psum960o2_44
  · exact le_trans (by norm_num) psum960o2_45
  · exact le_trans (by norm_num) psum960o2_46
  · exact le_trans (by norm_num) psum960o2_47
  · exact le_trans (by norm_num) psum960o2_48
  · exact le_trans (by norm_num) psum960o2_49
  · exact le_trans (by norm_num) psum960o2_50
  · exact le_trans (by norm_num) psum960o2_51
  · exact le_trans (by norm_num) psum960o2_52
  · exact le_trans (by norm_num) psum960o2_53
  · exact le_trans (by norm_num) psum960o2_54
  · exact le_trans (by norm_num) psum960o2_55
  · exact le_trans (by norm_num) psum960o2_56
  · exact le_trans (by norm_num) psum960o2_57
  · exact le_trans (by norm_num) psum960o2_58
  · exact le_trans (by norm_num) psum960o2_59
  · exact le_trans (by norm_num) psum960o2_60
  · exact le_trans (by norm_num) psum960o2_61
  · exact le_trans (by norm_num) psum960o2_62
  · exact le_trans (by norm_num) psum960o2_63
  · exact le_trans (by norm_num) psum960o2_64
  · exact le_trans (by norm_num) psum960o2_65
  · exact le_trans (by norm_num) psum960o2_66
  · exact le_trans (by norm_num) psum960o2_67
  · exact le_trans (by norm_num) psum960o2_68
  · exact le_trans (by norm_num) psum960o2_69
  · exact le_trans (by norm_num) psum960o2_70
  · exact le_trans (by norm_num) psum960o2_71
  · exact le_trans (by norm_num) psum960o2_72
  · exact le_trans (by norm_num) psum960o2_73
  · exact le_trans (by norm_num) psum960o2_74
  · exact le_trans (by norm_num) psum960o2_75
  · exact le_trans (by norm_num) psum960o2_76
  · exact le_trans (by norm_num) psum960o2_77
  · exact le_trans (by norm_num) psum960o2_78
  · exact le_trans (by norm_num) psum960o2_79
  · exact le_trans (by norm_num) psum960o2_80
  · exact le_trans (by norm_num) psum960o2_81
  · exact le_trans (by norm_num) psum960o2_82
  · exact le_trans (by norm_num) psum960o2_83
  · exact le_trans (by norm_num) psum960o2_84
  · exact le_trans (by norm_num) psum960o2_85
  · exact le_trans (by norm_num) psum960o2_86
  · exact le_trans (by norm_num) psum960o2_87
  · exact le_trans (by norm_num) psum960o2_88
  · exact le_trans (by norm_num) psum960o2_89
  · exact le_trans (by norm_num) psum960o2_90
  · exact le_trans (by norm_num) psum960o2_91
  · exact le_trans (by norm_num) psum960o2_92
  · exact le_trans (by norm_num) psum960o2_93
  · exact le_trans (by norm_num) psum960o2_94
  · exact le_trans (by norm_num) psum960o2_95
  · exact le_trans (by norm_num) psum960o2_96
  · exact le_trans (by norm_num) psum960o2_97
  · exact le_trans (by norm_num) psum960o2_98
  · exact le_trans (by norm_num) psum960o2_99
  · exact le_trans (by norm_num) psum960o2_100
  · exact le_trans (by norm_num) psum960o2_101
  · exact le_trans (by norm_num) psum960o2_102
  · exact le_trans (by norm_num) psum960o2_103
  · exact le_trans (by norm_num) psum960o2_104
  · exact le_trans (by norm_num) psum960o2_105
  · exact le_trans (by norm_num) psum960o2_106
  · exact le_trans (by norm_num) psum960o2_107
  · exact le_trans (by norm_num) psum960o2_108
  · exact le_trans (by norm_num) psum960o2_109
  · exact le_trans (by norm_num) psum960o2_110
  · exact le_trans (by norm_num) psum960o2_111
  · exact le_trans (by norm_num) psum960o2_112
  · exact le_trans (by norm_num) psum960o2_113
  · exact le_trans (by norm_num) psum960o2_114
  · exact le_trans (by norm_num) psum960o2_115
  · exact le_trans (by norm_num) psum960o2_116
  · exact le_trans (by norm_num) psum960o2_117
  · exact le_trans (by norm_num) psum960o2_118
  · exact le_trans (by norm_num) psum960o2_119
  · exact le_trans (by norm_num) psum960o2_120
  · exact le_trans (by norm_num) psum960o2_121
  · exact le_trans (by norm_num) psum960o2_122
  · exact le_trans (by norm_num) psum960o2_123
  · exact le_trans (by norm_num) psum960o2_124
  · exact le_trans (by norm_num) psum960o2_125
  · exact le_trans (by norm_num) psum960o2_126
  · exact le_trans (by norm_num) psum960o2_127
  · exact le_trans (by norm_num) psum960o2_128
  · exact le_trans (by norm_num) psum960o2_129
  · exact le_trans (by norm_num) psum960o2_130
  · exact le_trans (by norm_num) psum960o2_131
  · exact le_trans (by norm_num) psum960o2_132
  · exact le_trans (by norm_num) psum960o2_133
  · exact le_trans (by norm_num) psum960o2_134
  · exact le_trans (by norm_num) psum960o2_135
  · exact le_trans (by norm_num) psum960o2_136
  · exact le_trans (by norm_num) psum960o2_137
  · exact le_trans (by norm_num) psum960o2_138
  · exact le_trans (by norm_num) psum960o2_139
  · exact le_trans (by norm_num) psum960o2_140
  · exact le_trans (by norm_num) psum960o2_141
  · exact le_trans (by norm_num) psum960o2_142
  · exact le_trans (by norm_num) psum960o2_143
  · exact le_trans (by norm_num) psum960o2_144
  · exact le_trans (by norm_num) psum960o2_145
  · exact le_trans (by norm_num) psum960o2_146
  · exact le_trans (by norm_num) psum960o2_147
  · exact le_trans (by norm_num) psum960o2_148
  · exact le_trans (by norm_num) psum960o2_149
  · exact le_trans (by norm_num) psum960o2_150
  · exact le_trans (by norm_num) psum960o2_151
  · exact le_trans (by norm_num) psum960o2_152
  · exact le_trans (by norm_num) psum960o2_153
  · exact le_trans (by norm_num) psum960o2_154
  · exact le_trans (by norm_num) psum960o2_155
  · exact le_trans (by norm_num) psum960o2_156
  · exact le_trans (by norm_num) psum960o2_157
  · exact le_trans (by norm_num) psum960o2_158
  · exact le_trans (by norm_num) psum960o2_159
  · exact le_trans (by norm_num) psum960o2_160
  · exact le_trans (by norm_num) psum960o2_161
  · exact le_trans (by norm_num) psum960o2_162
  · exact le_trans (by norm_num) psum960o2_163
  · exact le_trans (by norm_num) psum960o2_164
  · exact le_trans (by norm_num) psum960o2_165
  · exact le_trans (by norm_num) psum960o2_166
  · exact le_trans (by norm_num) psum960o2_167
  · exact le_trans (by norm_num) psum960o2_168
  · exact le_trans (by norm_num) psum960o2_169
  · exact le_trans (by norm_num) psum960o2_170
  · exact le_trans (by norm_num) psum960o2_171
  · exact le_trans (by norm_num) psum960o2_172
  · exact le_trans (by norm_num) psum960o2_173
  · exact le_trans (by norm_num) psum960o2_174
  · exact le_trans (by norm_num) psum960o2_175
  · exact le_trans (by norm_num) psum960o2_176
  · exact le_trans (by norm_num) psum960o2_177
  · exact le_trans (by norm_num) psum960o2_178
  · exact le_trans (by norm_num) psum960o2_179
  · exact le_trans (by norm_num) psum960o2_180
  · exact le_trans (by norm_num) psum960o2_181
  · exact le_trans (by norm_num) psum960o2_182
  · exact le_trans (by norm_num) psum960o2_183
  · exact le_trans (by norm_num) psum960o2_184
  · exact le_trans (by norm_num) psum960o2_185
  · exact le_trans (by norm_num) psum960o2_186
  · exact le_trans (by norm_num) psum960o2_187
  · exact le_trans (by norm_num) psum960o2_188
  · exact le_trans (by norm_num) psum960o2_189
  · exact le_trans (by norm_num) psum960o2_190
  · exact le_trans (by norm_num) psum960o2_191
  · exact le_trans (by norm_num) psum960o2_192
  · exact le_trans (by norm_num) psum960o2_193
  · exact le_trans (by norm_num) psum960o2_194
  · exact le_trans (by norm_num) psum960o2_195
  · exact le_trans (by norm_num) psum960o2_196
  · exact le_trans (by norm_num) psum960o2_197
  · exact le_trans (by norm_num) psum960o2_198
  · exact le_trans (by norm_num) psum960o2_199
  · exact le_trans (by norm_num) psum960o2_200
  · exact le_trans (by norm_num) psum960o2_201
  · exact le_trans (by norm_num) psum960o2_202
  · exact le_trans (by norm_num) psum960o2_203
  · exact le_trans (by norm_num) psum960o2_204
  · exact le_trans (by norm_num) psum960o2_205
  · exact le_trans (by norm_num) psum960o2_206
  · exact le_trans (by norm_num) psum960o2_207
  · exact le_trans (by norm_num) psum960o2_208
  · exact le_trans (by norm_num) psum960o2_209
  · exact le_trans (by norm_num) psum960o2_210
  · exact le_trans (by norm_num) psum960o2_211
  · exact le_trans (by norm_num) psum960o2_212
  · exact le_trans (by norm_num) psum960o2_213
  · exact le_trans (by norm_num) psum960o2_214
  · exact le_trans (by norm_num) psum960o2_215
  · exact le_trans (by norm_num) psum960o2_216
  · exact le_trans (by norm_num) psum960o2_217
  · exact le_trans (by norm_num) psum960o2_218
  · exact le_trans (by norm_num) psum960o2_219
  · exact le_trans (by norm_num) psum960o2_220
  · exact le_trans (by norm_num) psum960o2_221
  · exact le_trans (by norm_num) psum960o2_222
  · exact le_trans (by norm_num) psum960o2_223
  · exact le_trans (by norm_num) psum960o2_224
  · exact le_trans (by norm_num) psum960o2_225
  · exact le_trans (by norm_num) psum960o2_226
  · exact le_trans (by norm_num) psum960o2_227
  · exact le_trans (by norm_num) psum960o2_228
  · exact le_trans (by norm_num) psum960o2_229
  · exact le_trans (by norm_num) psum960o2_230
  · exact le_trans (by norm_num) psum960o2_231
  · exact le_trans (by norm_num) psum960o2_232
  · exact le_trans (by norm_num) psum960o2_233
  · exact le_trans (by norm_num) psum960o2_234
  · exact le_trans (by norm_num) psum960o2_235
  · exact le_trans (by norm_num) psum960o2_236
  · exact le_trans (by norm_num) psum960o2_237
  · exact le_trans (by norm_num) psum960o2_238
  · exact le_trans (by norm_num) psum960o2_239
  · exact le_trans (by norm_num) psum960o2_240
  · exact le_trans (by norm_num) psum960o2_241
  · exact le_trans (by norm_num) psum960o2_242
  · exact le_trans (by norm_num) psum960o2_243
  · exact le_trans (by norm_num) psum960o2_244
  · exact le_trans (by norm_num) psum960o2_245
  · exact le_trans (by norm_num) psum960o2_246
  · exact le_trans (by norm_num) psum960o2_247
  · exact le_trans (by norm_num) psum960o2_248
  · exact le_trans (by norm_num) psum960o2_249
  · exact le_trans (by norm_num) psum960o2_250
  · exact le_trans (by norm_num) psum960o2_251
  · exact le_trans (by norm_num) psum960o2_252
  · exact le_trans (by norm_num) psum960o2_253
  · exact le_trans (by norm_num) psum960o2_254
  · exact le_trans (by norm_num) psum960o2_255
  · exact le_trans (by norm_num) psum960o2_256
  · exact le_trans (by norm_num) psum960o2_257
  · exact le_trans (by norm_num) psum960o2_258
  · exact le_trans (by norm_num) psum960o2_259
  · exact le_trans (by norm_num) psum960o2_260
  · exact le_trans (by norm_num) psum960o2_261
  · exact le_trans (by norm_num) psum960o2_262
  · exact le_trans (by norm_num) psum960o2_263
  · exact le_trans (by norm_num) psum960o2_264
  · exact le_trans (by norm_num) psum960o2_265
  · exact le_trans (by norm_num) psum960o2_266
  · exact le_trans (by norm_num) psum960o2_267
  · exact le_trans (by norm_num) psum960o2_268
  · exact le_trans (by norm_num) psum960o2_269
  · exact le_trans (by norm_num) psum960o2_270
  · exact le_trans (by norm_num) psum960o2_271
  · exact le_trans (by norm_num) psum960o2_272
  · exact le_trans (by norm_num) psum960o2_273
  · exact le_trans (by norm_num) psum960o2_274
  · exact le_trans (by norm_num) psum960o2_275
  · exact le_trans (by norm_num) psum960o2_276
  · exact le_trans (by norm_num) psum960o2_277
  · exact le_trans (by norm_num) psum960o2_278
  · exact le_trans (by norm_num) psum960o2_279
  · exact le_trans (by norm_num) psum960o2_280
  · exact le_trans (by norm_num) psum960o2_281
  · exact le_trans (by norm_num) psum960o2_282
  · exact le_trans (by norm_num) psum960o2_283
  · exact le_trans (by norm_num) psum960o2_284
  · exact le_trans (by norm_num) psum960o2_285
  · exact le_trans (by norm_num) psum960o2_286
  · exact le_trans (by norm_num) psum960o2_287
  · exact le_trans (by norm_num) psum960o2_288
  · exact le_trans (by norm_num) psum960o2_289
  · exact le_trans (by norm_num) psum960o2_290
  · exact le_trans (by norm_num) psum960o2_291
  · exact le_trans (by norm_num) psum960o2_292
  · exact le_trans (by norm_num) psum960o2_293
  · exact le_trans (by norm_num) psum960o2_294
  · exact le_trans (by norm_num) psum960o2_295
  · exact le_trans (by norm_num) psum960o2_296
  · exact le_trans (by norm_num) psum960o2_297
  · exact le_trans (by norm_num) psum960o2_298
  · exact le_trans (by norm_num) psum960o2_299
  · exact le_trans (by norm_num) psum960o2_300
  · exact le_trans (by norm_num) psum960o2_301
  · exact le_trans (by norm_num) psum960o2_302
  · exact le_trans (by norm_num) psum960o2_303
  · exact le_trans (by norm_num) psum960o2_304
  · exact le_trans (by norm_num) psum960o2_305
  · exact le_trans (by norm_num) psum960o2_306
  · exact le_trans (by norm_num) psum960o2_307
  · exact le_trans (by norm_num) psum960o2_308
  · exact le_trans (by norm_num) psum960o2_309
  · exact le_trans (by norm_num) psum960o2_310
  · exact le_trans (by norm_num) psum960o2_311
  · exact le_trans (by norm_num) psum960o2_312
  · exact le_trans (by norm_num) psum960o2_313
  · exact le_trans (by norm_num) psum960o2_314
  · exact le_trans (by norm_num) psum960o2_315
  · exact le_trans (by norm_num) psum960o2_316
  · exact le_trans (by norm_num) psum960o2_317
  · exact le_trans (by norm_num) psum960o2_318
  · exact le_trans (by norm_num) psum960o2_319
  · exact le_trans (by norm_num) psum960o2_320
  · exact le_trans (by norm_num) psum960o2_321
  · exact le_trans (by norm_num) psum960o2_322
  · exact le_trans (by norm_num) psum960o2_323
  · exact le_trans (by norm_num) psum960o2_324
  · exact le_trans (by norm_num) psum960o2_325
  · exact le_trans (by norm_num) psum960o2_326
  · exact le_trans (by norm_num) psum960o2_327
  · exact le_trans (by norm_num) psum960o2_328
  · exact le_trans (by norm_num) psum960o2_329
  · exact le_trans (by norm_num) psum960o2_330
  · exact le_trans (by norm_num) psum960o2_331
  · exact le_trans (by norm_num) psum960o2_332
  · exact le_trans (by norm_num) psum960o2_333
  · exact le_trans (by norm_num) psum960o2_334
  · exact le_trans (by norm_num) psum960o2_335
  · exact le_trans (by norm_num) psum960o2_336
  · exact le_trans (by norm_num) psum960o2_337
  · exact le_trans (by norm_num) psum960o2_338
  · exact le_trans (by norm_num) psum960o2_339
  · exact le_trans (by norm_num) psum960o2_340
  · exact le_trans (by norm_num) psum960o2_341
  · exact le_trans (by norm_num) psum960o2_342
  · exact le_trans (by norm_num) psum960o2_343
  · exact le_trans (by norm_num) psum960o2_344
  · exact le_trans (by norm_num) psum960o2_345
  · exact le_trans (by norm_num) psum960o2_346
  · exact le_trans (by norm_num) psum960o2_347
  · exact le_trans (by norm_num) psum960o2_348
  · exact le_trans (by norm_num) psum960o2_349
  · exact le_trans (by norm_num) psum960o2_350
  · exact le_trans (by norm_num) psum960o2_351
  · exact le_trans (by norm_num) psum960o2_352
  · exact le_trans (by norm_num) psum960o2_353
  · exact le_trans (by norm_num) psum960o2_354
  · exact le_trans (by norm_num) psum960o2_355
  · exact le_trans (by norm_num) psum960o2_356
  · exact le_trans (by norm_num) psum960o2_357
  · exact le_trans (by norm_num) psum960o2_358
  · exact le_trans (by norm_num) psum960o2_359
  · exact le_trans (by norm_num) psum960o2_360
  · exact le_trans (by norm_num) psum960o2_361
  · exact le_trans (by norm_num) psum960o2_362
  · exact le_trans (by norm_num) psum960o2_363
  · exact le_trans (by norm_num) psum960o2_364
  · exact le_trans (by norm_num) psum960o2_365
  · exact le_trans (by norm_num) psum960o2_366
  · exact le_trans (by norm_num) psum960o2_367
  · exact le_trans (by norm_num) psum960o2_368
  · exact le_trans (by norm_num) psum960o2_369
  · exact le_trans (by norm_num) psum960o2_370
  · exact le_trans (by norm_num) psum960o2_371
  · exact le_trans (by norm_num) psum960o2_372
  · exact le_trans (by norm_num) psum960o2_373
  · exact le_trans (by norm_num) psum960o2_374
  · exact le_trans (by norm_num) psum960o2_375
  · exact le_trans (by norm_num) psum960o2_376
  · exact le_trans (by norm_num) psum960o2_377
  · exact le_trans (by norm_num) psum960o2_378
  · exact le_trans (by norm_num) psum960o2_379
  · exact le_trans (by norm_num) psum960o2_380
  · exact le_trans (by norm_num) psum960o2_381
  · exact le_trans (by norm_num) psum960o2_382
  · exact le_trans (by norm_num) psum960o2_383
  · exact le_trans (by norm_num) psum960o2_384
  · exact le_trans (by norm_num) psum960o2_385
  · exact le_trans (by norm_num) psum960o2_386
  · exact le_trans (by norm_num) psum960o2_387
  · exact le_trans (by norm_num) psum960o2_388
  · exact le_trans (by norm_num) psum960o2_389
  · exact le_trans (by norm_num) psum960o2_390
  · exact le_trans (by norm_num) psum960o2_391
  · exact le_trans (by norm_num) psum960o2_392
  · exact le_trans (by norm_num) psum960o2_393
  · exact le_trans (by norm_num) psum960o2_394
  · exact le_trans (by norm_num) psum960o2_395
  · exact le_trans (by norm_num) psum960o2_396
  · exact le_trans (by norm_num) psum960o2_397
  · exact le_trans (by norm_num) psum960o2_398
  · exact le_trans (by norm_num) psum960o2_399
  · exact le_trans (by norm_num) psum960o2_400
  · exact le_trans (by norm_num) psum960o2_401
  · exact le_trans (by norm_num) psum960o2_402
  · exact le_trans (by norm_num) psum960o2_403
  · exact le_trans (by norm_num) psum960o2_404
  · exact le_trans (by norm_num) psum960o2_405
  · exact le_trans (by norm_num) psum960o2_406
  · exact le_trans (by norm_num) psum960o2_407
  · exact le_trans (by norm_num) psum960o2_408
  · exact le_trans (by norm_num) psum960o2_409
  · exact le_trans (by norm_num) psum960o2_410
  · exact le_trans (by norm_num) psum960o2_411
  · exact le_trans (by norm_num) psum960o2_412
  · exact le_trans (by norm_num) psum960o2_413
  · exact le_trans (by norm_num) psum960o2_414
  · exact le_trans (by norm_num) psum960o2_415
  · exact le_trans (by norm_num) psum960o2_416
  · exact le_trans (by norm_num) psum960o2_417
  · exact le_trans (by norm_num) psum960o2_418
  · exact le_trans (by norm_num) psum960o2_419
  · exact le_trans (by norm_num) psum960o2_420
  · exact le_trans (by norm_num) psum960o2_421
  · exact le_trans (by norm_num) psum960o2_422
  · exact le_trans (by norm_num) psum960o2_423
  · exact le_trans (by norm_num) psum960o2_424
  · exact le_trans (by norm_num) psum960o2_425
  · exact le_trans (by norm_num) psum960o2_426
  · exact le_trans (by norm_num) psum960o2_427
  · exact le_trans (by norm_num) psum960o2_428
  · exact le_trans (by norm_num) psum960o2_429
  · exact le_trans (by norm_num) psum960o2_430
  · exact le_trans (by norm_num) psum960o2_431
  · exact le_trans (by norm_num) psum960o2_432
  · exact le_trans (by norm_num) psum960o2_433
  · exact le_trans (by norm_num) psum960o2_434
  · exact le_trans (by norm_num) psum960o2_435
  · exact le_trans (by norm_num) psum960o2_436
  · exact le_trans (by norm_num) psum960o2_437
  · exact le_trans (by norm_num) psum960o2_438
  · exact le_trans (by norm_num) psum960o2_439
  · exact le_trans (by norm_num) psum960o2_440
  · exact le_trans (by norm_num) psum960o2_441
  · exact le_trans (by norm_num) psum960o2_442
  · exact le_trans (by norm_num) psum960o2_443
  · exact le_trans (by norm_num) psum960o2_444
  · exact le_trans (by norm_num) psum960o2_445
  · exact le_trans (by norm_num) psum960o2_446
  · exact le_trans (by norm_num) psum960o2_447
  · exact le_trans (by norm_num) psum960o2_448
  · exact le_trans (by norm_num) psum960o2_449
  · exact le_trans (by norm_num) psum960o2_450
  · exact le_trans (by norm_num) psum960o2_451
  · exact le_trans (by norm_num) psum960o2_452
  · exact le_trans (by norm_num) psum960o2_453
  · exact le_trans (by norm_num) psum960o2_454
  · exact le_trans (by norm_num) psum960o2_455
  · exact le_trans (by norm_num) psum960o2_456
  · exact le_trans (by norm_num) psum960o2_457
  · exact le_trans (by norm_num) psum960o2_458
  · exact le_trans (by norm_num) psum960o2_459
  · exact le_trans (by norm_num) psum960o2_460
  · exact le_trans (by norm_num) psum960o2_461
  · exact le_trans (by norm_num) psum960o2_462
  · exact le_trans (by norm_num) psum960o2_463
  · exact le_trans (by norm_num) psum960o2_464
  · exact le_trans (by norm_num) psum960o2_465
  · exact le_trans (by norm_num) psum960o2_466
  · exact le_trans (by norm_num) psum960o2_467
  · exact le_trans (by norm_num) psum960o2_468
  · exact le_trans (by norm_num) psum960o2_469
  · exact le_trans (by norm_num) psum960o2_470
  · exact le_trans (by norm_num) psum960o2_471
  · exact le_trans (by norm_num) psum960o2_472
  · exact le_trans (by norm_num) psum960o2_473
  · exact le_trans (by norm_num) psum960o2_474
  · exact le_trans (by norm_num) psum960o2_475
  · exact le_trans (by norm_num) psum960o2_476
  · exact le_trans (by norm_num) psum960o2_477
  · exact le_trans (by norm_num) psum960o2_478
  · exact le_trans (by norm_num) psum960o2_479
  · exact le_trans (by norm_num) psum960o2_480
  · exact le_trans (by norm_num) psum960o2_481
  · exact le_trans (by norm_num) psum960o2_482
  · exact le_trans (by norm_num) psum960o2_483
  · exact le_trans (by norm_num) psum960o2_484
  · exact le_trans (by norm_num) psum960o2_485
  · exact le_trans (by norm_num) psum960o2_486
  · exact le_trans (by norm_num) psum960o2_487
  · exact le_trans (by norm_num) psum960o2_488
  · exact le_trans (by norm_num) psum960o2_489
  · exact le_trans (by norm_num) psum960o2_490
  · exact le_trans (by norm_num) psum960o2_491
  · exact le_trans (by norm_num) psum960o2_492
  · exact le_trans (by norm_num) psum960o2_493
  · exact le_trans (by norm_num) psum960o2_494
  · exact le_trans (by norm_num) psum960o2_495
  · exact le_trans (by norm_num) psum960o2_496
  · exact le_trans (by norm_num) psum960o2_497
  · exact le_trans (by norm_num) psum960o2_498
  · exact le_trans (by norm_num) psum960o2_499
  · exact le_trans (by norm_num) psum960o2_500

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum960o2_floor
#print axioms CriticalLinePhasor.DVP.psum960o2_500
end AxiomAudit
