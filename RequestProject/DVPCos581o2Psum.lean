import RequestProject.DVPCos581o2Table

/-!
# The cosine partial-sum floor, `t = 581/2` (N = 500)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 581/2` segment certificate. -/
def cos581o2c (n : ℕ) : ℝ := Real.cos (((581:ℕ):ℝ) * (Real.log n / 2))

theorem psum581o2_11 : ((41477/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos581o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 11 - ((165933/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum581o2_12 : ((22309/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos581o2c k) + cos581o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_11
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 12 - ((191061/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_13 : ((116119/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos581o2c k) + cos581o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_12
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 13 - ((-847081/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_14 : ((78787/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos581o2c k) + cos581o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_13
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 14 - ((199049/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_15 : ((1852343/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos581o2c k) + cos581o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_14
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 15 - ((276703/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_16 : ((2224541/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos581o2c k) + cos581o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_15
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 16 - ((186149/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_17 : ((3223251/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos581o2c k) + cos581o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_16
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 17 - ((99881/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_18 : ((2561483/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos581o2c k) + cos581o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_17
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 18 - ((-165417/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_19 : ((3224131/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos581o2c k) + cos581o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_18
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 19 - ((165687/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_20 : ((2224793/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos581o2c k) + cos581o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_19
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 20 - ((-499619/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_21 : ((2300061/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos581o2c k) + cos581o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_20
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 21 - ((9421/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_22 : ((3153703/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos581o2c k) + cos581o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_21
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 22 - ((426871/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_23 : ((516689/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos581o2c k) + cos581o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_22
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 23 - ((979909/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_24 : ((2526533/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos581o2c k) + cos581o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_23
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 24 - ((459827/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_25 : ((2748287/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos581o2c k) + cos581o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_24
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 25 - ((55451/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_26 : ((605283/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos581o2c k) + cos581o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_25
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 26 - ((-65421/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_27 : ((4107181/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos581o2c k) + cos581o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_26
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 27 - ((-734983/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_28 : ((2515061/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos581o2c k) + cos581o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_27
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 28 - ((923041/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_29 : ((4634471/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos581o2c k) + cos581o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_28
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 29 - ((-395551/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_30 : ((4617431/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos581o2c k) + cos581o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_29
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 30 - ((-847/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_31 : ((4734689/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos581o2c k) + cos581o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_30
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 31 - ((58679/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_32 : ((2409321/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos581o2c k) + cos581o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_31
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 32 - ((84053/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_33 : ((855819/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos581o2c k) + cos581o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_32
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 33 - ((-539447/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_34 : ((5248269/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos581o2c k) + cos581o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_33
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 34 - ((484637/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_35 : ((2260077/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos581o2c k) + cos581o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_34
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 35 - ((-145603/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_36 : ((4107087/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos581o2c k) + cos581o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_35
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 36 - ((-412967/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_37 : ((2528067/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos581o2c k) + cos581o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_36
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 37 - ((949147/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_38 : ((2735157/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos581o2c k) + cos581o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_37
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 38 - ((10357/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_39 : ((4728551/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos581o2c k) + cos581o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_38
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 39 - ((-741663/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_40 : ((3784497/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos581o2c k) + cos581o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_39
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 40 - ((-471977/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_41 : ((3446769/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos581o2c k) + cos581o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_40
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 41 - ((-84407/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_42 : ((3810867/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos581o2c k) + cos581o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_41
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 42 - ((182099/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_43 : ((2304753/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos581o2c k) + cos581o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_42
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 43 - ((798739/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_44 : ((1115647/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos581o2c k) + cos581o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_43
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 44 - ((968829/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_45 : ((3289061/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos581o2c k) + cos581o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_44
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 45 - ((999987/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_46 : ((946671/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos581o2c k) + cos581o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_45
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 46 - ((497673/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_47 : ((4285707/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos581o2c k) + cos581o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_46
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 47 - ((499073/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_48 : ((9565673/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos581o2c k) + cos581o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_47
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 48 - ((994359/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_49 : ((26217/2500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos581o2c k) + cos581o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_48
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 49 - ((921227/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_50 : ((11173409/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos581o2c k) + cos581o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_49
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 50 - ((686709/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_51 : ((11397801/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos581o2c k) + cos581o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_50
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 51 - ((56123/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_52 : ((5496887/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos581o2c k) + cos581o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_51
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 52 - ((-403927/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_53 : ((10074693/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos581o2c k) + cos581o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_52
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 53 - ((-918981/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_54 : ((9173201/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos581o2c k) + cos581o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_53
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 54 - ((-56337/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_55 : ((9003719/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos581o2c k) + cos581o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_54
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 55 - ((-84691/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_56 : ((9773471/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos581o2c k) + cos581o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_55
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 56 - ((192463/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_57 : ((5337069/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos581o2c k) + cos581o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_56
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 57 - ((900767/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_58 : ((264123/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos581o2c k) + cos581o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_57
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 58 - ((-54559/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_59 : ((9575199/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos581o2c k) + cos581o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_58
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 59 - ((-989621/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_60 : ((4632987/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos581o2c k) + cos581o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_59
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 60 - ((-2473/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_61 : ((10185509/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos581o2c k) + cos581o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_60
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 61 - ((183927/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_62 : ((1323567/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos581o2c k) + cos581o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_61
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 62 - ((403127/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_63 : ((9649289/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos581o2c k) + cos581o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_62
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 63 - ((-939147/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_64 : ((589853/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos581o2c k) + cos581o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_63
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 64 - ((-211541/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_65 : ((10437537/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos581o2c k) + cos581o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_64
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 65 - ((999989/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_66 : ((10168347/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos581o2c k) + cos581o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_65
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 66 - ((-26909/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_67 : ((116903/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos581o2c k) + cos581o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_66
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 67 - ((-816007/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_68 : ((5103409/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos581o2c k) + cos581o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_67
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 68 - ((427339/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_69 : ((5140539/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos581o2c k) + cos581o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_68
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 69 - ((1859/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_70 : ((4692029/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos581o2c k) + cos581o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_69
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 70 - ((-22423/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_71 : ((2562821/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos581o2c k) + cos581o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_70
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 71 - ((433663/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_72 : ((5061579/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos581o2c k) + cos581o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_71
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 72 - ((-64013/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_73 : ((9451001/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos581o2c k) + cos581o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_72
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 73 - ((-672057/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_74 : ((10450637/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos581o2c k) + cos581o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_73
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 74 - ((124967/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_75 : ((4854299/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos581o2c k) + cos581o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_74
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 75 - ((-741939/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_76 : ((9837953/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos581o2c k) + cos581o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_75
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 76 - ((25891/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_77 : ((10339959/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos581o2c k) + cos581o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_76
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 77 - ((251053/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_78 : ((9434223/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos581o2c k) + cos581o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_77
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 78 - ((-226409/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_79 : ((10426791/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos581o2c k) + cos581o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_78
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 79 - ((248167/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_80 : ((9620859/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos581o2c k) + cos581o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_79
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 80 - ((-100729/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_81 : ((2518397/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos581o2c k) + cos581o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_80
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 81 - ((452829/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_82 : ((10026441/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos581o2c k) + cos581o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_81
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 82 - ((-47047/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_83 : ((969983/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos581o2c k) + cos581o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_82
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 83 - ((-326511/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_84 : ((5160393/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos581o2c k) + cos581o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_83
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 84 - ((9704/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_85 : ((9497839/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos581o2c k) + cos581o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_84
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 85 - ((-822847/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_86 : ((5218847/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos581o2c k) + cos581o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_85
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 86 - ((187991/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_87 : ((9446221/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos581o2c k) + cos581o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_86
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 87 - ((-991373/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_88 : ((10445017/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos581o2c k) + cos581o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_87
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 88 - ((62431/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_89 : ((236563/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos581o2c k) + cos581o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_88
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 89 - ((-982397/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_90 : ((2605011/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos581o2c k) + cos581o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_89
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 90 - ((119703/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_91 : ((118553/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos581o2c k) + cos581o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_90
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 91 - ((-116963/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_92 : ((10407581/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos581o2c k) + cos581o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_91
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 92 - ((923441/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_93 : ((9483647/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos581o2c k) + cos581o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_92
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 93 - ((-461917/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_94 : ((10420073/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos581o2c k) + cos581o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_93
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 94 - ((468263/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_95 : ((1892387/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos581o2c k) + cos581o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_94
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 95 - ((-479019/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_96 : ((10443643/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos581o2c k) + cos581o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_95
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 96 - ((61363/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_97 : ((9445333/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos581o2c k) + cos581o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_96
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 97 - ((-99821/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_98 : ((10440011/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos581o2c k) + cos581o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_97
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 98 - ((497389/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_99 : ((9482981/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos581o2c k) + cos581o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_98
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 99 - ((-95693/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_100 : ((10352413/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos581o2c k) + cos581o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_99
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 100 - ((217383/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_101 : ((4816347/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos581o2c k) + cos581o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_100
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 101 - ((-719619/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_102 : ((1266591/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos581o2c k) + cos581o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_101
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 102 - ((250067/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_103 : ((9918003/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos581o2c k) + cos581o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_102
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 103 - ((-1717/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_104 : ((9799677/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos581o2c k) + cos581o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_103
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 104 - ((-59113/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_105 : ((5130747/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos581o2c k) + cos581o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_104
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 105 - ((461917/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_106 : ((2374559/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos581o2c k) + cos581o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_105
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 106 - ((-381579/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_107 : ((2091347/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos581o2c k) + cos581o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_106
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 107 - ((958599/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_108 : ((9467937/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos581o2c k) + cos581o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_107
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 108 - ((-494349/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_109 : ((5142403/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos581o2c k) + cos581o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_108
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 109 - ((816969/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_110 : ((491701/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos581o2c k) + cos581o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_109
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 110 - ((-225343/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_111 : ((1223609/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos581o2c k) + cos581o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_110
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 111 - ((-5631/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_112 : ((1292233/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos581o2c k) + cos581o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_111
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 112 - ((137273/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_113 : ((4714437/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos581o2c k) + cos581o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_112
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 113 - ((-90889/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_114 : ((5208627/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos581o2c k) + cos581o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_113
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 114 - ((3089/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_115 : ((9689833/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos581o2c k) + cos581o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_114
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 115 - ((-727321/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_116 : ((1975319/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos581o2c k) + cos581o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_115
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 116 - ((93431/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_117 : ((10320471/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos581o2c k) + cos581o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_116
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 117 - ((55497/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_118 : ((588517/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos581o2c k) + cos581o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_117
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 118 - ((-904099/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_119 : ((1298179/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos581o2c k) + cos581o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_118
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 119 - ((48463/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_120 : ((9811151/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos581o2c k) + cos581o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_119
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 120 - ((-574181/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_121 : ((4846073/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos581o2c k) + cos581o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_120
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 121 - ((-23781/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_122 : ((10456259/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos581o2c k) + cos581o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_121
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 122 - ((764213/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_123 : ((9458551/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos581o2c k) + cos581o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_122
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 123 - ((-124701/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_124 : ((10111999/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos581o2c k) + cos581o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_123
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 124 - ((163387/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_125 : ((10207727/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos581o2c k) + cos581o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_124
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 125 - ((23957/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_126 : ((9410329/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos581o2c k) + cos581o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_125
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 126 - ((-398649/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_127 : ((5195427/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos581o2c k) + cos581o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_126
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 127 - ((1569/1600 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_128 : ((2475539/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos581o2c k) + cos581o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_127
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 128 - ((-244299/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_129 : ((1908017/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos581o2c k) + cos581o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_128
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 129 - ((-361971/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_130 : ((1049471/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos581o2c k) + cos581o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_129
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 130 - ((38189/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_131 : ((9676947/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos581o2c k) + cos581o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_130
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 131 - ((-817663/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_132 : ((303179/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos581o2c k) + cos581o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_131
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 132 - ((24881/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_133 : ((2624949/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos581o2c k) + cos581o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_132
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 133 - ((99771/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_134 : ((191003/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos581o2c k) + cos581o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_133
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 134 - ((-474773/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_135 : ((4908413/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos581o2c k) + cos581o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_134
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 135 - ((33347/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_136 : ((5240913/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos581o2c k) + cos581o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_135
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 136 - ((6651/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_137 : ((4748087/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos581o2c k) + cos581o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_136
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 137 - ((-61597/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_138 : ((9859303/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos581o2c k) + cos581o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_137
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 138 - ((363229/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_139 : ((262051/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos581o2c k) + cos581o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_138
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 139 - ((622837/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_140 : ((4747413/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos581o2c k) + cos581o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_139
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 140 - ((-493557/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_141 : ((9824531/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos581o2c k) + cos581o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_140
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 141 - ((65961/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_142 : ((5253939/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos581o2c k) + cos581o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_141
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 142 - ((683447/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_143 : ((477401/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos581o2c k) + cos581o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_142
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 143 - ((-479879/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_144 : ((4858021/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos581o2c k) + cos581o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_143
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 144 - ((84061/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_145 : ((10536429/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos581o2c k) + cos581o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_144
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 145 - ((820487/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_146 : ((9676817/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos581o2c k) + cos581o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_145
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 146 - ((-107439/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_147 : ((2388171/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos581o2c k) + cos581o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_146
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 147 - ((-124033/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_148 : ((2103037/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos581o2c k) + cos581o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_147
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 148 - ((962601/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_149 : ((2475529/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos581o2c k) + cos581o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_148
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 149 - ((-612969/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_150 : ((4694517/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos581o2c k) + cos581o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_149
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 150 - ((-256491/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_151 : ((5186461/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos581o2c k) + cos581o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_150
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 151 - ((245997/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_152 : ((2551523/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos581o2c k) + cos581o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_151
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 152 - ((-16673/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_153 : ((9329197/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos581o2c k) + cos581o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_152
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 153 - ((-175359/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_154 : ((5031267/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos581o2c k) + cos581o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_153
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 154 - ((733437/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_155 : ((10486533/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos581o2c k) + cos581o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_154
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 155 - ((424099/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_156 : ((9496299/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos581o2c k) + cos581o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_155
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 156 - ((-495067/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_157 : ((9640547/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos581o2c k) + cos581o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_156
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 157 - ((36087/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_158 : ((10554147/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos581o2c k) + cos581o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_157
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 158 - ((9137/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_159 : ((1984969/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos581o2c k) + cos581o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_158
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 159 - ((-314601/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_160 : ((1165969/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos581o2c k) + cos581o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_159
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 160 - ((-596993/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_161 : ((5124243/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos581o2c k) + cos581o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_160
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 161 - ((460417/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_162 : ((5210067/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos581o2c k) + cos581o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_161
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 162 - ((42937/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_163 : ((1884203/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos581o2c k) + cos581o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_162
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 163 - ((-999019/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_164 : ((4834289/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos581o2c k) + cos581o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_163
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 164 - ((247663/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_165 : ((10570907/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos581o2c k) + cos581o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_164
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 165 - ((902429/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_166 : ((9981733/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos581o2c k) + cos581o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_165
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 166 - ((-294537/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_167 : ((9287721/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos581o2c k) + cos581o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_166
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 167 - ((-86739/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_168 : ((5055519/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos581o2c k) + cos581o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_167
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 168 - ((823417/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_169 : ((5273009/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos581o2c k) + cos581o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_168
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 169 - ((10877/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_170 : ((2398173/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos581o2c k) + cos581o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_169
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 170 - ((-476613/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_171 : ((294357/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos581o2c k) + cos581o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_170
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 171 - ((-10823/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_172 : ((5209013/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos581o2c k) + cos581o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_171
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 172 - ((499351/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_173 : ((10355671/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos581o2c k) + cos581o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_172
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 173 - ((-12451/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_174 : ((9369293/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos581o2c k) + cos581o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_173
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 174 - ((-493139/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_175 : ((4813053/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos581o2c k) + cos581o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_174
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 175 - ((256913/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_176 : ((5283659/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos581o2c k) + cos581o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_175
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 176 - ((14708/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_177 : ((10159989/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos581o2c k) + cos581o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_176
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 177 - ((-407229/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_178 : ((4637663/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos581o2c k) + cos581o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_177
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 178 - ((-884563/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_179 : ((9791001/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos581o2c k) + cos581o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_178
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 179 - ((20631/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_180 : ((84977/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos581o2c k) + cos581o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_179
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 180 - ((103903/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_181 : ((5017199/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos581o2c k) + cos581o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_180
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 181 - ((-587627/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_182 : ((9242999/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos581o2c k) + cos581o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_181
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 182 - ((-791299/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_183 : ((1233851/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos581o2c k) + cos581o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_182
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 183 - ((627909/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_184 : ((2128241/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos581o2c k) + cos581o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_183
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 184 - ((770497/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_185 : ((5000391/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos581o2c k) + cos581o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_184
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 185 - ((-640323/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_186 : ((2307383/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos581o2c k) + cos581o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_185
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 186 - ((-15423/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_187 : ((9855901/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos581o2c k) + cos581o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_186
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 187 - ((626469/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_188 : ((10648519/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos581o2c k) + cos581o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_187
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 188 - ((396359/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_189 : ((10062611/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos581o2c k) + cos581o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_188
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 189 - ((-36613/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_190 : ((9230487/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos581o2c k) + cos581o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_189
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 190 - ((-104003/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_191 : ((2436603/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos581o2c k) + cos581o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_190
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 191 - ((20641/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_192 : ((10629411/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos581o2c k) + cos581o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_191
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 192 - ((883099/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_193 : ((2553869/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos581o2c k) + cos581o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_192
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 193 - ((-82767/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_194 : ((4639243/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos581o2c k) + cos581o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_193
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 194 - ((-93689/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_195 : ((4777347/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos581o2c k) + cos581o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_194
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 195 - ((69077/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_196 : ((1316953/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos581o2c k) + cos581o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_195
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 196 - ((98103/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_197 : ((5216513/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos581o2c k) + cos581o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_196
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 197 - ((-51249/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_198 : ((943293/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos581o2c k) + cos581o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_197
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 198 - ((-249999/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_199 : ((373139/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos581o2c k) + cos581o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_198
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 199 - ((-20871/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_200 : ((2060889/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos581o2c k) + cos581o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_199
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 200 - ((97607/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_201 : ((10638877/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos581o2c k) + cos581o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_200
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 201 - ((83633/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_202 : ((4873659/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos581o2c k) + cos581o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_201
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 202 - ((-891459/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_203 : ((1835451/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos581o2c k) + cos581o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_202
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 203 - ((-569963/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_204 : ((9909021/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos581o2c k) + cos581o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_203
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 204 - ((365933/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_205 : ((10692243/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos581o2c k) + cos581o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_204
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 205 - ((391661/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_206 : ((1275099/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos581o2c k) + cos581o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_205
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 206 - ((-491351/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_207 : ((9261189/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos581o2c k) + cos581o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_206
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 207 - ((-939503/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_208 : ((4719483/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos581o2c k) + cos581o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_207
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 208 - ((177877/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_209 : ((2087773/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos581o2c k) + cos581o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_208
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 209 - ((999999/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_210 : ((2655143/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos581o2c k) + cos581o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_209
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 210 - ((181807/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_211 : ((4844721/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos581o2c k) + cos581o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_210
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 211 - ((-93103/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_212 : ((9148991/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos581o2c k) + cos581o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_211
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 212 - ((-540351/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_213 : ((9863601/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos581o2c k) + cos581o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_212
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 213 - ((71471/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_214 : ((10696613/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos581o2c k) + cos581o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_213
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 214 - ((104139/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_215 : ((1033527/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos581o2c k) + cos581o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_214
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 215 - ((-361243/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_216 : ((2336483/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos581o2c k) + cos581o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_215
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 216 - ((-494619/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_217 : ((115797/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos581o2c k) + cos581o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_216
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 217 - ((-10259/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_218 : ((2553433/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos581o2c k) + cos581o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_217
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 218 - ((118759/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_219 : ((10743627/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos581o2c k) + cos581o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_218
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 219 - ((105999/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_220 : ((10051087/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos581o2c k) + cos581o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_219
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 220 - ((-17311/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_221 : ((4589499/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos581o2c k) + cos581o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_220
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 221 - ((-871989/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_222 : ((9428471/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos581o2c k) + cos581o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_221
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 222 - ((249573/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_223 : ((10428287/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos581o2c k) + cos581o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_222
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 223 - ((249979/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_224 : ((2677083/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos581o2c k) + cos581o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_223
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 224 - ((56029/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_225 : ((9861369/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos581o2c k) + cos581o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_224
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 225 - ((-846863/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_226 : ((2278607/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos581o2c k) + cos581o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_225
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 226 - ((-746841/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_227 : ((953961/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos581o2c k) + cos581o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_226
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 227 - ((212641/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_228 : ((5264479/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos581o2c k) + cos581o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_227
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 228 - ((123681/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_229 : ((5341151/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos581o2c k) + cos581o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_228
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 229 - ((38361/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_230 : ((978573/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos581o2c k) + cos581o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_229
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 230 - ((-112059/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_231 : ((4544911/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos581o2c k) + cos581o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_230
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 231 - ((-10872/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_232 : ((1911239/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos581o2c k) + cos581o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_231
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 232 - ((466473/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_233 : ((5271341/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos581o2c k) + cos581o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_232
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 233 - ((986587/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_234 : ((2140913/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos581o2c k) + cos581o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_233
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 234 - ((161983/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_235 : ((2456087/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos581o2c k) + cos581o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_234
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 235 - ((-880117/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_236 : ((9085013/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos581o2c k) + cos581o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_235
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 236 - ((-147847/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_237 : ((9471001/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos581o2c k) + cos581o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_236
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 237 - ((48261/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_238 : ((10469713/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos581o2c k) + cos581o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_237
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 238 - ((249703/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_239 : ((10768969/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos581o2c k) + cos581o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_238
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 239 - ((74839/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_240 : ((9980019/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos581o2c k) + cos581o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_239
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 240 - ((-15777/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_241 : ((9125331/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos581o2c k) + cos581o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_240
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 241 - ((-213647/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_242 : ((1860487/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos581o2c k) + cos581o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_241
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 242 - ((44301/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_243 : ((5141719/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos581o2c k) + cos581o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_242
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 243 - ((981103/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_244 : ((10825063/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos581o2c k) + cos581o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_243
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 244 - ((21669/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_245 : ((256187/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos581o2c k) + cos581o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_244
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 245 - ((-577483/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_246 : ((1854659/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos581o2c k) + cos581o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_245
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 246 - ((-194817/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_247 : ((910979/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos581o2c k) + cos581o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_246
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 247 - ((-32681/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_248 : ((4978153/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos581o2c k) + cos581o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_247
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 248 - ((105827/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_249 : ((10777113/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos581o2c k) + cos581o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_248
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 249 - ((820907/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_250 : ((5288507/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos581o2c k) + cos581o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_249
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 250 - ((-199999/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_251 : ((4799417/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 251, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 251, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 250, cos581o2c k) + cos581o2c 251 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 250) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_250
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 251 - ((-6113/6250 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_251).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_252 : ((9013229/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 252, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 252, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 251, cos581o2c k) + cos581o2c 252 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 251) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_251
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 252 - ((-117101/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_252).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_253 : ((297323/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 253, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 253, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 252, cos581o2c k) + cos581o2c 253 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 252) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_252
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 253 - ((501207/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_253).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_254 : ((1313653/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 254, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 254, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 253, cos581o2c k) + cos581o2c 254 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 253) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_253
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 254 - ((248747/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_254).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_255 : ((2166477/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 255, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 255, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 254, cos581o2c k) + cos581o2c 255 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 254) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_254
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 255 - ((323261/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_255).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_256 : ((10109507/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 256, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 256, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 255, cos581o2c k) + cos581o2c 256 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 255) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_255
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 256 - ((-361389/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_256).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_257 : ((9176921/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 257, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 257, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 256, cos581o2c k) + cos581o2c 257 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 256) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_256
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 257 - ((-466243/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_257).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_258 : ((142247/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 258, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 258, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 257, cos581o2c k) + cos581o2c 258 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 257) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_257
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 258 - ((-73013/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_258).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_259 : ((997149/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 259, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 259, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 258, cos581o2c k) + cos581o2c 259 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 258) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_258
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 259 - ((433891/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_259).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_260 : ((10797067/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 260, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 260, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 259, cos581o2c k) + cos581o2c 260 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 259) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_259
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 260 - ((825677/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_260).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_261 : ((10653691/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 261, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 261, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 260, cos581o2c k) + cos581o2c 261 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 260) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_260
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 261 - ((-35819/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_261).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_262 : ((1212893/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 262, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 262, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 261, cos581o2c k) + cos581o2c 262 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 261) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_261
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 262 - ((-950447/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_262).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_263 : ((8999579/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 263, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 263, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 262, cos581o2c k) + cos581o2c 263 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 262) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_262
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 263 - ((-140693/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_263).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_264 : ((9316147/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 264, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 264, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 263, cos581o2c k) + cos581o2c 264 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 263) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_263
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 264 - ((79167/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_264).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_265 : ((412191/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 265, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 265, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 264, cos581o2c k) + cos581o2c 265 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 264) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_264
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 265 - ((123591/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_265).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_266 : ((435653/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 266, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 266, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 265, cos581o2c k) + cos581o2c 266 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 265) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_265
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 266 - ((11733/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_266).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_267 : ((10444477/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 267, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 267, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 266, cos581o2c k) + cos581o2c 267 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 266) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_266
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 267 - ((-111687/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_267).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_268 : ((2361153/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 268, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 268, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 267, cos581o2c k) + cos581o2c 268 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 267) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_267
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 268 - ((-199953/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_268).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_269 : ((4477927/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 269, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 269, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 268, cos581o2c k) + cos581o2c 269 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 268) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_268
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 269 - ((-244329/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_269).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_270 : ((9493177/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 270, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 270, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 269, cos581o2c k) + cos581o2c 270 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 269) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_269
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 270 - ((537423/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_270).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_271 : ((10490591/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 271, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 271, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 270, cos581o2c k) + cos581o2c 271 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 270) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_270
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 271 - ((498757/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_271).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_272 : ((1090763/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 272, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 272, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 271, cos581o2c k) + cos581o2c 272 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 271) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_271
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 272 - ((417139/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_272).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_273 : ((10313747/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 273, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 273, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 272, cos581o2c k) + cos581o2c 273 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 272) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_272
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 273 - ((-593783/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_273).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_274 : ((4660859/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 274, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 274, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 273, cos581o2c k) + cos581o2c 274 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 273) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_273
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 274 - ((-991929/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_274).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_275 : ((4472847/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 275, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 275, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 274, cos581o2c k) + cos581o2c 275 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 274) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_274
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 275 - ((-93981/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_275).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_276 : ((4782923/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 276, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 276, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 275, cos581o2c k) + cos581o2c 276 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 275) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_275
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 276 - ((155063/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_276).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_277 : ((5277339/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 277, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 277, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 276, cos581o2c k) + cos581o2c 277 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 276) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_276
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 277 - ((247233/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_277).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_278 : ((136511/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 278, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 278, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 277, cos581o2c k) + cos581o2c 278 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 277) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_277
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 278 - ((183151/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_278).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_279 : ((5150667/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 279, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 279, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 278, cos581o2c k) + cos581o2c 279 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 278) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_278
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 279 - ((-309723/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_279).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_280 : ((1163819/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 280, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 280, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 279, cos581o2c k) + cos581o2c 280 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 279) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_279
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 280 - ((-495341/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_280).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_281 : ((1115297/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 281, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 281, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 280, cos581o2c k) + cos581o2c 281 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 280) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_280
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 281 - ((-97019/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_281).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_282 : ((2378547/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 282, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 282, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 281, cos581o2c k) + cos581o2c 282 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 281) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_281
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 282 - ((73989/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_282).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_283 : ((2101991/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 283, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 283, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 282, cos581o2c k) + cos581o2c 283 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 282) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_282
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 283 - ((995867/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_283).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_284 : ((2189889/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 284, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 284, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 283, cos581o2c k) + cos581o2c 284 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 283) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_283
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 284 - ((43959/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_284).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_285 : ((5206569/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 285, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 285, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 284, cos581o2c k) + cos581o2c 285 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 284) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_284
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 285 - ((-536207/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_285).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_286 : ((4706559/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 286, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 286, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 285, cos581o2c k) + cos581o2c 286 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 285) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_285
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 286 - ((-12499/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_286).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_287 : ((4447659/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 287, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 287, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 286, cos581o2c k) + cos581o2c 287 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 286) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_286
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 287 - ((-5177/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_287).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_288 : ((2336191/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 288, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 288, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 287, cos581o2c k) + cos581o2c 288 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 287) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_287
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 288 - ((224773/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_288).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_289 : ((161561/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 289, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 289, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 288, cos581o2c k) + cos581o2c 289 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 288) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_288
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 289 - ((24881/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_289).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_290 : ((10956809/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 290, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 290, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 289, cos581o2c k) + cos581o2c 290 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 289) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_289
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 290 - ((123401/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_290).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_291 : ((5313943/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 291, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 291, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 290, cos581o2c k) + cos581o2c 291 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 290) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_290
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 291 - ((-328823/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_291).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_292 : ((4828123/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 292, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 292, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 291, cos581o2c k) + cos581o2c 292 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 291) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_291
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 292 - ((-48577/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_292).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_293 : ((4463599/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 293, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 293, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 292, cos581o2c k) + cos581o2c 293 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 292) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_292
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 293 - ((-182237/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_293).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_294 : ((1819843/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 294, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 294, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 293, cos581o2c k) + cos581o2c 294 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 293) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_293
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 294 - ((172117/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_294).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_295 : ((5007839/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 295, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 295, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 294, cos581o2c k) + cos581o2c 295 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 294) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_294
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 295 - ((916563/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_295).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_296 : ((10856569/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 296, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 296, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 295, cos581o2c k) + cos581o2c 296 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 295) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_295
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 296 - ((840991/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_296).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_297 : ((10875811/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 297, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 297, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 296, cos581o2c k) + cos581o2c 297 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 296) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_296
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 297 - ((9671/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_297).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_298 : ((10058177/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 298, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 298, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 297, cos581o2c k) + cos581o2c 298 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 297) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_297
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 298 - ((-408767/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_298).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_299 : ((2280503/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 299, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 299, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 298, cos581o2c k) + cos581o2c 299 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 298) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_298
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 299 - ((-187213/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_299).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_300 : ((355317/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 300, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 300, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 299, cos581o2c k) + cos581o2c 300 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 299) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_299
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 300 - ((-238987/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_300).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_301 : ((4773131/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 301, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 301, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 300, cos581o2c k) + cos581o2c 301 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 300) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_300
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 301 - ((663437/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_301).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_302 : ((1317399/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 302, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 302, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 301, cos581o2c k) + cos581o2c 302 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 301) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_301
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 302 - ((99303/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_302).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_303 : ((11011767/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 303, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 303, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 302, cos581o2c k) + cos581o2c 303 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 302) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_302
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 303 - ((18907/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_303).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_304 : ((1320423/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 304, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 304, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 303, cos581o2c k) + cos581o2c 304 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 303) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_303
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 304 - ((-448283/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_304).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_305 : ((4787403/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 305, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 305, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 304, cos581o2c k) + cos581o2c 305 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 304) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_304
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 305 - ((-494239/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_305).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_306 : ((4438631/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 306, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 306, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 305, cos581o2c k) + cos581o2c 306 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 305) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_305
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 306 - ((-174361/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_306).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_307 : ((9052217/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 307, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 307, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 306, cos581o2c k) + cos581o2c 307 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 306) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_306
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 307 - ((35011/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_307).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_308 : ((2488127/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 308, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 308, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 307, cos581o2c k) + cos581o2c 308 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 307) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_307
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 308 - ((900391/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_308).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_309 : ((10834021/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 309, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 309, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 308, cos581o2c k) + cos581o2c 309 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 308) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_308
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 309 - ((881613/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_309).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_310 : ((5487061/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 310, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 310, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 309, cos581o2c k) + cos581o2c 310 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 309) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_309
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 310 - ((140201/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_310).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_311 : ((5130097/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 311, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 311, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 310, cos581o2c k) + cos581o2c 311 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 310) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_310
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 311 - ((-178457/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_311).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_312 : ((9272349/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 312, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 312, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 311, cos581o2c k) + cos581o2c 312 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 311) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_311
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 312 - ((-197549/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_312).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_313 : ((17613/2000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 313, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 313, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 312, cos581o2c k) + cos581o2c 313 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 312) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_312
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 313 - ((-465749/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_313).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_314 : ((923429/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 314, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 314, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 313, cos581o2c k) + cos581o2c 314 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 313) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_313
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 314 - ((42789/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_314).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_315 : ((638329/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 315, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 315, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 314, cos581o2c k) + cos581o2c 315 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 314) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_314
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 315 - ((489537/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_315).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_316 : ((342741/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 316, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 316, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 315, cos581o2c k) + cos581o2c 316 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 315) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_315
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 316 - ((188637/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_316).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_317 : ((10904783/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 317, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 317, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 316, cos581o2c k) + cos581o2c 317 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 316) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_316
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 317 - ((-62829/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_317).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_318 : ((10075397/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 318, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 318, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 317, cos581o2c k) + cos581o2c 318 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 317) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_317
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 318 - ((-414643/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_318).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_319 : ((9125793/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 319, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 319, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 318, cos581o2c k) + cos581o2c 319 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 318) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_318
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 319 - ((-14836/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_319).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_320 : ((4394951/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 320, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 320, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 319, cos581o2c k) + cos581o2c 320 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 319) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_319
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 320 - ((-335791/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_320).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_321 : ((9324351/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 321, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 321, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 320, cos581o2c k) + cos581o2c 321 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 320) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_320
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 321 - ((534549/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_321).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_322 : ((412757/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 322, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 322, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 321, cos581o2c k) + cos581o2c 322 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 321) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_321
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 322 - ((497337/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_322).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_323 : ((11017301/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 323, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 323, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 322, cos581o2c k) + cos581o2c 323 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 322) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_322
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 323 - ((174619/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_323).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_324 : ((2723199/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 324, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 324, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 323, cos581o2c k) + cos581o2c 324 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 323) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_323
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 324 - ((-24881/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_324).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_325 : ((10040623/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 325, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 325, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 324, cos581o2c k) + cos581o2c 325 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 324) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_324
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 325 - ((-852073/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_325).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_326 : ((9098307/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 326, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 326, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 325, cos581o2c k) + cos581o2c 326 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 325) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_325
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 326 - ((-117777/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_326).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_327 : ((4382623/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 327, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 327, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 326, cos581o2c k) + cos581o2c 327 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 326) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_326
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 327 - ((-332961/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_327).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_328 : ((1857157/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 328, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 328, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 327, cos581o2c k) + cos581o2c 328 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 327) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_327
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 328 - ((520639/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_328).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_329 : ((1284507/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 329, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 329, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 328, cos581o2c k) + cos581o2c 329 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 328) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_328
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 329 - ((990371/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_329).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_330 : ((5506283/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 330, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 330, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 329, cos581o2c k) + cos581o2c 330 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 329) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_329
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 330 - ((73661/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_330).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_331 : ((5480783/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 331, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 331, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 330, cos581o2c k) + cos581o2c 331 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 330) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_330
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 331 - ((-509/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_331).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_332 : ((1270187/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 332, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 332, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 331, cos581o2c k) + cos581o2c 332 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 331) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_331
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 332 - ((-79997/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_332).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_333 : ((4593879/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 333, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 333, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 332, cos581o2c k) + cos581o2c 333 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 332) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_332
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 333 - ((-486819/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_333).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_334 : ((2183781/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 334, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 334, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 333, cos581o2c k) + cos581o2c 334 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 333) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_333
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 334 - ((-226267/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_334).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_335 : ((1824681/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 335, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 335, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 334, cos581o2c k) + cos581o2c 335 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 334) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_334
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 335 - ((388381/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_335).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_336 : ((5038417/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 336, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 336, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 335, cos581o2c k) + cos581o2c 336 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 335) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_335
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 336 - ((953529/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_336).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_337 : ((10925447/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 337, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 337, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 336, cos581o2c k) + cos581o2c 337 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 336) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_336
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 337 - ((848713/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_337).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_338 : ((5538789/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 338, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 338, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 337, cos581o2c k) + cos581o2c 338 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 337) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_337
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 338 - ((152231/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_338).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_339 : ((521457/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 339, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 339, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 338, cos581o2c k) + cos581o2c 339 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 338) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_338
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 339 - ((-324169/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_339).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_340 : ((9429087/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 340, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 340, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 339, cos581o2c k) + cos581o2c 340 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 339) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_339
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 340 - ((-999953/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_340).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_341 : ((2191017/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 341, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 341, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 340, cos581o2c k) + cos581o2c 341 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 340) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_340
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 341 - ((-664919/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_341).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_342 : ((4443471/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 342, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 342, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 341, cos581o2c k) + cos581o2c 342 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 341) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_341
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 342 - ((61487/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_342).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_343 : ((1214069/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 343, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 343, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 342, cos581o2c k) + cos581o2c 343 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 342) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_342
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 343 - ((82571/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_343).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_344 : ((10682257/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 344, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 344, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 343, cos581o2c k) + cos581o2c 344 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 343) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_343
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 344 - ((193961/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_344).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_345 : ((11144971/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 345, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 345, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 344, cos581o2c k) + cos581o2c 345 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 344) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_344
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 345 - ((231407/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_345).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_346 : ((2158589/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 346, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 346, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 345, cos581o2c k) + cos581o2c 346 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 345) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_345
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 346 - ((-175963/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_346).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_347 : ((9861529/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 347, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 347, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 346, cos581o2c k) + cos581o2c 347 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 346) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_346
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 347 - ((-232829/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_347).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_348 : ((2241699/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 348, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 348, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 347, cos581o2c k) + cos581o2c 348 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 347) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_347
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 348 - ((-894633/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_348).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_349 : ((2174023/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 349, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 349, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 348, cos581o2c k) + cos581o2c 349 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 348) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_348
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 349 - ((-67651/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_349).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_350 : ((144137/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 350, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 350, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 349, cos581o2c k) + cos581o2c 350 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 349) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_349
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 350 - ((66097/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_350).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_351 : ((10207639/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 351, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 351, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 350, cos581o2c k) + cos581o2c 351 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 350) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_350
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 351 - ((982971/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_351).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_352 : ((550433/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 352, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 352, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 351, cos581o2c k) + cos581o2c 352 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 351) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_351
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 352 - ((801121/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_352).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_353 : ((11113413/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 353, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 353, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 352, cos581o2c k) + cos581o2c 353 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 352) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_352
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 353 - ((104853/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_353).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_354 : ((1307047/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 354, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 354, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 353, cos581o2c k) + cos581o2c 354 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 353) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_353
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 354 - ((-656937/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_354).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_355 : ((15131/1600 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 355, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 355, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 354, cos581o2c k) + cos581o2c 355 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 354) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_354
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 355 - ((-999401/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_355).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_356 : ((8747673/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 356, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 356, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 355, cos581o2c k) + cos581o2c 356 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 355) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_355
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 356 - ((-354551/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_356).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_357 : ((4387099/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 357, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 357, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 356, cos581o2c k) + cos581o2c 357 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 356) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_356
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 357 - ((213/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_357).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_358 : ((9518217/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 358, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 358, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 357, cos581o2c k) + cos581o2c 358 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 357) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_357
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 358 - ((744119/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_358).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_359 : ((10515019/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 359, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 359, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 358, cos581o2c k) + cos581o2c 359 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 358) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_358
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 359 - ((498451/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_359).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_360 : ((11146797/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 360, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 360, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 359, cos581o2c k) + cos581o2c 360 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 359) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_359
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 360 - ((315939/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_360).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_361 : ((5512577/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 361, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 361, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 360, cos581o2c k) + cos581o2c 361 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 360) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_360
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 361 - ((-121543/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_361).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_362 : ((127827/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 362, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 362, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 361, cos581o2c k) + cos581o2c 362 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 361) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_361
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 362 - ((-399447/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_362).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_363 : ((144347/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 363, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 363, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 362, cos581o2c k) + cos581o2c 363 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 362) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_362
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 363 - ((-246963/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_363).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_364 : ((433033/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 364, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 364, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 363, cos581o2c k) + cos581o2c 364 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 363) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_363
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 364 - ((-72181/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_364).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_365 : ((1768191/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 365, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 365, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 364, cos581o2c k) + cos581o2c 365 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 364) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_364
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 365 - ((36079/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_365).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_366 : ((9669227/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 366, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 366, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 365, cos581o2c k) + cos581o2c 366 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 365) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_365
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 366 - ((207093/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_366).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_367 : ((10649583/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 367, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 367, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 366, cos581o2c k) + cos581o2c 367 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 366) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_366
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 367 - ((122557/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_367).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_368 : ((559971/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 368, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 368, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 367, cos581o2c k) + cos581o2c 368 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 367) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_367
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 368 - ((549937/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_368).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_369 : ((10994733/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 369, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 369, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 368, cos581o2c k) + cos581o2c 369 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 368) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_368
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 369 - ((-204587/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_369).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_370 : ((5078687/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 370, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 370, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 369, cos581o2c k) + cos581o2c 370 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 369) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_369
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 370 - ((-837259/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_370).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_371 : ((4589159/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 371, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 371, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 370, cos581o2c k) + cos581o2c 371 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 370) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_370
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 371 - ((-244739/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_371).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_372 : ((345097/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 372, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 372, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 371, cos581o2c k) + cos581o2c 372 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 371) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_371
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 372 - ((-550793/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_372).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_373 : ((275707/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 373, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 373, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 372, cos581o2c k) + cos581o2c 373 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 372) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_372
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 373 - ((195299/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_373).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_374 : ((9649843/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 374, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 374, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 373, cos581o2c k) + cos581o2c 374 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 373) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_373
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 374 - ((827319/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_374).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_375 : ((5316861/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 375, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 375, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 374, cos581o2c k) + cos581o2c 375 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 374) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_374
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 375 - ((983979/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_375).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_376 : ((2242593/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 376, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 376, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 375, cos581o2c k) + cos581o2c 376 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 375) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_375
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 376 - ((579343/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_376).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_377 : ((11059823/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 377, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 377, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 376, cos581o2c k) + cos581o2c 377 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 376) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_376
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 377 - ((-76521/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_377).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_378 : ((10262199/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 378, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 378, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 377, cos581o2c k) + cos581o2c 378 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 377) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_377
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 378 - ((-199381/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_378).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_379 : ((57933/6250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 379, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 379, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 378, cos581o2c k) + cos581o2c 379 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 378) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_378
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 379 - ((-992819/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_379).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_380 : ((4318093/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 380, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 380, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 379, cos581o2c k) + cos581o2c 380 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 379) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_379
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 380 - ((-316497/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_380).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_381 : ((1742811/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 381, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 381, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 380, cos581o2c k) + cos581o2c 381 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 380) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_380
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 381 - ((77969/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_381).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_382 : ((591143/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 382, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 382, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 381, cos581o2c k) + cos581o2c 382 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 381) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_381
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 382 - ((744333/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_382).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_383 : ((10457791/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 383, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 383, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 382, cos581o2c k) + cos581o2c 383 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 382) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_382
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 383 - ((999603/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_383).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_384 : ((11164583/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 384, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 384, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 383, cos581o2c k) + cos581o2c 384 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 383) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_383
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 384 - ((176723/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_384).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_385 : ((11194041/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 385, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 385, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 384, cos581o2c k) + cos581o2c 385 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 384) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_384
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 385 - ((14779/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_385).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_386 : ((10531559/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 386, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 386, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 385, cos581o2c k) + cos581o2c 386 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 385) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_385
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 386 - ((-331191/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_386).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_387 : ((4767993/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 387, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 387, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 386, cos581o2c k) + cos581o2c 387 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 386) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_386
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 387 - ((-995473/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_387).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_388 : ((1748507/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 388, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 388, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 387, cos581o2c k) + cos581o2c 388 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 387) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_387
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 388 - ((-793351/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_388).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_389 : ((1714937/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 389, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 389, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 388, cos581o2c k) + cos581o2c 389 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 388) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_388
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 389 - ((-671/4000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_389).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_390 : ((4560167/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 390, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 390, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 389, cos581o2c k) + cos581o2c 390 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 389) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_389
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 390 - ((545749/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_390).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_391 : ((2017849/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 391, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 391, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 390, cos581o2c k) + cos581o2c 391 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 390) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_390
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 391 - ((969011/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_391).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_392 : ((2194067/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 392, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 392, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 391, cos581o2c k) + cos581o2c 392 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 391) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_391
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 392 - ((88119/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_392).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_393 : ((565103/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 393, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 393, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 392, cos581o2c k) + cos581o2c 393 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 392) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_392
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 393 - ((13273/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_393).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_394 : ((10912533/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 394, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 394, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 393, cos581o2c k) + cos581o2c 394 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 393) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_393
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 394 - ((-389427/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_394).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_395 : ((5002661/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 395, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 395, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 394, cos581o2c k) + cos581o2c 395 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 394) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_394
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 395 - ((-907111/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_395).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_396 : ((2262479/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 396, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 396, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 395, cos581o2c k) + cos581o2c 396 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 395) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_395
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 396 - ((-477653/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_396).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_397 : ((8537351/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 397, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 397, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 396, cos581o2c k) + cos581o2c 397 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 396) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_396
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 397 - ((-102493/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_397).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_398 : ((4364423/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 398, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 398, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 397, cos581o2c k) + cos581o2c 398 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 397) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_397
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 398 - ((38319/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_398).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_399 : ((9525417/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 399, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 399, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 398, cos581o2c k) + cos581o2c 399 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 398) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_398
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 399 - ((796671/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_399).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_400 : ((10522267/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 400, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 400, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 399, cos581o2c k) + cos581o2c 400 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 399) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_399
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 400 - ((19939/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_400).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_401 : ((11216379/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 401, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 401, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 400, cos581o2c k) + cos581o2c 401 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 400) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_400
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 401 - ((173553/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_401).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_402 : ((11260071/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 402, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 402, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 401, cos581o2c k) + cos581o2c 402 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 401) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_401
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 402 - ((2737/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_402).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_403 : ((531639/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 403, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 403, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 402, cos581o2c k) + cos581o2c 403 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 402) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_402
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 403 - ((-627191/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_403).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_404 : ((9647591/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 404, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 404, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 403, cos581o2c k) + cos581o2c 404 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 403) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_403
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 404 - ((-985089/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_404).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_405 : ((8792501/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 405, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 405, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 404, cos581o2c k) + cos581o2c 405 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 404) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_404
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 405 - ((-85499/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_405).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_406 : ((2122043/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 406, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 406, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 405, cos581o2c k) + cos581o2c 406 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 405) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_405
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 406 - ((-304229/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_406).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_407 : ((8882551/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 407, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 407, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 406, cos581o2c k) + cos581o2c 407 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 406) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_406
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 407 - ((394479/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_407).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_408 : ((1222731/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 408, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 408, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 407, cos581o2c k) + cos581o2c 408 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 407) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_407
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 408 - ((899397/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_408).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_409 : ((5374231/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 409, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 409, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 408, cos581o2c k) + cos581o2c 409 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 408) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_408
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 409 - ((483357/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_409).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_410 : ((11315197/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 410, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 410, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 409, cos581o2c k) + cos581o2c 410 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 409) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_409
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 410 - ((113367/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_410).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_411 : ((11210263/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 411, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 411, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 410, cos581o2c k) + cos581o2c 411 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 410) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_410
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 411 - ((-52417/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_411).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_412 : ((5242603/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 412, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 412, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 411, cos581o2c k) + cos581o2c 412 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 411) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_411
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 412 - ((-724957/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_412).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_413 : ((9486651/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 413, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 413, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 412, cos581o2c k) + cos581o2c 413 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 412) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_412
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 413 - ((-199691/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_413).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_414 : ((69509/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 414, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 414, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 413, cos581o2c k) + cos581o2c 414 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 413) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_413
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 414 - ((-398963/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_414).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_415 : ((8467383/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 415, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 415, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 414, cos581o2c k) + cos581o2c 415 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 414) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_414
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 415 - ((-110571/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_415).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_416 : ((8925653/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 416, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 416, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 415, cos581o2c k) + cos581o2c 416 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 415) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_415
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 416 - ((45837/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_416).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_417 : ((4923861/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 417, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 417, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 416, cos581o2c k) + cos581o2c 417 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 416) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_416
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 417 - ((922169/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_417).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_418 : ((5401677/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 418, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 418, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 417, cos581o2c k) + cos581o2c 418 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 417) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_417
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 418 - ((238933/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_418).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_419 : ((1418699/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 419, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 419, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 418, cos581o2c k) + cos581o2c 419 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 418) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_418
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 419 - ((273169/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_419).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_420 : ((5617617/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 420, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 420, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 419, cos581o2c k) + cos581o2c 420 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 419) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_419
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 420 - ((-57129/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_420).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_421 : ((657129/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 421, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 421, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 420, cos581o2c k) + cos581o2c 421 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 420) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_420
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 421 - ((-72107/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_421).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_422 : ((9516869/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 422, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 422, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 421, cos581o2c k) + cos581o2c 422 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 421) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_421
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 422 - ((-199419/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_422).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_423 : ((2174469/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 423, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 423, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 422, cos581o2c k) + cos581o2c 423 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 422) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_422
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 423 - ((-818893/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_423).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_424 : ((8427651/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 424, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 424, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 423, cos581o2c k) + cos581o2c 424 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 423) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_423
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 424 - ((-2161/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_424).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_425 : ((4413451/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 425, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 425, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 424, cos581o2c k) + cos581o2c 425 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 424) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_424
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 425 - ((399351/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_425).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_426 : ((9715061/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 426, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 426, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 425, cos581o2c k) + cos581o2c 426 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 425) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_425
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 426 - ((888259/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_426).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_427 : ((10694249/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 427, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 427, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 426, cos581o2c k) + cos581o2c 427 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 426) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_426
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 427 - ((122411/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_427).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_428 : ((2832171/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 428, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 428, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 427, cos581o2c k) + cos581o2c 428 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 427) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_427
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 428 - ((126907/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_428).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_429 : ((5669011/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 429, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 429, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 428, cos581o2c k) + cos581o2c 429 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 428) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_428
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 429 - ((4719/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_429).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_430 : ((10719343/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 430, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 430, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 429, cos581o2c k) + cos581o2c 430 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 429) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_429
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 430 - ((-618579/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_430).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_431 : ((974537/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 431, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 431, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 430, cos581o2c k) + cos581o2c 431 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 430) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_430
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 431 - ((-973873/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_431).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_432 : ((8842291/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 432, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 432, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 431, cos581o2c k) + cos581o2c 432 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 431) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_431
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 432 - ((-902979/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_432).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_433 : ((4201383/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 433, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 433, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 432, cos581o2c k) + cos581o2c 433 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 432) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_432
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 433 - ((-17577/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_433).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_434 : ((538511/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 434, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 434, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 433, cos581o2c k) + cos581o2c 434 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 433) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_433
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 434 - ((21351/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_434).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_435 : ((9389201/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 435, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 435, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 434, cos581o2c k) + cos581o2c 435 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 434) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_434
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 435 - ((1237/1600 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_435).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_436 : ((10388901/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 436, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 436, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 435, cos581o2c k) + cos581o2c 436 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 435) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_435
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 436 - ((4999/5000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_436).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_437 : ((2237519/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 437, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 437, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 436, cos581o2c k) + cos581o2c 437 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 436) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_436
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 437 - ((399397/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_437).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_438 : ((2861449/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 438, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 438, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 437, cos581o2c k) + cos581o2c 438 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 437) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_437
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 438 - ((258301/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_438).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_439 : ((690947/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 439, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 439, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 438, cos581o2c k) + cos581o2c 439 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 438) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_438
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 439 - ((-24409/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_439).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_440 : ((1272703/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 440, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 440, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 439, cos581o2c k) + cos581o2c 440 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 439) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_439
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 440 - ((-218357/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_440).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_441 : ((9192883/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 441, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 441, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 440, cos581o2c k) + cos581o2c 441 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 440) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_440
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 441 - ((-988641/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_441).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_442 : ((170049/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 442, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 442, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 441, cos581o2c k) + cos581o2c 442 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 441) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_441
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 442 - ((-690333/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_442).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_443 : ((8397097/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 443, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 443, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 442, cos581o2c k) + cos581o2c 443 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 442) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_442
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 443 - ((-105253/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_443).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_444 : ((8919319/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 444, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 444, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 443, cos581o2c k) + cos581o2c 444 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 443) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_443
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 444 - ((261161/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_444).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_445 : ((492619/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 445, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 445, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 444, cos581o2c k) + cos581o2c 445 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 444) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_444
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 445 - ((933161/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_445).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_446 : ((10812111/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 446, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 446, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 445, cos581o2c k) + cos581o2c 446 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 445) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_445
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 446 - ((959831/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_446).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_447 : ((2851457/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 447, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 447, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 446, cos581o2c k) + cos581o2c 447 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 446) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_446
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 447 - ((593817/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_447).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_448 : ((5696171/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 448, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 448, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 447, cos581o2c k) + cos581o2c 448 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 447) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_447
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 448 - ((-6693/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_448).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_449 : ((2694567/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 449, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 449, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 448, cos581o2c k) + cos581o2c 449 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 448) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_448
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 449 - ((-306987/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_449).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_450 : ((9812667/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 450, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 450, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 449, cos581o2c k) + cos581o2c 450 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 449) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_449
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 450 - ((-965501/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_450).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_451 : ((2221107/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 451, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 451, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 450, cos581o2c k) + cos581o2c 451 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 450) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_450
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 451 - ((-928139/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_451).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_452 : ((8365071/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 452, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 452, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 451, cos581o2c k) + cos581o2c 452 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 451) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_451
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 452 - ((-519257/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_452).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_453 : ((8460847/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 453, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 453, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 452, cos581o2c k) + cos581o2c 453 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 452) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_452
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 453 - ((23969/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_453).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_454 : ((9132503/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 454, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 454, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 453, cos581o2c k) + cos581o2c 454 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 453) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_453
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 454 - ((167939/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_454).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_455 : ((2528361/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 455, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 455, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 454, cos581o2c k) + cos581o2c 455 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 454) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_454
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 455 - ((981041/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_455).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_456 : ((11016929/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 456, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 456, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 455, cos581o2c k) + cos581o2c 456 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 455) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_455
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 456 - ((180717/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_456).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_457 : ((718061/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 457, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 457, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 456, cos581o2c k) + cos581o2c 457 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 456) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_456
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 457 - ((472147/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_457).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_458 : ((2836529/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 458, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 458, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 457, cos581o2c k) + cos581o2c 458 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 457) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_457
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 458 - ((-3569/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_458).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_459 : ((10644973/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 459, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 459, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 458, cos581o2c k) + cos581o2c 459 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 458) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_458
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 459 - ((-701043/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_459).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_460 : ((4828963/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 460, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 460, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 459, cos581o2c k) + cos581o2c 460 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 459) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_459
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 460 - ((-986947/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_460).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_461 : ((175317/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 461, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 461, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 460, cos581o2c k) + cos581o2c 461 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 460) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_460
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 461 - ((-111497/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_461).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_462 : ((4155433/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 462, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 462, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 461, cos581o2c k) + cos581o2c 462 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 461) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_461
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 462 - ((-113721/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_462).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_463 : ((8466013/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 463, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 463, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 462, cos581o2c k) + cos581o2c 463 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 462) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_462
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 463 - ((155247/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_463).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_464 : ((458553/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 464, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 464, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 463, cos581o2c k) + cos581o2c 464 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 463) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_463
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 464 - ((705147/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_464).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_465 : ((5078873/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 465, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 465, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 464, cos581o2c k) + cos581o2c 465 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 464) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_464
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 465 - ((493393/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_465).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_466 : ((11053119/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 466, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 466, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 465, cos581o2c k) + cos581o2c 466 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 465) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_465
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 466 - ((895473/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_466).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_467 : ((5760399/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 467, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 467, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 466, cos581o2c k) + cos581o2c 467 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 466) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_466
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 467 - ((467779/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_467).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_468 : ((11386501/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 468, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 468, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 467, cos581o2c k) + cos581o2c 468 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 467) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_467
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 468 - ((-134197/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_468).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_469 : ((10701349/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 469, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 469, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 468, cos581o2c k) + cos581o2c 469 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 468) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_468
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 469 - ((-171263/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_469).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_470 : ((4860333/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 470, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 470, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 469, cos581o2c k) + cos581o2c 470 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 469) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_469
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 470 - ((-980583/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_470).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_471 : ((1761499/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 471, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 471, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 470, cos581o2c k) + cos581o2c 471 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 470) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_470
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 471 - ((-913071/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_471).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_472 : ((8297871/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 472, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 472, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 471, cos581o2c k) + cos581o2c 472 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 471) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_471
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 472 - ((-127381/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_472).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_473 : ((2094467/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 473, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 473, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 472, cos581o2c k) + cos581o2c 473 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 472) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_472
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 473 - ((80097/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_473).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_474 : ((9017169/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 474, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 474, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 473, cos581o2c k) + cos581o2c 474 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 473) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_473
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 474 - ((639401/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_474).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_475 : ((9982201/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 475, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 475, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 474, cos581o2c k) + cos581o2c 475 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 474) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_474
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 475 - ((241283/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_475).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_476 : ((10922813/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 476, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 476, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 475, cos581o2c k) + cos581o2c 476 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 475) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_475
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 476 - ((117589/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_476).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_477 : ((11499737/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 477, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 477, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 476, cos581o2c k) + cos581o2c 477 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 476) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_476
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 477 - ((9016/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_477).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_478 : ((11506323/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 478, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 478, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 477, cos581o2c k) + cos581o2c 478 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 477) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_477
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 478 - ((3343/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_478).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_479 : ((8753/800 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 479, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 479, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 478, cos581o2c k) + cos581o2c 479 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 478) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_478
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 479 - ((-564973/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_479).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_480 : ((5003429/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 480, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 480, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 479, cos581o2c k) + cos581o2c 480 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 479) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_479
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 480 - ((-233573/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_480).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_481 : ((9035427/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 481, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 481, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 480, cos581o2c k) + cos581o2c 481 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 480) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_480
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 481 - ((-971331/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_481).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_482 : ((4185189/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 482, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 482, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 481, cos581o2c k) + cos581o2c 482 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 481) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_481
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 482 - ((-664949/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_482).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_483 : ((8245241/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 483, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 483, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 482, cos581o2c k) + cos581o2c 483 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 482) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_482
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 483 - ((-125037/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_483).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_484 : ((8702903/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 484, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 484, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 483, cos581o2c k) + cos581o2c 484 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 483) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_483
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 484 - ((228881/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_484).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_485 : ((2395603/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 485, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 485, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 484, cos581o2c k) + cos581o2c 485 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 484) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_484
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 485 - ((879609/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_485).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_486 : ((2644263/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 486, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 486, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 485, cos581o2c k) + cos581o2c 486 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 485) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_485
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 486 - ((49737/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_486).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_487 : ((11341963/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 487, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 487, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 486, cos581o2c k) + cos581o2c 487 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 486) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_486
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 487 - ((765011/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_487).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_488 : ((290339/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 488, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 488, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 487, cos581o2c k) + cos581o2c 488 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 487) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_487
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 488 - ((271697/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_488).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_489 : ((1129937/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 489, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 489, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 488, cos581o2c k) + cos581o2c 489 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 488) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_488
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 489 - ((-31409/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_489).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_490 : ((10507953/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 490, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 490, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 489, cos581o2c k) + cos581o2c 490 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 489) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_489
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 490 - ((-791317/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_490).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_491 : ((4755001/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 491, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 491, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 490, cos581o2c k) + cos581o2c 491 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 490) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_490
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 491 - ((-997851/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_491).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_492 : ((4322411/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 492, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 492, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 491, cos581o2c k) + cos581o2c 492 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 491) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_491
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 492 - ((-21627/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_492).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_493 : ((820483/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 493, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 493, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 492, cos581o2c k) + cos581o2c 493 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 492) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_492
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 493 - ((-109973/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_493).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_494 : ((8337527/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 494, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 494, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 493, cos581o2c k) + cos581o2c 494 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 493) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_493
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 494 - ((132797/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_494).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_495 : ((2249323/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 495, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 495, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 494, cos581o2c k) + cos581o2c 495 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 494) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_494
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 495 - ((131973/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_495).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_496 : ((498129/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 496, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 496, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 495, cos581o2c k) + cos581o2c 496 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 495) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_495
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 496 - ((241347/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_496).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_497 : ((10911329/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 497, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 497, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 496, cos581o2c k) + cos581o2c 497 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 496) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_496
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 497 - ((948849/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_497).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_498 : ((11528811/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 498, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 498, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 497, cos581o2c k) + cos581o2c 498 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 497) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_497
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 498 - ((308791/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_498).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_499 : ((5805769/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 499, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 499, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 498, cos581o2c k) + cos581o2c 499 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 498) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_498
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 499 - ((82827/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_499).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum581o2_500 : ((1113319/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 500, cos581o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 500, cos581o2c k)
      = (∑ k ∈ Finset.Icc 11 499, cos581o2c k) + cos581o2c 500 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 499) (by norm_num) cos581o2c
    simpa using h
  have hprev := psum581o2_499
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos581o2c 500 - ((-59781/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos581o2_br_500).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 16384 in
theorem psum581o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 500 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos581o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum581o2_11
  · exact le_trans (by norm_num) psum581o2_12
  · exact le_trans (by norm_num) psum581o2_13
  · exact le_trans (by norm_num) psum581o2_14
  · exact le_trans (by norm_num) psum581o2_15
  · exact le_trans (by norm_num) psum581o2_16
  · exact le_trans (by norm_num) psum581o2_17
  · exact le_trans (by norm_num) psum581o2_18
  · exact le_trans (by norm_num) psum581o2_19
  · exact le_trans (by norm_num) psum581o2_20
  · exact le_trans (by norm_num) psum581o2_21
  · exact le_trans (by norm_num) psum581o2_22
  · exact le_trans (by norm_num) psum581o2_23
  · exact le_trans (by norm_num) psum581o2_24
  · exact le_trans (by norm_num) psum581o2_25
  · exact le_trans (by norm_num) psum581o2_26
  · exact le_trans (by norm_num) psum581o2_27
  · exact le_trans (by norm_num) psum581o2_28
  · exact le_trans (by norm_num) psum581o2_29
  · exact le_trans (by norm_num) psum581o2_30
  · exact le_trans (by norm_num) psum581o2_31
  · exact le_trans (by norm_num) psum581o2_32
  · exact le_trans (by norm_num) psum581o2_33
  · exact le_trans (by norm_num) psum581o2_34
  · exact le_trans (by norm_num) psum581o2_35
  · exact le_trans (by norm_num) psum581o2_36
  · exact le_trans (by norm_num) psum581o2_37
  · exact le_trans (by norm_num) psum581o2_38
  · exact le_trans (by norm_num) psum581o2_39
  · exact le_trans (by norm_num) psum581o2_40
  · exact le_trans (by norm_num) psum581o2_41
  · exact le_trans (by norm_num) psum581o2_42
  · exact le_trans (by norm_num) psum581o2_43
  · exact le_trans (by norm_num) psum581o2_44
  · exact le_trans (by norm_num) psum581o2_45
  · exact le_trans (by norm_num) psum581o2_46
  · exact le_trans (by norm_num) psum581o2_47
  · exact le_trans (by norm_num) psum581o2_48
  · exact le_trans (by norm_num) psum581o2_49
  · exact le_trans (by norm_num) psum581o2_50
  · exact le_trans (by norm_num) psum581o2_51
  · exact le_trans (by norm_num) psum581o2_52
  · exact le_trans (by norm_num) psum581o2_53
  · exact le_trans (by norm_num) psum581o2_54
  · exact le_trans (by norm_num) psum581o2_55
  · exact le_trans (by norm_num) psum581o2_56
  · exact le_trans (by norm_num) psum581o2_57
  · exact le_trans (by norm_num) psum581o2_58
  · exact le_trans (by norm_num) psum581o2_59
  · exact le_trans (by norm_num) psum581o2_60
  · exact le_trans (by norm_num) psum581o2_61
  · exact le_trans (by norm_num) psum581o2_62
  · exact le_trans (by norm_num) psum581o2_63
  · exact le_trans (by norm_num) psum581o2_64
  · exact le_trans (by norm_num) psum581o2_65
  · exact le_trans (by norm_num) psum581o2_66
  · exact le_trans (by norm_num) psum581o2_67
  · exact le_trans (by norm_num) psum581o2_68
  · exact le_trans (by norm_num) psum581o2_69
  · exact le_trans (by norm_num) psum581o2_70
  · exact le_trans (by norm_num) psum581o2_71
  · exact le_trans (by norm_num) psum581o2_72
  · exact le_trans (by norm_num) psum581o2_73
  · exact le_trans (by norm_num) psum581o2_74
  · exact le_trans (by norm_num) psum581o2_75
  · exact le_trans (by norm_num) psum581o2_76
  · exact le_trans (by norm_num) psum581o2_77
  · exact le_trans (by norm_num) psum581o2_78
  · exact le_trans (by norm_num) psum581o2_79
  · exact le_trans (by norm_num) psum581o2_80
  · exact le_trans (by norm_num) psum581o2_81
  · exact le_trans (by norm_num) psum581o2_82
  · exact le_trans (by norm_num) psum581o2_83
  · exact le_trans (by norm_num) psum581o2_84
  · exact le_trans (by norm_num) psum581o2_85
  · exact le_trans (by norm_num) psum581o2_86
  · exact le_trans (by norm_num) psum581o2_87
  · exact le_trans (by norm_num) psum581o2_88
  · exact le_trans (by norm_num) psum581o2_89
  · exact le_trans (by norm_num) psum581o2_90
  · exact le_trans (by norm_num) psum581o2_91
  · exact le_trans (by norm_num) psum581o2_92
  · exact le_trans (by norm_num) psum581o2_93
  · exact le_trans (by norm_num) psum581o2_94
  · exact le_trans (by norm_num) psum581o2_95
  · exact le_trans (by norm_num) psum581o2_96
  · exact le_trans (by norm_num) psum581o2_97
  · exact le_trans (by norm_num) psum581o2_98
  · exact le_trans (by norm_num) psum581o2_99
  · exact le_trans (by norm_num) psum581o2_100
  · exact le_trans (by norm_num) psum581o2_101
  · exact le_trans (by norm_num) psum581o2_102
  · exact le_trans (by norm_num) psum581o2_103
  · exact le_trans (by norm_num) psum581o2_104
  · exact le_trans (by norm_num) psum581o2_105
  · exact le_trans (by norm_num) psum581o2_106
  · exact le_trans (by norm_num) psum581o2_107
  · exact le_trans (by norm_num) psum581o2_108
  · exact le_trans (by norm_num) psum581o2_109
  · exact le_trans (by norm_num) psum581o2_110
  · exact le_trans (by norm_num) psum581o2_111
  · exact le_trans (by norm_num) psum581o2_112
  · exact le_trans (by norm_num) psum581o2_113
  · exact le_trans (by norm_num) psum581o2_114
  · exact le_trans (by norm_num) psum581o2_115
  · exact le_trans (by norm_num) psum581o2_116
  · exact le_trans (by norm_num) psum581o2_117
  · exact le_trans (by norm_num) psum581o2_118
  · exact le_trans (by norm_num) psum581o2_119
  · exact le_trans (by norm_num) psum581o2_120
  · exact le_trans (by norm_num) psum581o2_121
  · exact le_trans (by norm_num) psum581o2_122
  · exact le_trans (by norm_num) psum581o2_123
  · exact le_trans (by norm_num) psum581o2_124
  · exact le_trans (by norm_num) psum581o2_125
  · exact le_trans (by norm_num) psum581o2_126
  · exact le_trans (by norm_num) psum581o2_127
  · exact le_trans (by norm_num) psum581o2_128
  · exact le_trans (by norm_num) psum581o2_129
  · exact le_trans (by norm_num) psum581o2_130
  · exact le_trans (by norm_num) psum581o2_131
  · exact le_trans (by norm_num) psum581o2_132
  · exact le_trans (by norm_num) psum581o2_133
  · exact le_trans (by norm_num) psum581o2_134
  · exact le_trans (by norm_num) psum581o2_135
  · exact le_trans (by norm_num) psum581o2_136
  · exact le_trans (by norm_num) psum581o2_137
  · exact le_trans (by norm_num) psum581o2_138
  · exact le_trans (by norm_num) psum581o2_139
  · exact le_trans (by norm_num) psum581o2_140
  · exact le_trans (by norm_num) psum581o2_141
  · exact le_trans (by norm_num) psum581o2_142
  · exact le_trans (by norm_num) psum581o2_143
  · exact le_trans (by norm_num) psum581o2_144
  · exact le_trans (by norm_num) psum581o2_145
  · exact le_trans (by norm_num) psum581o2_146
  · exact le_trans (by norm_num) psum581o2_147
  · exact le_trans (by norm_num) psum581o2_148
  · exact le_trans (by norm_num) psum581o2_149
  · exact le_trans (by norm_num) psum581o2_150
  · exact le_trans (by norm_num) psum581o2_151
  · exact le_trans (by norm_num) psum581o2_152
  · exact le_trans (by norm_num) psum581o2_153
  · exact le_trans (by norm_num) psum581o2_154
  · exact le_trans (by norm_num) psum581o2_155
  · exact le_trans (by norm_num) psum581o2_156
  · exact le_trans (by norm_num) psum581o2_157
  · exact le_trans (by norm_num) psum581o2_158
  · exact le_trans (by norm_num) psum581o2_159
  · exact le_trans (by norm_num) psum581o2_160
  · exact le_trans (by norm_num) psum581o2_161
  · exact le_trans (by norm_num) psum581o2_162
  · exact le_trans (by norm_num) psum581o2_163
  · exact le_trans (by norm_num) psum581o2_164
  · exact le_trans (by norm_num) psum581o2_165
  · exact le_trans (by norm_num) psum581o2_166
  · exact le_trans (by norm_num) psum581o2_167
  · exact le_trans (by norm_num) psum581o2_168
  · exact le_trans (by norm_num) psum581o2_169
  · exact le_trans (by norm_num) psum581o2_170
  · exact le_trans (by norm_num) psum581o2_171
  · exact le_trans (by norm_num) psum581o2_172
  · exact le_trans (by norm_num) psum581o2_173
  · exact le_trans (by norm_num) psum581o2_174
  · exact le_trans (by norm_num) psum581o2_175
  · exact le_trans (by norm_num) psum581o2_176
  · exact le_trans (by norm_num) psum581o2_177
  · exact le_trans (by norm_num) psum581o2_178
  · exact le_trans (by norm_num) psum581o2_179
  · exact le_trans (by norm_num) psum581o2_180
  · exact le_trans (by norm_num) psum581o2_181
  · exact le_trans (by norm_num) psum581o2_182
  · exact le_trans (by norm_num) psum581o2_183
  · exact le_trans (by norm_num) psum581o2_184
  · exact le_trans (by norm_num) psum581o2_185
  · exact le_trans (by norm_num) psum581o2_186
  · exact le_trans (by norm_num) psum581o2_187
  · exact le_trans (by norm_num) psum581o2_188
  · exact le_trans (by norm_num) psum581o2_189
  · exact le_trans (by norm_num) psum581o2_190
  · exact le_trans (by norm_num) psum581o2_191
  · exact le_trans (by norm_num) psum581o2_192
  · exact le_trans (by norm_num) psum581o2_193
  · exact le_trans (by norm_num) psum581o2_194
  · exact le_trans (by norm_num) psum581o2_195
  · exact le_trans (by norm_num) psum581o2_196
  · exact le_trans (by norm_num) psum581o2_197
  · exact le_trans (by norm_num) psum581o2_198
  · exact le_trans (by norm_num) psum581o2_199
  · exact le_trans (by norm_num) psum581o2_200
  · exact le_trans (by norm_num) psum581o2_201
  · exact le_trans (by norm_num) psum581o2_202
  · exact le_trans (by norm_num) psum581o2_203
  · exact le_trans (by norm_num) psum581o2_204
  · exact le_trans (by norm_num) psum581o2_205
  · exact le_trans (by norm_num) psum581o2_206
  · exact le_trans (by norm_num) psum581o2_207
  · exact le_trans (by norm_num) psum581o2_208
  · exact le_trans (by norm_num) psum581o2_209
  · exact le_trans (by norm_num) psum581o2_210
  · exact le_trans (by norm_num) psum581o2_211
  · exact le_trans (by norm_num) psum581o2_212
  · exact le_trans (by norm_num) psum581o2_213
  · exact le_trans (by norm_num) psum581o2_214
  · exact le_trans (by norm_num) psum581o2_215
  · exact le_trans (by norm_num) psum581o2_216
  · exact le_trans (by norm_num) psum581o2_217
  · exact le_trans (by norm_num) psum581o2_218
  · exact le_trans (by norm_num) psum581o2_219
  · exact le_trans (by norm_num) psum581o2_220
  · exact le_trans (by norm_num) psum581o2_221
  · exact le_trans (by norm_num) psum581o2_222
  · exact le_trans (by norm_num) psum581o2_223
  · exact le_trans (by norm_num) psum581o2_224
  · exact le_trans (by norm_num) psum581o2_225
  · exact le_trans (by norm_num) psum581o2_226
  · exact le_trans (by norm_num) psum581o2_227
  · exact le_trans (by norm_num) psum581o2_228
  · exact le_trans (by norm_num) psum581o2_229
  · exact le_trans (by norm_num) psum581o2_230
  · exact le_trans (by norm_num) psum581o2_231
  · exact le_trans (by norm_num) psum581o2_232
  · exact le_trans (by norm_num) psum581o2_233
  · exact le_trans (by norm_num) psum581o2_234
  · exact le_trans (by norm_num) psum581o2_235
  · exact le_trans (by norm_num) psum581o2_236
  · exact le_trans (by norm_num) psum581o2_237
  · exact le_trans (by norm_num) psum581o2_238
  · exact le_trans (by norm_num) psum581o2_239
  · exact le_trans (by norm_num) psum581o2_240
  · exact le_trans (by norm_num) psum581o2_241
  · exact le_trans (by norm_num) psum581o2_242
  · exact le_trans (by norm_num) psum581o2_243
  · exact le_trans (by norm_num) psum581o2_244
  · exact le_trans (by norm_num) psum581o2_245
  · exact le_trans (by norm_num) psum581o2_246
  · exact le_trans (by norm_num) psum581o2_247
  · exact le_trans (by norm_num) psum581o2_248
  · exact le_trans (by norm_num) psum581o2_249
  · exact le_trans (by norm_num) psum581o2_250
  · exact le_trans (by norm_num) psum581o2_251
  · exact le_trans (by norm_num) psum581o2_252
  · exact le_trans (by norm_num) psum581o2_253
  · exact le_trans (by norm_num) psum581o2_254
  · exact le_trans (by norm_num) psum581o2_255
  · exact le_trans (by norm_num) psum581o2_256
  · exact le_trans (by norm_num) psum581o2_257
  · exact le_trans (by norm_num) psum581o2_258
  · exact le_trans (by norm_num) psum581o2_259
  · exact le_trans (by norm_num) psum581o2_260
  · exact le_trans (by norm_num) psum581o2_261
  · exact le_trans (by norm_num) psum581o2_262
  · exact le_trans (by norm_num) psum581o2_263
  · exact le_trans (by norm_num) psum581o2_264
  · exact le_trans (by norm_num) psum581o2_265
  · exact le_trans (by norm_num) psum581o2_266
  · exact le_trans (by norm_num) psum581o2_267
  · exact le_trans (by norm_num) psum581o2_268
  · exact le_trans (by norm_num) psum581o2_269
  · exact le_trans (by norm_num) psum581o2_270
  · exact le_trans (by norm_num) psum581o2_271
  · exact le_trans (by norm_num) psum581o2_272
  · exact le_trans (by norm_num) psum581o2_273
  · exact le_trans (by norm_num) psum581o2_274
  · exact le_trans (by norm_num) psum581o2_275
  · exact le_trans (by norm_num) psum581o2_276
  · exact le_trans (by norm_num) psum581o2_277
  · exact le_trans (by norm_num) psum581o2_278
  · exact le_trans (by norm_num) psum581o2_279
  · exact le_trans (by norm_num) psum581o2_280
  · exact le_trans (by norm_num) psum581o2_281
  · exact le_trans (by norm_num) psum581o2_282
  · exact le_trans (by norm_num) psum581o2_283
  · exact le_trans (by norm_num) psum581o2_284
  · exact le_trans (by norm_num) psum581o2_285
  · exact le_trans (by norm_num) psum581o2_286
  · exact le_trans (by norm_num) psum581o2_287
  · exact le_trans (by norm_num) psum581o2_288
  · exact le_trans (by norm_num) psum581o2_289
  · exact le_trans (by norm_num) psum581o2_290
  · exact le_trans (by norm_num) psum581o2_291
  · exact le_trans (by norm_num) psum581o2_292
  · exact le_trans (by norm_num) psum581o2_293
  · exact le_trans (by norm_num) psum581o2_294
  · exact le_trans (by norm_num) psum581o2_295
  · exact le_trans (by norm_num) psum581o2_296
  · exact le_trans (by norm_num) psum581o2_297
  · exact le_trans (by norm_num) psum581o2_298
  · exact le_trans (by norm_num) psum581o2_299
  · exact le_trans (by norm_num) psum581o2_300
  · exact le_trans (by norm_num) psum581o2_301
  · exact le_trans (by norm_num) psum581o2_302
  · exact le_trans (by norm_num) psum581o2_303
  · exact le_trans (by norm_num) psum581o2_304
  · exact le_trans (by norm_num) psum581o2_305
  · exact le_trans (by norm_num) psum581o2_306
  · exact le_trans (by norm_num) psum581o2_307
  · exact le_trans (by norm_num) psum581o2_308
  · exact le_trans (by norm_num) psum581o2_309
  · exact le_trans (by norm_num) psum581o2_310
  · exact le_trans (by norm_num) psum581o2_311
  · exact le_trans (by norm_num) psum581o2_312
  · exact le_trans (by norm_num) psum581o2_313
  · exact le_trans (by norm_num) psum581o2_314
  · exact le_trans (by norm_num) psum581o2_315
  · exact le_trans (by norm_num) psum581o2_316
  · exact le_trans (by norm_num) psum581o2_317
  · exact le_trans (by norm_num) psum581o2_318
  · exact le_trans (by norm_num) psum581o2_319
  · exact le_trans (by norm_num) psum581o2_320
  · exact le_trans (by norm_num) psum581o2_321
  · exact le_trans (by norm_num) psum581o2_322
  · exact le_trans (by norm_num) psum581o2_323
  · exact le_trans (by norm_num) psum581o2_324
  · exact le_trans (by norm_num) psum581o2_325
  · exact le_trans (by norm_num) psum581o2_326
  · exact le_trans (by norm_num) psum581o2_327
  · exact le_trans (by norm_num) psum581o2_328
  · exact le_trans (by norm_num) psum581o2_329
  · exact le_trans (by norm_num) psum581o2_330
  · exact le_trans (by norm_num) psum581o2_331
  · exact le_trans (by norm_num) psum581o2_332
  · exact le_trans (by norm_num) psum581o2_333
  · exact le_trans (by norm_num) psum581o2_334
  · exact le_trans (by norm_num) psum581o2_335
  · exact le_trans (by norm_num) psum581o2_336
  · exact le_trans (by norm_num) psum581o2_337
  · exact le_trans (by norm_num) psum581o2_338
  · exact le_trans (by norm_num) psum581o2_339
  · exact le_trans (by norm_num) psum581o2_340
  · exact le_trans (by norm_num) psum581o2_341
  · exact le_trans (by norm_num) psum581o2_342
  · exact le_trans (by norm_num) psum581o2_343
  · exact le_trans (by norm_num) psum581o2_344
  · exact le_trans (by norm_num) psum581o2_345
  · exact le_trans (by norm_num) psum581o2_346
  · exact le_trans (by norm_num) psum581o2_347
  · exact le_trans (by norm_num) psum581o2_348
  · exact le_trans (by norm_num) psum581o2_349
  · exact le_trans (by norm_num) psum581o2_350
  · exact le_trans (by norm_num) psum581o2_351
  · exact le_trans (by norm_num) psum581o2_352
  · exact le_trans (by norm_num) psum581o2_353
  · exact le_trans (by norm_num) psum581o2_354
  · exact le_trans (by norm_num) psum581o2_355
  · exact le_trans (by norm_num) psum581o2_356
  · exact le_trans (by norm_num) psum581o2_357
  · exact le_trans (by norm_num) psum581o2_358
  · exact le_trans (by norm_num) psum581o2_359
  · exact le_trans (by norm_num) psum581o2_360
  · exact le_trans (by norm_num) psum581o2_361
  · exact le_trans (by norm_num) psum581o2_362
  · exact le_trans (by norm_num) psum581o2_363
  · exact le_trans (by norm_num) psum581o2_364
  · exact le_trans (by norm_num) psum581o2_365
  · exact le_trans (by norm_num) psum581o2_366
  · exact le_trans (by norm_num) psum581o2_367
  · exact le_trans (by norm_num) psum581o2_368
  · exact le_trans (by norm_num) psum581o2_369
  · exact le_trans (by norm_num) psum581o2_370
  · exact le_trans (by norm_num) psum581o2_371
  · exact le_trans (by norm_num) psum581o2_372
  · exact le_trans (by norm_num) psum581o2_373
  · exact le_trans (by norm_num) psum581o2_374
  · exact le_trans (by norm_num) psum581o2_375
  · exact le_trans (by norm_num) psum581o2_376
  · exact le_trans (by norm_num) psum581o2_377
  · exact le_trans (by norm_num) psum581o2_378
  · exact le_trans (by norm_num) psum581o2_379
  · exact le_trans (by norm_num) psum581o2_380
  · exact le_trans (by norm_num) psum581o2_381
  · exact le_trans (by norm_num) psum581o2_382
  · exact le_trans (by norm_num) psum581o2_383
  · exact le_trans (by norm_num) psum581o2_384
  · exact le_trans (by norm_num) psum581o2_385
  · exact le_trans (by norm_num) psum581o2_386
  · exact le_trans (by norm_num) psum581o2_387
  · exact le_trans (by norm_num) psum581o2_388
  · exact le_trans (by norm_num) psum581o2_389
  · exact le_trans (by norm_num) psum581o2_390
  · exact le_trans (by norm_num) psum581o2_391
  · exact le_trans (by norm_num) psum581o2_392
  · exact le_trans (by norm_num) psum581o2_393
  · exact le_trans (by norm_num) psum581o2_394
  · exact le_trans (by norm_num) psum581o2_395
  · exact le_trans (by norm_num) psum581o2_396
  · exact le_trans (by norm_num) psum581o2_397
  · exact le_trans (by norm_num) psum581o2_398
  · exact le_trans (by norm_num) psum581o2_399
  · exact le_trans (by norm_num) psum581o2_400
  · exact le_trans (by norm_num) psum581o2_401
  · exact le_trans (by norm_num) psum581o2_402
  · exact le_trans (by norm_num) psum581o2_403
  · exact le_trans (by norm_num) psum581o2_404
  · exact le_trans (by norm_num) psum581o2_405
  · exact le_trans (by norm_num) psum581o2_406
  · exact le_trans (by norm_num) psum581o2_407
  · exact le_trans (by norm_num) psum581o2_408
  · exact le_trans (by norm_num) psum581o2_409
  · exact le_trans (by norm_num) psum581o2_410
  · exact le_trans (by norm_num) psum581o2_411
  · exact le_trans (by norm_num) psum581o2_412
  · exact le_trans (by norm_num) psum581o2_413
  · exact le_trans (by norm_num) psum581o2_414
  · exact le_trans (by norm_num) psum581o2_415
  · exact le_trans (by norm_num) psum581o2_416
  · exact le_trans (by norm_num) psum581o2_417
  · exact le_trans (by norm_num) psum581o2_418
  · exact le_trans (by norm_num) psum581o2_419
  · exact le_trans (by norm_num) psum581o2_420
  · exact le_trans (by norm_num) psum581o2_421
  · exact le_trans (by norm_num) psum581o2_422
  · exact le_trans (by norm_num) psum581o2_423
  · exact le_trans (by norm_num) psum581o2_424
  · exact le_trans (by norm_num) psum581o2_425
  · exact le_trans (by norm_num) psum581o2_426
  · exact le_trans (by norm_num) psum581o2_427
  · exact le_trans (by norm_num) psum581o2_428
  · exact le_trans (by norm_num) psum581o2_429
  · exact le_trans (by norm_num) psum581o2_430
  · exact le_trans (by norm_num) psum581o2_431
  · exact le_trans (by norm_num) psum581o2_432
  · exact le_trans (by norm_num) psum581o2_433
  · exact le_trans (by norm_num) psum581o2_434
  · exact le_trans (by norm_num) psum581o2_435
  · exact le_trans (by norm_num) psum581o2_436
  · exact le_trans (by norm_num) psum581o2_437
  · exact le_trans (by norm_num) psum581o2_438
  · exact le_trans (by norm_num) psum581o2_439
  · exact le_trans (by norm_num) psum581o2_440
  · exact le_trans (by norm_num) psum581o2_441
  · exact le_trans (by norm_num) psum581o2_442
  · exact le_trans (by norm_num) psum581o2_443
  · exact le_trans (by norm_num) psum581o2_444
  · exact le_trans (by norm_num) psum581o2_445
  · exact le_trans (by norm_num) psum581o2_446
  · exact le_trans (by norm_num) psum581o2_447
  · exact le_trans (by norm_num) psum581o2_448
  · exact le_trans (by norm_num) psum581o2_449
  · exact le_trans (by norm_num) psum581o2_450
  · exact le_trans (by norm_num) psum581o2_451
  · exact le_trans (by norm_num) psum581o2_452
  · exact le_trans (by norm_num) psum581o2_453
  · exact le_trans (by norm_num) psum581o2_454
  · exact le_trans (by norm_num) psum581o2_455
  · exact le_trans (by norm_num) psum581o2_456
  · exact le_trans (by norm_num) psum581o2_457
  · exact le_trans (by norm_num) psum581o2_458
  · exact le_trans (by norm_num) psum581o2_459
  · exact le_trans (by norm_num) psum581o2_460
  · exact le_trans (by norm_num) psum581o2_461
  · exact le_trans (by norm_num) psum581o2_462
  · exact le_trans (by norm_num) psum581o2_463
  · exact le_trans (by norm_num) psum581o2_464
  · exact le_trans (by norm_num) psum581o2_465
  · exact le_trans (by norm_num) psum581o2_466
  · exact le_trans (by norm_num) psum581o2_467
  · exact le_trans (by norm_num) psum581o2_468
  · exact le_trans (by norm_num) psum581o2_469
  · exact le_trans (by norm_num) psum581o2_470
  · exact le_trans (by norm_num) psum581o2_471
  · exact le_trans (by norm_num) psum581o2_472
  · exact le_trans (by norm_num) psum581o2_473
  · exact le_trans (by norm_num) psum581o2_474
  · exact le_trans (by norm_num) psum581o2_475
  · exact le_trans (by norm_num) psum581o2_476
  · exact le_trans (by norm_num) psum581o2_477
  · exact le_trans (by norm_num) psum581o2_478
  · exact le_trans (by norm_num) psum581o2_479
  · exact le_trans (by norm_num) psum581o2_480
  · exact le_trans (by norm_num) psum581o2_481
  · exact le_trans (by norm_num) psum581o2_482
  · exact le_trans (by norm_num) psum581o2_483
  · exact le_trans (by norm_num) psum581o2_484
  · exact le_trans (by norm_num) psum581o2_485
  · exact le_trans (by norm_num) psum581o2_486
  · exact le_trans (by norm_num) psum581o2_487
  · exact le_trans (by norm_num) psum581o2_488
  · exact le_trans (by norm_num) psum581o2_489
  · exact le_trans (by norm_num) psum581o2_490
  · exact le_trans (by norm_num) psum581o2_491
  · exact le_trans (by norm_num) psum581o2_492
  · exact le_trans (by norm_num) psum581o2_493
  · exact le_trans (by norm_num) psum581o2_494
  · exact le_trans (by norm_num) psum581o2_495
  · exact le_trans (by norm_num) psum581o2_496
  · exact le_trans (by norm_num) psum581o2_497
  · exact le_trans (by norm_num) psum581o2_498
  · exact le_trans (by norm_num) psum581o2_499
  · exact le_trans (by norm_num) psum581o2_500

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum581o2_floor
#print axioms CriticalLinePhasor.DVP.psum581o2_500
end AxiomAudit
