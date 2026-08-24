import RequestProject.DVPCos471o2Table

/-!
# The cosine partial-sum floor, `t = 471/2`
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 471/2` segment certificate. -/
def cos471o2c (n : ℕ) : ℝ := Real.cos (((471:ℕ):ℝ) * (Real.log n / 2))

theorem psum471o2_11 : ((709221/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos471o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 11 - ((709261/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum471o2_12 : ((681081/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos471o2c k) + cos471o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_11
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 12 - ((652981/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_13 : ((503681/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos471o2c k) + cos471o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_12
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 13 - ((326301/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_14 : ((2873757/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos471o2c k) + cos471o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_13
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 14 - ((859073/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_15 : ((46843/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos471o2c k) + cos471o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_14
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 15 - ((-999997/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_16 : ((2748069/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos471o2c k) + cos471o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_15
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 16 - ((874389/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_17 : ((3106561/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos471o2c k) + cos471o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_16
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 17 - ((89633/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_18 : ((2602941/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos471o2c k) + cos471o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_17
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 18 - ((-25179/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_19 : ((30674/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos471o2c k) + cos471o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_18
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 19 - ((-127953/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_20 : ((351437/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos471o2c k) + cos471o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_19
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 20 - ((-205911/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_21 : ((1260377/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos471o2c k) + cos471o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_20
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 21 - ((763609/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_22 : ((12541/4000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos471o2c k) + cos471o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_21
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 22 - ((76817/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_23 : ((1072129/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos471o2c k) + cos471o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_22
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 23 - ((-123869/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_24 : ((721909/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos471o2c k) + cos471o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_23
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 24 - ((371709/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_25 : ((2282917/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos471o2c k) + cos471o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_24
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 25 - ((-604679/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_26 : ((75649/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos471o2c k) + cos471o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_25
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 26 - ((743083/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_27 : ((127819/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos471o2c k) + cos471o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_26
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 27 - ((-61301/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_28 : ((1416301/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos471o2c k) + cos471o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_27
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 28 - ((393769/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_29 : ((3083813/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos471o2c k) + cos471o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_28
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 29 - ((251251/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_30 : ((209147/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos471o2c k) + cos471o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_29
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 30 - ((-992303/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_31 : ((183811/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos471o2c k) + cos471o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_30
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 31 - ((-6333/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_32 : ((528833/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos471o2c k) + cos471o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_31
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 32 - ((161219/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_33 : ((718017/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos471o2c k) + cos471o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_32
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 33 - ((23649/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_34 : ((2031811/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos471o2c k) + cos471o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_33
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 34 - ((473577/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_35 : ((4013579/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos471o2c k) + cos471o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_34
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 35 - ((-50003/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_36 : ((3623121/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos471o2c k) + cos471o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_35
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 36 - ((-195209/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_37 : ((1541571/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos471o2c k) + cos471o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_36
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 37 - ((-539939/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_38 : ((2545543/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos471o2c k) + cos471o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_37
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 38 - ((-537559/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_39 : ((17237/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos471o2c k) + cos471o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_38
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 39 - ((-195439/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_40 : ((2073931/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos471o2c k) + cos471o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_39
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 40 - ((-40327/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_41 : ((1225807/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos471o2c k) + cos471o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_40
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 41 - ((377723/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_42 : ((1053/320 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos471o2c k) + cos471o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_41
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 42 - ((839051/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_43 : ((4276757/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos471o2c k) + cos471o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_42
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 43 - ((246543/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_44 : ((4786683/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos471o2c k) + cos471o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_43
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 44 - ((254983/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_45 : ((1086639/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos471o2c k) + cos471o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_44
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 45 - ((-440087/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_46 : ((836637/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos471o2c k) + cos471o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_45
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 46 - ((-31249/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_47 : ((1496981/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos471o2c k) + cos471o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_46
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 47 - ((-176273/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_48 : ((953967/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos471o2c k) + cos471o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_47
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 48 - ((410973/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_49 : ((899407/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos471o2c k) + cos471o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_48
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 49 - ((681207/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_50 : ((1898277/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos471o2c k) + cos471o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_49
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 50 - ((-700441/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_51 : ((1558939/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos471o2c k) + cos471o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_50
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 51 - ((-169659/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_52 : ((3939499/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos471o2c k) + cos471o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_51
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 52 - ((821661/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_53 : ((1077581/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos471o2c k) + cos471o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_52
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 53 - ((74173/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_54 : ((3312701/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos471o2c k) + cos471o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_53
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 54 - ((-997583/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_55 : ((181439/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos471o2c k) + cos471o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_54
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 55 - ((316119/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_56 : ((4332111/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos471o2c k) + cos471o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_55
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 56 - ((703371/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_57 : ((3359789/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos471o2c k) + cos471o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_56
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 57 - ((-486141/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_58 : ((597/160 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos471o2c k) + cos471o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_57
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 58 - ((371501/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_59 : ((1053429/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos471o2c k) + cos471o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_58
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 59 - ((241253/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_60 : ((3244963/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos471o2c k) + cos471o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_59
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 60 - ((-968713/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_61 : ((257649/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos471o2c k) + cos471o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_60
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 61 - ((877461/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_62 : ((3748837/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos471o2c k) + cos471o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_61
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 62 - ((-373507/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_63 : ((109609/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos471o2c k) + cos471o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_62
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 63 - ((-241309/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_64 : ((4232319/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos471o2c k) + cos471o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_63
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 64 - ((724871/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_65 : ((1631721/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos471o2c k) + cos471o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_64
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 65 - ((-968837/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_66 : ((4242747/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos471o2c k) + cos471o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_65
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 66 - ((195869/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_67 : ((683863/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos471o2c k) + cos471o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_66
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 67 - ((-25731/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_68 : ((400031/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos471o2c k) + cos471o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_67
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 68 - ((116207/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_69 : ((460289/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos471o2c k) + cos471o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_68
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 69 - ((-158979/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_70 : ((1879413/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos471o2c k) + cos471o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_69
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 70 - ((38277/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_71 : ((1940367/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos471o2c k) + cos471o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_70
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 71 - ((30487/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_72 : ((3609693/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos471o2c k) + cos471o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_71
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 72 - ((-271001/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_73 : ((3981653/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos471o2c k) + cos471o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_72
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 73 - ((93/250 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_74 : ((3552339/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos471o2c k) + cos471o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_73
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 74 - ((-214637/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_75 : ((499893/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos471o2c k) + cos471o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_74
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 75 - ((89369/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_76 : ((1786181/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos471o2c k) + cos471o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_75
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 76 - ((-213371/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_77 : ((157647/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos471o2c k) + cos471o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_76
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 77 - ((368853/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_78 : ((3669653/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos471o2c k) + cos471o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_77
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 78 - ((-135741/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_79 : ((3802593/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos471o2c k) + cos471o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_78
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 79 - ((6649/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_80 : ((60132/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos471o2c k) + cos471o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_79
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 80 - ((9179/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_81 : ((3589391/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos471o2c k) + cos471o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_80
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 81 - ((-259017/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_82 : ((816201/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos471o2c k) + cos471o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_81
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 82 - ((245827/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_83 : ((1681459/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos471o2c k) + cos471o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_82
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 83 - ((-718047/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_84 : ((852787/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos471o2c k) + cos471o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_83
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 84 - ((901057/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_85 : ((3268311/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos471o2c k) + cos471o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_84
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 85 - ((-15556/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_86 : ((1056401/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos471o2c k) + cos471o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_85
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 86 - ((957333/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_87 : ((1734309/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos471o2c k) + cos471o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_86
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 87 - ((-378473/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_88 : ((773161/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos471o2c k) + cos471o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_87
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 88 - ((397227/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_89 : ((393777/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos471o2c k) + cos471o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_88
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 89 - ((14401/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_90 : ((105867/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos471o2c k) + cos471o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_89
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 90 - ((-274993/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_91 : ((134017/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos471o2c k) + cos471o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_90
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 91 - ((22521/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_92 : ((3295541/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos471o2c k) + cos471o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_91
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 92 - ((-992963/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_93 : ((506379/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos471o2c k) + cos471o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_92
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 93 - ((755531/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_94 : ((477437/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos471o2c k) + cos471o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_93
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 94 - ((-28937/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_95 : ((3415449/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos471o2c k) + cos471o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_94
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 95 - ((-404007/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_96 : ((2151363/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos471o2c k) + cos471o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_95
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 96 - ((887317/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_97 : ((1663597/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos471o2c k) + cos471o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_96
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 97 - ((-243873/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_98 : ((122201/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos471o2c k) + cos471o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_97
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 98 - ((291639/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_99 : ((1009497/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos471o2c k) + cos471o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_98
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 99 - ((31899/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_100 : ((3252951/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos471o2c k) + cos471o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_99
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 100 - ((-784997/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_101 : ((4244451/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos471o2c k) + cos471o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_100
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 101 - ((49577/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_102 : ((732797/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos471o2c k) + cos471o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_101
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 102 - ((-290213/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_103 : ((1720527/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos471o2c k) + cos471o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_102
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 103 - ((-222891/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_104 : ((4328101/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos471o2c k) + cos471o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_103
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 104 - ((887087/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_105 : ((1705107/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos471o2c k) + cos471o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_104
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 105 - ((-917847/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_106 : ((3660739/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos471o2c k) + cos471o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_105
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 106 - ((50113/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_107 : ((214359/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos471o2c k) + cos471o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_106
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 107 - ((626481/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_108 : ((328877/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos471o2c k) + cos471o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_107
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 108 - ((-99837/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_109 : ((761019/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos471o2c k) + cos471o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_108
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 109 - ((103273/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_110 : ((2119239/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos471o2c k) + cos471o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_109
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 110 - ((433423/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_111 : ((1622361/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos471o2c k) + cos471o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_110
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 111 - ((-248429/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_112 : ((481579/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos471o2c k) + cos471o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_111
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 112 - ((12159/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_113 : ((529647/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos471o2c k) + cos471o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_112
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 113 - ((48073/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_114 : ((810777/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos471o2c k) + cos471o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_113
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 114 - ((-248507/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_115 : ((3803853/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos471o2c k) + cos471o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_114
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 115 - ((112157/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_116 : ((4289633/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos471o2c k) + cos471o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_115
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 116 - ((24291/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_117 : ((658239/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos471o2c k) + cos471o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_116
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 117 - ((-499199/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_118 : ((3659159/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos471o2c k) + cos471o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_117
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 118 - ((92001/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_119 : ((4360543/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos471o2c k) + cos471o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_118
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 119 - ((43839/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_120 : ((1715449/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos471o2c k) + cos471o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_119
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 120 - ((-185921/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_121 : ((3436973/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos471o2c k) + cos471o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_120
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 121 - ((1223/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_122 : ((272997/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos471o2c k) + cos471o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_121
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 122 - ((931019/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_123 : ((185229/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos471o2c k) + cos471o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_122
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 123 - ((-165833/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_124 : ((804213/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos471o2c k) + cos471o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_123
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 124 - ((-60961/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_125 : ((419907/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos471o2c k) + cos471o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_124
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 125 - ((491129/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_126 : ((816447/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos471o2c k) + cos471o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_125
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 126 - ((-23359/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_127 : ((1582123/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos471o2c k) + cos471o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_126
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 127 - ((-917949/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_128 : ((759251/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos471o2c k) + cos471o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_127
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 128 - ((632049/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_129 : ((4381061/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos471o2c k) + cos471o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_128
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 129 - ((292423/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_130 : ((3451231/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos471o2c k) + cos471o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_129
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 130 - ((-92979/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_131 : ((165427/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos471o2c k) + cos471o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_130
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 131 - ((-142651/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_132 : ((4305541/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos471o2c k) + cos471o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_131
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 132 - ((997041/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_133 : ((4025767/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos471o2c k) + cos471o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_132
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 133 - ((-139867/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_134 : ((627449/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos471o2c k) + cos471o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_133
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 134 - ((-444241/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_135 : ((3747873/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos471o2c k) + cos471o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_134
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 135 - ((152667/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_136 : ((1106759/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos471o2c k) + cos471o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_135
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 136 - ((679203/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_137 : ((899317/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos471o2c k) + cos471o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_136
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 137 - ((-25929/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_138 : ((3162037/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos471o2c k) + cos471o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_137
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 138 - ((-435191/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_139 : ((2055511/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos471o2c k) + cos471o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_138
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 139 - ((37961/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_140 : ((2156433/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos471o2c k) + cos471o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_139
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 140 - ((50471/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_141 : ((3317617/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos471o2c k) + cos471o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_140
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 141 - ((-995209/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_142 : ((3313177/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos471o2c k) + cos471o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_141
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 142 - ((-11/2500 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_143 : ((4310139/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos471o2c k) + cos471o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_142
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 143 - ((498501/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_144 : ((4162879/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos471o2c k) + cos471o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_143
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 144 - ((-7361/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_145 : ((3184133/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos471o2c k) + cos471o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_144
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 145 - ((-489353/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_146 : ((429483/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos471o2c k) + cos471o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_145
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 146 - ((251771/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_147 : ((109843/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos471o2c k) + cos471o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_146
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 147 - ((119737/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_148 : ((510241/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos471o2c k) + cos471o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_147
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 148 - ((-38969/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_149 : ((627307/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos471o2c k) + cos471o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_148
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 149 - ((-945353/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_150 : ((3466737/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos471o2c k) + cos471o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_149
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 150 - ((165121/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_151 : ((1103139/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos471o2c k) + cos471o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_150
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 151 - ((945859/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_152 : ((4103427/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos471o2c k) + cos471o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_151
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 152 - ((-309089/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_153 : ((314449/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos471o2c k) + cos471o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_152
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 153 - ((-958897/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_154 : ((3392941/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos471o2c k) + cos471o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_153
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 154 - ((248491/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_155 : ((4372043/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos471o2c k) + cos471o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_154
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 155 - ((489571/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_156 : ((844853/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos471o2c k) + cos471o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_155
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 156 - ((-73869/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_157 : ((403451/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos471o2c k) + cos471o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_156
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 157 - ((-996617/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_158 : ((323429/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos471o2c k) + cos471o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_157
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 158 - ((3361/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_159 : ((4231189/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos471o2c k) + cos471o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_158
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 159 - ((996939/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_160 : ((4402857/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos471o2c k) + cos471o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_159
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 160 - ((42927/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_161 : ((688137/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos471o2c k) + cos471o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_160
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 161 - ((-240533/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_162 : ((3061699/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos471o2c k) + cos471o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_161
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 162 - ((-189473/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_163 : ((3934301/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos471o2c k) + cos471o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_162
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 163 - ((436321/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_164 : ((4531971/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos471o2c k) + cos471o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_163
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 164 - ((59771/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_165 : ((38209/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos471o2c k) + cos471o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_164
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 165 - ((-711031/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_166 : ((3020637/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos471o2c k) + cos471o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_165
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 166 - ((-800223/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_167 : ((348837/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos471o2c k) + cos471o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_166
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 167 - ((467773/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_168 : ((1109239/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos471o2c k) + cos471o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_167
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 168 - ((474313/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_169 : ((1072171/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos471o2c k) + cos471o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_168
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 169 - ((-18529/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_170 : ((3289177/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos471o2c k) + cos471o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_169
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 170 - ((-999467/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_171 : ((3068759/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos471o2c k) + cos471o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_170
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 171 - ((-110189/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_172 : ((3981881/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos471o2c k) + cos471o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_171
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 172 - ((456581/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_173 : ((4567263/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos471o2c k) + cos471o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_172
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 173 - ((292711/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_174 : ((3898901/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos471o2c k) + cos471o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_173
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 174 - ((-334161/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_175 : ((121059/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos471o2c k) + cos471o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_174
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 175 - ((-436193/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_176 : ((3304537/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos471o2c k) + cos471o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_175
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 176 - ((139051/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_177 : ((430347/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos471o2c k) + cos471o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_176
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 177 - ((998973/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_178 : ((900169/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos471o2c k) + cos471o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_177
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 178 - ((39483/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_179 : ((1800217/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos471o2c k) + cos471o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_178
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 179 - ((-900371/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_180 : ((2949319/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos471o2c k) + cos471o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_179
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 180 - ((-26043/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_181 : ((3510381/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos471o2c k) + cos471o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_180
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 181 - ((280551/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_182 : ((4458809/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos471o2c k) + cos471o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_181
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 182 - ((237117/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_183 : ((1104181/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos471o2c k) + cos471o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_182
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 183 - ((-8409/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_184 : ((1723317/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos471o2c k) + cos471o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_183
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 184 - ((-19401/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_185 : ((2932697/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos471o2c k) + cos471o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_184
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 185 - ((-513897/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_186 : ((3599387/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos471o2c k) + cos471o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_185
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 186 - ((66673/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_187 : ((2255857/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos471o2c k) + cos471o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_186
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 187 - ((912367/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_188 : ((880983/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos471o2c k) + cos471o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_187
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 188 - ((-106759/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_189 : ((856947/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos471o2c k) + cos471o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_188
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 189 - ((-977087/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_190 : ((2911431/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos471o2c k) + cos471o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_189
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 190 - ((-516317/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_191 : ((221923/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos471o2c k) + cos471o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_190
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 191 - ((639377/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_192 : ((4489189/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos471o2c k) + cos471o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_191
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 192 - ((938461/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_193 : ((4483921/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos471o2c k) + cos471o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_192
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 193 - ((-1307/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_194 : ((885999/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos471o2c k) + cos471o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_193
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 194 - ((-187977/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_195 : ((144663/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos471o2c k) + cos471o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_194
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 195 - ((-81337/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_196 : ((421153/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos471o2c k) + cos471o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_195
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 196 - ((119001/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_197 : ((1090383/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos471o2c k) + cos471o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_196
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 197 - ((248087/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_198 : ((4613347/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos471o2c k) + cos471o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_197
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 198 - ((50371/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_199 : ((3810609/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos471o2c k) + cos471o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_198
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 199 - ((-401349/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_200 : ((369201/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos471o2c k) + cos471o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_199
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 200 - ((-856961/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_201 : ((1549147/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos471o2c k) + cos471o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_200
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 201 - ((72363/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_202 : ((81309/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos471o2c k) + cos471o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_201
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 202 - ((241799/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_203 : ((468221/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos471o2c k) + cos471o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_202
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 203 - ((771/1250 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_204 : ((4209273/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos471o2c k) + cos471o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_203
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 204 - ((-472897/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_205 : ((802981/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos471o2c k) + cos471o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_204
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 205 - ((-997309/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_206 : ((1433821/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos471o2c k) + cos471o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_205
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 206 - ((-172121/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_207 : ((3577251/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos471o2c k) + cos471o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_206
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 207 - ((709649/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_208 : ((4515499/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos471o2c k) + cos471o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_207
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 208 - ((58643/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_209 : ((4603487/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos471o2c k) + cos471o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_208
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 209 - ((22007/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_210 : ((374309/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos471o2c k) + cos471o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_209
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 210 - ((-860357/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_211 : ((2908753/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos471o2c k) + cos471o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_210
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 211 - ((-834297/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_212 : ((3034987/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos471o2c k) + cos471o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_211
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 212 - ((63137/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_213 : ((1989523/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos471o2c k) + cos471o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_212
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 213 - ((944099/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_214 : ((4698923/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos471o2c k) + cos471o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_213
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 214 - ((719917/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_215 : ((1102223/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos471o2c k) + cos471o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_214
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 215 - ((-289991/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_216 : ((3425689/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos471o2c k) + cos471o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_215
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 216 - ((-983163/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_217 : ((2807167/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos471o2c k) + cos471o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_216
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 217 - ((-309241/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_218 : ((642237/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos471o2c k) + cos471o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_217
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 218 - ((202029/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_219 : ((4208179/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos471o2c k) + cos471o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_218
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 219 - ((498517/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_220 : ((1187981/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos471o2c k) + cos471o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_219
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 220 - ((108757/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_221 : ((2139263/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos471o2c k) + cos471o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_220
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 221 - ((-236679/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_222 : ((3278591/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos471o2c k) + cos471o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_221
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 222 - ((-199979/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_223 : ((2775717/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos471o2c k) + cos471o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_222
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 223 - ((-251417/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_224 : ((3278467/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos471o2c k) + cos471o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_223
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 224 - ((50279/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_225 : ((2139207/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos471o2c k) + cos471o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_224
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 225 - ((999987/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_226 : ((4776487/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos471o2c k) + cos471o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_225
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 226 - ((498113/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_227 : ((4281023/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos471o2c k) + cos471o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_226
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 227 - ((-7741/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_228 : ((3281133/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos471o2c k) + cos471o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_227
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 228 - ((-19997/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_229 : ((2752057/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos471o2c k) + cos471o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_228
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 229 - ((-132259/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_230 : ((3203727/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos471o2c k) + cos471o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_229
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 230 - ((45171/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_231 : ((840091/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos471o2c k) + cos471o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_230
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 231 - ((31149/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_232 : ((4792749/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos471o2c k) + cos471o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_231
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 232 - ((296167/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_233 : ((2211379/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos471o2c k) + cos471o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_232
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 233 - ((-369951/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_234 : ((429933/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos471o2c k) + cos471o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_233
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 234 - ((-491627/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_235 : ((172371/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos471o2c k) + cos471o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_234
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 235 - ((-42593/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_236 : ((3005503/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos471o2c k) + cos471o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_235
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 236 - ((247607/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_237 : ((395317/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos471o2c k) + cos471o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_236
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 237 - ((947707/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_238 : ((2369483/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos471o2c k) + cos471o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_237
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 238 - ((196459/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_239 : ((4655641/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos471o2c k) + cos471o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_238
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 239 - ((-16657/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_240 : ((755999/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos471o2c k) + cos471o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_239
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 240 - ((-437803/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_241 : ((722677/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos471o2c k) + cos471o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_240
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 241 - ((-889247/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_242 : ((2770423/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos471o2c k) + cos471o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_241
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 242 - ((-24049/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_243 : ((440257/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos471o2c k) + cos471o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_242
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 243 - ((751673/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_244 : ((4491679/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos471o2c k) + cos471o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_243
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 244 - ((969663/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_245 : ((2422267/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos471o2c k) + cos471o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_244
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 245 - ((70579/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_246 : ((4280999/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos471o2c k) + cos471o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_245
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 246 - ((-112699/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_247 : ((32811/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos471o2c k) + cos471o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_246
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 247 - ((-999859/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_248 : ((671751/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos471o2c k) + cos471o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_247
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 248 - ((-74257/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_249 : ((2993531/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos471o2c k) + cos471o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_248
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 249 - ((306567/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum471o2_250 : ((3944193/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos471o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos471o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos471o2c k) + cos471o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos471o2c
    simpa using h
  have hprev := psum471o2_249
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos471o2c 250 - ((475351/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos471o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 3200000 in
/-- **The Abel floor at `t = 471/2`.** -/
theorem psum471o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 250 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos471o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum471o2_11
  · exact le_trans (by norm_num) psum471o2_12
  · exact le_trans (by norm_num) psum471o2_13
  · exact le_trans (by norm_num) psum471o2_14
  · exact le_trans (by norm_num) psum471o2_15
  · exact le_trans (by norm_num) psum471o2_16
  · exact le_trans (by norm_num) psum471o2_17
  · exact le_trans (by norm_num) psum471o2_18
  · exact le_trans (by norm_num) psum471o2_19
  · exact le_trans (by norm_num) psum471o2_20
  · exact le_trans (by norm_num) psum471o2_21
  · exact le_trans (by norm_num) psum471o2_22
  · exact le_trans (by norm_num) psum471o2_23
  · exact le_trans (by norm_num) psum471o2_24
  · exact le_trans (by norm_num) psum471o2_25
  · exact le_trans (by norm_num) psum471o2_26
  · exact le_trans (by norm_num) psum471o2_27
  · exact le_trans (by norm_num) psum471o2_28
  · exact le_trans (by norm_num) psum471o2_29
  · exact le_trans (by norm_num) psum471o2_30
  · exact le_trans (by norm_num) psum471o2_31
  · exact le_trans (by norm_num) psum471o2_32
  · exact le_trans (by norm_num) psum471o2_33
  · exact le_trans (by norm_num) psum471o2_34
  · exact le_trans (by norm_num) psum471o2_35
  · exact le_trans (by norm_num) psum471o2_36
  · exact le_trans (by norm_num) psum471o2_37
  · exact le_trans (by norm_num) psum471o2_38
  · exact le_trans (by norm_num) psum471o2_39
  · exact le_trans (by norm_num) psum471o2_40
  · exact le_trans (by norm_num) psum471o2_41
  · exact le_trans (by norm_num) psum471o2_42
  · exact le_trans (by norm_num) psum471o2_43
  · exact le_trans (by norm_num) psum471o2_44
  · exact le_trans (by norm_num) psum471o2_45
  · exact le_trans (by norm_num) psum471o2_46
  · exact le_trans (by norm_num) psum471o2_47
  · exact le_trans (by norm_num) psum471o2_48
  · exact le_trans (by norm_num) psum471o2_49
  · exact le_trans (by norm_num) psum471o2_50
  · exact le_trans (by norm_num) psum471o2_51
  · exact le_trans (by norm_num) psum471o2_52
  · exact le_trans (by norm_num) psum471o2_53
  · exact le_trans (by norm_num) psum471o2_54
  · exact le_trans (by norm_num) psum471o2_55
  · exact le_trans (by norm_num) psum471o2_56
  · exact le_trans (by norm_num) psum471o2_57
  · exact le_trans (by norm_num) psum471o2_58
  · exact le_trans (by norm_num) psum471o2_59
  · exact le_trans (by norm_num) psum471o2_60
  · exact le_trans (by norm_num) psum471o2_61
  · exact le_trans (by norm_num) psum471o2_62
  · exact le_trans (by norm_num) psum471o2_63
  · exact le_trans (by norm_num) psum471o2_64
  · exact le_trans (by norm_num) psum471o2_65
  · exact le_trans (by norm_num) psum471o2_66
  · exact le_trans (by norm_num) psum471o2_67
  · exact le_trans (by norm_num) psum471o2_68
  · exact le_trans (by norm_num) psum471o2_69
  · exact le_trans (by norm_num) psum471o2_70
  · exact le_trans (by norm_num) psum471o2_71
  · exact le_trans (by norm_num) psum471o2_72
  · exact le_trans (by norm_num) psum471o2_73
  · exact le_trans (by norm_num) psum471o2_74
  · exact le_trans (by norm_num) psum471o2_75
  · exact le_trans (by norm_num) psum471o2_76
  · exact le_trans (by norm_num) psum471o2_77
  · exact le_trans (by norm_num) psum471o2_78
  · exact le_trans (by norm_num) psum471o2_79
  · exact le_trans (by norm_num) psum471o2_80
  · exact le_trans (by norm_num) psum471o2_81
  · exact le_trans (by norm_num) psum471o2_82
  · exact le_trans (by norm_num) psum471o2_83
  · exact le_trans (by norm_num) psum471o2_84
  · exact le_trans (by norm_num) psum471o2_85
  · exact le_trans (by norm_num) psum471o2_86
  · exact le_trans (by norm_num) psum471o2_87
  · exact le_trans (by norm_num) psum471o2_88
  · exact le_trans (by norm_num) psum471o2_89
  · exact le_trans (by norm_num) psum471o2_90
  · exact le_trans (by norm_num) psum471o2_91
  · exact le_trans (by norm_num) psum471o2_92
  · exact le_trans (by norm_num) psum471o2_93
  · exact le_trans (by norm_num) psum471o2_94
  · exact le_trans (by norm_num) psum471o2_95
  · exact le_trans (by norm_num) psum471o2_96
  · exact le_trans (by norm_num) psum471o2_97
  · exact le_trans (by norm_num) psum471o2_98
  · exact le_trans (by norm_num) psum471o2_99
  · exact le_trans (by norm_num) psum471o2_100
  · exact le_trans (by norm_num) psum471o2_101
  · exact le_trans (by norm_num) psum471o2_102
  · exact le_trans (by norm_num) psum471o2_103
  · exact le_trans (by norm_num) psum471o2_104
  · exact le_trans (by norm_num) psum471o2_105
  · exact le_trans (by norm_num) psum471o2_106
  · exact le_trans (by norm_num) psum471o2_107
  · exact le_trans (by norm_num) psum471o2_108
  · exact le_trans (by norm_num) psum471o2_109
  · exact le_trans (by norm_num) psum471o2_110
  · exact le_trans (by norm_num) psum471o2_111
  · exact le_trans (by norm_num) psum471o2_112
  · exact le_trans (by norm_num) psum471o2_113
  · exact le_trans (by norm_num) psum471o2_114
  · exact le_trans (by norm_num) psum471o2_115
  · exact le_trans (by norm_num) psum471o2_116
  · exact le_trans (by norm_num) psum471o2_117
  · exact le_trans (by norm_num) psum471o2_118
  · exact le_trans (by norm_num) psum471o2_119
  · exact le_trans (by norm_num) psum471o2_120
  · exact le_trans (by norm_num) psum471o2_121
  · exact le_trans (by norm_num) psum471o2_122
  · exact le_trans (by norm_num) psum471o2_123
  · exact le_trans (by norm_num) psum471o2_124
  · exact le_trans (by norm_num) psum471o2_125
  · exact le_trans (by norm_num) psum471o2_126
  · exact le_trans (by norm_num) psum471o2_127
  · exact le_trans (by norm_num) psum471o2_128
  · exact le_trans (by norm_num) psum471o2_129
  · exact le_trans (by norm_num) psum471o2_130
  · exact le_trans (by norm_num) psum471o2_131
  · exact le_trans (by norm_num) psum471o2_132
  · exact le_trans (by norm_num) psum471o2_133
  · exact le_trans (by norm_num) psum471o2_134
  · exact le_trans (by norm_num) psum471o2_135
  · exact le_trans (by norm_num) psum471o2_136
  · exact le_trans (by norm_num) psum471o2_137
  · exact le_trans (by norm_num) psum471o2_138
  · exact le_trans (by norm_num) psum471o2_139
  · exact le_trans (by norm_num) psum471o2_140
  · exact le_trans (by norm_num) psum471o2_141
  · exact le_trans (by norm_num) psum471o2_142
  · exact le_trans (by norm_num) psum471o2_143
  · exact le_trans (by norm_num) psum471o2_144
  · exact le_trans (by norm_num) psum471o2_145
  · exact le_trans (by norm_num) psum471o2_146
  · exact le_trans (by norm_num) psum471o2_147
  · exact le_trans (by norm_num) psum471o2_148
  · exact le_trans (by norm_num) psum471o2_149
  · exact le_trans (by norm_num) psum471o2_150
  · exact le_trans (by norm_num) psum471o2_151
  · exact le_trans (by norm_num) psum471o2_152
  · exact le_trans (by norm_num) psum471o2_153
  · exact le_trans (by norm_num) psum471o2_154
  · exact le_trans (by norm_num) psum471o2_155
  · exact le_trans (by norm_num) psum471o2_156
  · exact le_trans (by norm_num) psum471o2_157
  · exact le_trans (by norm_num) psum471o2_158
  · exact le_trans (by norm_num) psum471o2_159
  · exact le_trans (by norm_num) psum471o2_160
  · exact le_trans (by norm_num) psum471o2_161
  · exact le_trans (by norm_num) psum471o2_162
  · exact le_trans (by norm_num) psum471o2_163
  · exact le_trans (by norm_num) psum471o2_164
  · exact le_trans (by norm_num) psum471o2_165
  · exact le_trans (by norm_num) psum471o2_166
  · exact le_trans (by norm_num) psum471o2_167
  · exact le_trans (by norm_num) psum471o2_168
  · exact le_trans (by norm_num) psum471o2_169
  · exact le_trans (by norm_num) psum471o2_170
  · exact le_trans (by norm_num) psum471o2_171
  · exact le_trans (by norm_num) psum471o2_172
  · exact le_trans (by norm_num) psum471o2_173
  · exact le_trans (by norm_num) psum471o2_174
  · exact le_trans (by norm_num) psum471o2_175
  · exact le_trans (by norm_num) psum471o2_176
  · exact le_trans (by norm_num) psum471o2_177
  · exact le_trans (by norm_num) psum471o2_178
  · exact le_trans (by norm_num) psum471o2_179
  · exact le_trans (by norm_num) psum471o2_180
  · exact le_trans (by norm_num) psum471o2_181
  · exact le_trans (by norm_num) psum471o2_182
  · exact le_trans (by norm_num) psum471o2_183
  · exact le_trans (by norm_num) psum471o2_184
  · exact le_trans (by norm_num) psum471o2_185
  · exact le_trans (by norm_num) psum471o2_186
  · exact le_trans (by norm_num) psum471o2_187
  · exact le_trans (by norm_num) psum471o2_188
  · exact le_trans (by norm_num) psum471o2_189
  · exact le_trans (by norm_num) psum471o2_190
  · exact le_trans (by norm_num) psum471o2_191
  · exact le_trans (by norm_num) psum471o2_192
  · exact le_trans (by norm_num) psum471o2_193
  · exact le_trans (by norm_num) psum471o2_194
  · exact le_trans (by norm_num) psum471o2_195
  · exact le_trans (by norm_num) psum471o2_196
  · exact le_trans (by norm_num) psum471o2_197
  · exact le_trans (by norm_num) psum471o2_198
  · exact le_trans (by norm_num) psum471o2_199
  · exact le_trans (by norm_num) psum471o2_200
  · exact le_trans (by norm_num) psum471o2_201
  · exact le_trans (by norm_num) psum471o2_202
  · exact le_trans (by norm_num) psum471o2_203
  · exact le_trans (by norm_num) psum471o2_204
  · exact le_trans (by norm_num) psum471o2_205
  · exact le_trans (by norm_num) psum471o2_206
  · exact le_trans (by norm_num) psum471o2_207
  · exact le_trans (by norm_num) psum471o2_208
  · exact le_trans (by norm_num) psum471o2_209
  · exact le_trans (by norm_num) psum471o2_210
  · exact le_trans (by norm_num) psum471o2_211
  · exact le_trans (by norm_num) psum471o2_212
  · exact le_trans (by norm_num) psum471o2_213
  · exact le_trans (by norm_num) psum471o2_214
  · exact le_trans (by norm_num) psum471o2_215
  · exact le_trans (by norm_num) psum471o2_216
  · exact le_trans (by norm_num) psum471o2_217
  · exact le_trans (by norm_num) psum471o2_218
  · exact le_trans (by norm_num) psum471o2_219
  · exact le_trans (by norm_num) psum471o2_220
  · exact le_trans (by norm_num) psum471o2_221
  · exact le_trans (by norm_num) psum471o2_222
  · exact le_trans (by norm_num) psum471o2_223
  · exact le_trans (by norm_num) psum471o2_224
  · exact le_trans (by norm_num) psum471o2_225
  · exact le_trans (by norm_num) psum471o2_226
  · exact le_trans (by norm_num) psum471o2_227
  · exact le_trans (by norm_num) psum471o2_228
  · exact le_trans (by norm_num) psum471o2_229
  · exact le_trans (by norm_num) psum471o2_230
  · exact le_trans (by norm_num) psum471o2_231
  · exact le_trans (by norm_num) psum471o2_232
  · exact le_trans (by norm_num) psum471o2_233
  · exact le_trans (by norm_num) psum471o2_234
  · exact le_trans (by norm_num) psum471o2_235
  · exact le_trans (by norm_num) psum471o2_236
  · exact le_trans (by norm_num) psum471o2_237
  · exact le_trans (by norm_num) psum471o2_238
  · exact le_trans (by norm_num) psum471o2_239
  · exact le_trans (by norm_num) psum471o2_240
  · exact le_trans (by norm_num) psum471o2_241
  · exact le_trans (by norm_num) psum471o2_242
  · exact le_trans (by norm_num) psum471o2_243
  · exact le_trans (by norm_num) psum471o2_244
  · exact le_trans (by norm_num) psum471o2_245
  · exact le_trans (by norm_num) psum471o2_246
  · exact le_trans (by norm_num) psum471o2_247
  · exact le_trans (by norm_num) psum471o2_248
  · exact le_trans (by norm_num) psum471o2_249
  · exact le_trans (by norm_num) psum471o2_250

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum471o2_floor
#print axioms CriticalLinePhasor.DVP.psum471o2_250
end AxiomAudit
