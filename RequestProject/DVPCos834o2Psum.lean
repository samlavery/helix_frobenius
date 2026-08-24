import RequestProject.DVPCos834o2Table

/-!
# The cosine partial-sum floor, `t = 834/2` (N = 500)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 834/2` segment certificate. -/
def cos834o2c (n : ℕ) : ℝ := Real.cos (((834:ℕ):ℝ) * (Real.log n / 2))

theorem psum834o2_11 : ((624751/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos834o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 11 - ((624851/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum834o2_12 : ((1492717/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos834o2c k) + cos834o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_11
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 12 - ((434033/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_13 : ((405171/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos834o2c k) + cos834o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_12
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 13 - ((128067/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_14 : ((221883/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos834o2c k) + cos834o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_13
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 14 - ((299123/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_15 : ((2073639/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos834o2c k) + cos834o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_14
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 15 - ((-145091/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_16 : ((3071529/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos834o2c k) + cos834o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_15
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 16 - ((99799/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_17 : ((506153/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos834o2c k) + cos834o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_16
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 17 - ((195559/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_18 : ((4514657/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos834o2c k) + cos834o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_17
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 18 - ((465533/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_19 : ((3652603/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos834o2c k) + cos834o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_18
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 19 - ((-430977/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_20 : ((4075969/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos834o2c k) + cos834o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_19
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 20 - ((211733/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_21 : ((5010907/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos834o2c k) + cos834o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_20
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 21 - ((467519/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_22 : ((5623199/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos834o2c k) + cos834o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_21
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 22 - ((76549/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_23 : ((201539/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos834o2c k) + cos834o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_22
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 23 - ((826149/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_24 : ((3662489/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos834o2c k) + cos834o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_23
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 24 - ((87583/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_25 : ((265449/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos834o2c k) + cos834o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_24
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 25 - ((-688653/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_26 : ((6748449/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos834o2c k) + cos834o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_25
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 26 - ((28081/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_27 : ((833203/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos834o2c k) + cos834o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_26
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 27 - ((-3309/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_28 : ((1812747/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos834o2c k) + cos834o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_27
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 28 - ((73183/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_29 : ((6259267/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos834o2c k) + cos834o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_28
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 29 - ((-991621/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_30 : ((6129743/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos834o2c k) + cos834o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_29
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 30 - ((-8089/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_31 : ((3479297/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos834o2c k) + cos834o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_30
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 31 - ((828951/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_32 : ((3977677/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos834o2c k) + cos834o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_31
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 32 - ((49843/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_33 : ((1779289/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos834o2c k) + cos834o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_32
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 33 - ((941191/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_34 : ((4935347/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos834o2c k) + cos834o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_33
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 34 - ((974349/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_35 : ((1083911/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos834o2c k) + cos834o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_34
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 35 - ((242129/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_36 : ((11318519/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos834o2c k) + cos834o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_35
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 36 - ((479509/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_37 : ((2680127/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos834o2c k) + cos834o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_36
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 37 - ((-597911/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_38 : ((9850523/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos834o2c k) + cos834o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_37
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 38 - ((-173977/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_39 : ((10478919/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos834o2c k) + cos834o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_38
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 39 - ((39281/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_40 : ((5458299/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos834o2c k) + cos834o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_39
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 40 - ((437779/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_41 : ((1989303/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos834o2c k) + cos834o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_40
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 41 - ((-969983/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_42 : ((10875713/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos834o2c k) + cos834o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_41
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 42 - ((464649/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_43 : ((2030947/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos834o2c k) + cos834o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_42
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 43 - ((-360439/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_44 : ((5377207/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos834o2c k) + cos834o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_43
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 44 - ((599779/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_45 : ((10112513/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos834o2c k) + cos834o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_44
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 45 - ((-641801/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_46 : ((10929547/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos834o2c k) + cos834o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_45
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 46 - ((408567/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_47 : ((497093/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos834o2c k) + cos834o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_46
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 47 - ((-987587/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_48 : ((10825133/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos834o2c k) + cos834o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_47
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 48 - ((883373/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_49 : ((2642849/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos834o2c k) + cos834o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_48
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 49 - ((-253637/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_50 : ((2473557/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos834o2c k) + cos834o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_49
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 50 - ((-169267/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_51 : ((541843/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos834o2c k) + cos834o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_50
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 51 - ((235683/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_52 : ((170833/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos834o2c k) + cos834o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_51
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 52 - ((12069/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_53 : ((9933241/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos834o2c k) + cos834o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_52
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 53 - ((-999971/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_54 : ((986623/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos834o2c k) + cos834o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_53
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 54 - ((-66911/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_55 : ((10830069/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos834o2c k) + cos834o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_54
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 55 - ((963939/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_56 : ((11402537/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos834o2c k) + cos834o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_55
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 56 - ((71571/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_57 : ((5466827/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos834o2c k) + cos834o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_56
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 57 - ((-468783/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_58 : ((994001/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos834o2c k) + cos834o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_57
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 58 - ((-124193/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_59 : ((9195731/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos834o2c k) + cos834o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_58
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 59 - ((-744179/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_60 : ((9081947/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos834o2c k) + cos834o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_59
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 60 - ((-28421/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_61 : ((9557409/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos834o2c k) + cos834o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_60
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 61 - ((237781/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_62 : ((5197501/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos834o2c k) + cos834o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_61
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 62 - ((837693/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_63 : ((5688569/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos834o2c k) + cos834o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_62
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 63 - ((245559/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_64 : ((12372521/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos834o2c k) + cos834o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_63
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 64 - ((995483/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_65 : ((13334259/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos834o2c k) + cos834o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_64
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 65 - ((480919/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_66 : ((7134937/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos834o2c k) + cos834o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_65
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 66 - ((187143/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_67 : ((3041957/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos834o2c k) + cos834o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_66
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 67 - ((940011/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_68 : ((16180343/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos834o2c k) + cos834o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_67
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 68 - ((485329/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_69 : ((8589561/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos834o2c k) + cos834o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_68
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 69 - ((998879/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_70 : ((4537841/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos834o2c k) + cos834o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_69
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 70 - ((486171/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_71 : ((9487183/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos834o2c k) + cos834o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_70
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 71 - ((411551/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_72 : ((1946763/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos834o2c k) + cos834o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_71
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 72 - ((123341/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_73 : ((3890421/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos834o2c k) + cos834o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_72
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 73 - ((-617/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_74 : ((9433423/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos834o2c k) + cos834o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_73
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 74 - ((-585159/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_75 : ((4475087/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos834o2c k) + cos834o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_74
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 75 - ((-483199/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_76 : ((17022651/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos834o2c k) + cos834o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_75
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 76 - ((-877597/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_77 : ((2098263/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos834o2c k) + cos834o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_76
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 77 - ((-236447/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_78 : ((17402087/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos834o2c k) + cos834o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_77
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 78 - ((616083/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_79 : ((18399941/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos834o2c k) + cos834o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_78
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 79 - ((498977/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_80 : ((9425911/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos834o2c k) + cos834o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_79
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 80 - ((451981/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_81 : ((2282417/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos834o2c k) + cos834o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_80
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 81 - ((-296193/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_82 : ((8642759/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos834o2c k) + cos834o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_81
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 82 - ((-486859/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_83 : ((3434639/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos834o2c k) + cos834o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_82
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 83 - ((-112223/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_84 : ((4524107/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos834o2c k) + cos834o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_83
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 84 - ((923333/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_85 : ((4668669/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos834o2c k) + cos834o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_84
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 85 - ((144587/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_86 : ((71859/4000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos834o2c k) + cos834o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_85
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 86 - ((-354913/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_87 : ((8593773/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos834o2c k) + cos834o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_86
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 87 - ((-48569/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_88 : ((888723/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos834o2c k) + cos834o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_87
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 88 - ((293507/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_89 : ((4645911/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos834o2c k) + cos834o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_88
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 89 - ((202321/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_90 : ((280531/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos834o2c k) + cos834o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_89
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 90 - ((-15739/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_91 : ((17246911/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos834o2c k) + cos834o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_90
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 91 - ((-706973/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_92 : ((18054701/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos834o2c k) + cos834o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_91
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 92 - ((80789/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_93 : ((18467823/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos834o2c k) + cos834o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_92
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 93 - ((206611/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_94 : ((17482743/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos834o2c k) + cos834o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_93
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 94 - ((-49249/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_95 : ((8804211/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos834o2c k) + cos834o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_94
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 95 - ((125779/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_96 : ((18498997/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos834o2c k) + cos834o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_95
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 96 - ((35627/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_97 : ((8869527/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos834o2c k) + cos834o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_96
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 97 - ((-759843/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_98 : ((1747001/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos834o2c k) + cos834o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_97
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 98 - ((-16809/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_99 : ((1153041/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos834o2c k) + cos834o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_98
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 99 - ((489373/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_100 : ((17783211/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos834o2c k) + cos834o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_99
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 100 - ((-133069/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_101 : ((17506977/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos834o2c k) + cos834o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_100
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 101 - ((-138067/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_102 : ((18454779/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos834o2c k) + cos834o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_101
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 102 - ((473951/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_103 : ((550961/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos834o2c k) + cos834o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_102
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 103 - ((-823927/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_104 : ((354229/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos834o2c k) + cos834o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_103
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 104 - ((40399/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_105 : ((368121/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos834o2c k) + cos834o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_104
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 105 - ((6947/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_106 : ((543937/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos834o2c k) + cos834o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_105
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 106 - ((-499983/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_107 : ((18115259/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos834o2c k) + cos834o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_106
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 107 - ((227/320 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_108 : ((9032039/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos834o2c k) + cos834o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_107
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 108 - ((-51081/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_109 : ((17458293/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos834o2c k) + cos834o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_108
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 109 - ((-121137/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_110 : ((18426231/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos834o2c k) + cos834o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_109
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 110 - ((484019/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_111 : ((17496987/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos834o2c k) + cos834o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_110
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 111 - ((-116143/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_112 : ((18056383/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos834o2c k) + cos834o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_111
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 112 - ((69937/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_113 : ((1802763/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos834o2c k) + cos834o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_112
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 113 - ((-28653/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_114 : ((17544799/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos834o2c k) + cos834o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_113
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 114 - ((-482731/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_115 : ((3677679/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos834o2c k) + cos834o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_114
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 115 - ((52731/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_116 : ((17393081/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos834o2c k) + cos834o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_115
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 116 - ((-497607/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_117 : ((9167871/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos834o2c k) + cos834o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_116
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 117 - ((942761/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_118 : ((17602149/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos834o2c k) + cos834o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_117
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 118 - ((-733493/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_119 : ((18033463/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos834o2c k) + cos834o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_118
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 119 - ((215707/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_120 : ((2241931/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos834o2c k) + cos834o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_119
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 120 - ((-19583/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_121 : ((8858103/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos834o2c k) + cos834o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_120
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 121 - ((-109571/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_122 : ((9102779/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos834o2c k) + cos834o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_121
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 122 - ((122363/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_123 : ((8753241/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos834o2c k) + cos834o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_122
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 123 - ((-21843/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_124 : ((18352631/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos834o2c k) + cos834o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_123
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 124 - ((846249/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_125 : ((17414557/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos834o2c k) + cos834o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_124
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 125 - ((-468987/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_126 : ((3679909/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos834o2c k) + cos834o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_125
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 126 - ((15392/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_127 : ((2174951/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos834o2c k) + cos834o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_126
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 127 - ((-999837/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_128 : ((229917/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos834o2c k) + cos834o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_127
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 128 - ((248463/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_129 : ((17416183/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos834o2c k) + cos834o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_128
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 129 - ((-977077/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_130 : ((18373461/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos834o2c k) + cos834o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_129
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 130 - ((478689/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_131 : ((1089557/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos834o2c k) + cos834o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_130
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 131 - ((-940449/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_132 : ((286919/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos834o2c k) + cos834o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_131
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 132 - ((232501/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_133 : ((17434781/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos834o2c k) + cos834o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_132
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 133 - ((-185587/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_134 : ((18369171/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos834o2c k) + cos834o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_133
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 134 - ((93449/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_135 : ((3484141/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos834o2c k) + cos834o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_134
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 135 - ((-474183/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_136 : ((9193669/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos834o2c k) + cos834o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_135
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 136 - ((966733/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_137 : ((17402003/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos834o2c k) + cos834o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_136
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 137 - ((-197047/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_138 : ((4599977/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos834o2c k) + cos834o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_137
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 138 - ((199601/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_139 : ((17402089/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos834o2c k) + cos834o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_138
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 139 - ((-997719/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_140 : ((18377913/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos834o2c k) + cos834o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_139
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 140 - ((243981/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_141 : ((8727123/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos834o2c k) + cos834o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_140
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 141 - ((-923567/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_142 : ((365723/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos834o2c k) + cos834o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_141
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 142 - ((208001/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_143 : ((17591743/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos834o2c k) + cos834o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_142
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 143 - ((-694307/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_144 : ((18098703/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos834o2c k) + cos834o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_143
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 144 - ((25353/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_145 : ((17826069/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos834o2c k) + cos834o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_144
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 145 - ((-136267/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_146 : ((8913201/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos834o2c k) + cos834o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_145
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 146 - ((433/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_147 : ((4529203/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos834o2c k) + cos834o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_146
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 147 - ((29051/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_148 : ((8772243/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos834o2c k) + cos834o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_147
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 148 - ((-286113/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_149 : ((2294191/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos834o2c k) + cos834o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_148
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 149 - ((404571/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_150 : ((1086951/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos834o2c k) + cos834o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_149
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 150 - ((-240553/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_151 : ((9193303/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos834o2c k) + cos834o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_150
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 151 - ((99549/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_152 : ((17501417/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos834o2c k) + cos834o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_151
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 152 - ((-885089/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_153 : ((1133109/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos834o2c k) + cos834o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_152
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 153 - ((628427/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_154 : ((17877819/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos834o2c k) + cos834o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_153
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 154 - ((-10073/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_155 : ((1769083/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos834o2c k) + cos834o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_154
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 155 - ((-186889/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_156 : ((3658849/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos834o2c k) + cos834o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_155
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 156 - ((120703/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_157 : ((173919/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos834o2c k) + cos834o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_156
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 157 - ((-180449/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_158 : ((9195321/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos834o2c k) + cos834o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_157
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 158 - ((499421/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_159 : ((17542641/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos834o2c k) + cos834o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_158
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 159 - ((-847901/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_160 : ((18008611/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos834o2c k) + cos834o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_159
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 160 - ((46607/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_161 : ((4516777/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos834o2c k) + cos834o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_160
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 161 - ((58597/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_162 : ((1092967/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos834o2c k) + cos834o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_161
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 162 - ((-36221/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_163 : ((2302133/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos834o2c k) + cos834o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_162
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 163 - ((232423/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_164 : ((17439757/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos834o2c k) + cos834o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_163
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 164 - ((-977207/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_165 : ((2265183/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos834o2c k) + cos834o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_164
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 165 - ((681807/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_166 : ((17993439/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos834o2c k) + cos834o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_165
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 166 - ((-5117/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_167 : ((17506233/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos834o2c k) + cos834o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_166
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 167 - ((-243553/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_168 : ((18423269/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos834o2c k) + cos834o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_167
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 168 - ((57321/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_169 : ((8727983/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos834o2c k) + cos834o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_168
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 169 - ((-967203/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_170 : ((9023539/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos834o2c k) + cos834o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_169
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 170 - ((147803/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_171 : ((18110221/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos834o2c k) + cos834o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_170
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 171 - ((63243/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_172 : ((8705777/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos834o2c k) + cos834o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_171
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 172 - ((-698567/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_173 : ((2301097/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos834o2c k) + cos834o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_172
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 173 - ((498661/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_174 : ((3524343/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos834o2c k) + cos834o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_173
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 174 - ((-786961/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_175 : ((2221873/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos834o2c k) + cos834o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_174
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 175 - ((153369/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_176 : ((18349021/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos834o2c k) + cos834o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_175
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 176 - ((574137/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_177 : ((1736513/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos834o2c k) + cos834o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_176
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 177 - ((-983791/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_178 : ((2272941/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos834o2c k) + cos834o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_177
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 178 - ((409249/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_179 : ((18030671/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos834o2c k) + cos834o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_178
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 179 - ((-152757/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_180 : ((17413411/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos834o2c k) + cos834o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_179
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 180 - ((-15429/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_181 : ((18410549/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos834o2c k) + cos834o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_180
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 181 - ((498619/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_182 : ((3538473/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos834o2c k) + cos834o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_181
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 182 - ((-179521/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_183 : ((8818349/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos834o2c k) + cos834o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_182
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 183 - ((-55567/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_184 : ((18435041/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos834o2c k) + cos834o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_183
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 184 - ((798443/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_185 : ((17462501/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos834o2c k) + cos834o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_184
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 185 - ((-24311/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_186 : ((4472503/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos834o2c k) + cos834o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_185
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 186 - ((427611/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_187 : ((9168627/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos834o2c k) + cos834o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_186
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 187 - ((223671/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_188 : ((4338759/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos834o2c k) + cos834o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_187
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 188 - ((-491059/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_189 : ((18093427/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos834o2c k) + cos834o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_188
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 189 - ((738491/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_190 : ((9101679/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos834o2c k) + cos834o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_189
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 190 - ((110031/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_191 : ((8664757/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos834o2c k) + cos834o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_190
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 191 - ((-54609/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_192 : ((9113593/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos834o2c k) + cos834o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_191
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 192 - ((224443/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_193 : ((4522053/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos834o2c k) + cos834o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_192
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 193 - ((-69437/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_194 : ((8669337/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos834o2c k) + cos834o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_193
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 194 - ((-374719/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_195 : ((9150629/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos834o2c k) + cos834o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_194
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 195 - ((240671/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_196 : ((9008487/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos834o2c k) + cos834o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_195
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 196 - ((-35523/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_197 : ((17349049/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos834o2c k) + cos834o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_196
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 197 - ((-26713/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_198 : ((2291353/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos834o2c k) + cos834o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_197
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 198 - ((1571/1600 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_199 : ((17997913/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos834o2c k) + cos834o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_198
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 199 - ((-332811/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_200 : ((1734439/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos834o2c k) + cos834o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_199
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 200 - ((-653423/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_201 : ((18323743/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos834o2c k) + cos834o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_200
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 201 - ((979453/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_202 : ((18032343/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos834o2c k) + cos834o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_201
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 202 - ((-2913/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_203 : ((17324191/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos834o2c k) + cos834o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_202
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 203 - ((-177013/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_204 : ((18276913/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos834o2c k) + cos834o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_203
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 204 - ((476411/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_205 : ((3623511/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos834o2c k) + cos834o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_204
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 205 - ((-79629/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_206 : ((8651309/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos834o2c k) + cos834o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_205
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 206 - ((-814837/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_207 : ((9089117/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos834o2c k) + cos834o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_206
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 207 - ((218929/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_208 : ((18243117/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos834o2c k) + cos834o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_207
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 208 - ((64983/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_209 : ((3461721/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos834o2c k) + cos834o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_208
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 209 - ((-233603/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_210 : ((4503631/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos834o2c k) + cos834o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_209
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 210 - ((706019/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_211 : ((4595577/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos834o2c k) + cos834o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_210
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 211 - ((91971/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_212 : ((8691249/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos834o2c k) + cos834o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_211
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 212 - ((-99971/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_213 : ((8893093/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos834o2c k) + cos834o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_212
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 213 - ((100947/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_214 : ((3696839/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos834o2c k) + cos834o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_213
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 214 - ((698109/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_215 : ((17562837/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos834o2c k) + cos834o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_214
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 215 - ((-460629/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_216 : ((17527499/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos834o2c k) + cos834o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_215
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 216 - ((-17619/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_217 : ((9238311/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos834o2c k) + cos834o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_216
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 217 - ((949223/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_218 : ((3571659/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos834o2c k) + cos834o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_217
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 218 - ((-618227/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_219 : ((270647/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos834o2c k) + cos834o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_218
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 219 - ((-536787/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_220 : ((9146601/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos834o2c k) + cos834o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_219
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 220 - ((485947/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_221 : ((9105233/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos834o2c k) + cos834o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_220
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 221 - ((-20659/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_222 : ((8643593/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos834o2c k) + cos834o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_221
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 222 - ((-46159/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_223 : ((17929689/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos834o2c k) + cos834o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_222
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 223 - ((642603/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_224 : ((18475871/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos834o2c k) + cos834o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_223
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 224 - ((273141/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_225 : ((437947/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos834o2c k) + cos834o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_224
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 225 - ((-957891/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_226 : ((17504961/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos834o2c k) + cos834o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_225
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 226 - ((-12819/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_227 : ((18471901/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos834o2c k) + cos834o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_226
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 227 - ((3022/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_228 : ((17975243/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos834o2c k) + cos834o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_227
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 228 - ((-248279/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_229 : ((17259877/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos834o2c k) + cos834o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_228
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 229 - ((-357633/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_230 : ((452797/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos834o2c k) + cos834o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_229
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 230 - ((852103/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_231 : ((18419209/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos834o2c k) + cos834o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_230
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 231 - ((307429/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_232 : ((1742247/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos834o2c k) + cos834o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_231
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 232 - ((-996639/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_233 : ((8781327/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos834o2c k) + cos834o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_232
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 233 - ((35071/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_234 : ((18499909/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos834o2c k) + cos834o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_233
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 234 - ((187471/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_235 : ((2245729/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos834o2c k) + cos834o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_234
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 235 - ((-533977/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_236 : ((17243109/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos834o2c k) + cos834o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_235
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 236 - ((-722623/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_237 : ((4514919/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos834o2c k) + cos834o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_236
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 237 - ((816667/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_238 : ((1847663/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos834o2c k) + cos834o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_237
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 238 - ((208527/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_239 : ((8754127/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos834o2c k) + cos834o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_238
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 239 - ((-242069/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_240 : ((17426033/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos834o2c k) + cos834o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_239
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 240 - ((-82121/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_241 : ((2302833/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos834o2c k) + cos834o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_240
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 241 - ((996731/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_242 : ((18187977/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos834o2c k) + cos834o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_241
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 242 - ((-234587/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_243 : ((17261297/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos834o2c k) + cos834o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_242
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 243 - ((-46329/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_244 : ((277569/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos834o2c k) + cos834o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_243
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 244 - ((503219/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_245 : ((18553061/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos834o2c k) + cos834o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_244
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 245 - ((157749/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_246 : ((4460683/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos834o2c k) + cos834o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_245
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 246 - ((-710229/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_247 : ((17229449/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos834o2c k) + cos834o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_246
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 247 - ((-613183/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_248 : ((904197/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos834o2c k) + cos834o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_247
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 248 - ((854591/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_249 : ((4627169/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos834o2c k) + cos834o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_248
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 249 - ((106209/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_250 : ((8782611/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos834o2c k) + cos834o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_249
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 250 - ((-471677/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_251 : ((8661607/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 251, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 251, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 250, cos834o2c k) + cos834o2c 251 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 250) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_250
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 251 - ((-60477/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_251).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_252 : ((45777/2500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 252, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 252, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 251, cos834o2c k) + cos834o2c 252 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 251) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_251
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 252 - ((493843/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_252).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_253 : ((18387029/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 253, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 253, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 252, cos834o2c k) + cos834o2c 253 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 252) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_252
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 253 - ((76329/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_253).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_254 : ((17386931/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 254, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 254, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 253, cos834o2c k) + cos834o2c 254 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 253) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_253
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 254 - ((-499999/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_254).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_255 : ((272692/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 255, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 255, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 254, cos834o2c k) + cos834o2c 255 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 254) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_254
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 255 - ((65457/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_255).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_256 : ((18444159/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 256, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 256, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 255, cos834o2c k) + cos834o2c 256 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 255) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_255
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 256 - ((991971/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_256).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_257 : ((9131667/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 257, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 257, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 256, cos834o2c k) + cos834o2c 257 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 256) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_256
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 257 - ((-7229/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_257).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_258 : ((17289647/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 258, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 258, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 257, cos834o2c k) + cos834o2c 258 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 257) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_257
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 258 - ((-973587/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_258).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_259 : ((8779447/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 259, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 259, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 258, cos834o2c k) + cos834o2c 259 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 258) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_258
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 259 - ((269347/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_259).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_260 : ((1156967/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 260, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 260, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 259, cos834o2c k) + cos834o2c 260 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 259) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_259
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 260 - ((476339/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_260).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_261 : ((18178967/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 261, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 261, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 260, cos834o2c k) + cos834o2c 261 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 260) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_260
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 261 - ((-66481/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_261).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_262 : ((17243927/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 262, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 262, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 261, cos834o2c k) + cos834o2c 262 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 261) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_261
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 262 - ((-46747/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_262).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_263 : ((3523037/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 263, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 263, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 262, cos834o2c k) + cos834o2c 263 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 262) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_262
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 263 - ((185679/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_263).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_264 : ((18539143/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 264, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 264, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 263, cos834o2c k) + cos834o2c 264 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 263) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_263
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 264 - ((462029/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_264).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_265 : ((18151479/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 265, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 265, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 264, cos834o2c k) + cos834o2c 265 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 264) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_264
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 265 - ((-96891/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_265).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_266 : ((538421/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 266, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 266, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 265, cos834o2c k) + cos834o2c 266 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 265) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_265
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 266 - ((-921907/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_266).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_267 : ((4402791/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 267, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 267, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 266, cos834o2c k) + cos834o2c 267 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 266) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_266
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 267 - ((11931/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_267).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_268 : ((18539799/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 268, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 268, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 267, cos834o2c k) + cos834o2c 268 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 267) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_267
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 268 - ((185747/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_268).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_269 : ((284148/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 269, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 269, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 268, cos834o2c k) + cos834o2c 269 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 268) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_268
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 269 - ((-354227/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_269).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_270 : ((3448431/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 270, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 270, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 269, cos834o2c k) + cos834o2c 270 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 269) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_269
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 270 - ((-943217/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_270).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_271 : ((17546563/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 271, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 271, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 270, cos834o2c k) + cos834o2c 271 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 270) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_270
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 271 - ((76127/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_271).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_272 : ((9254509/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 272, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 272, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 271, cos834o2c k) + cos834o2c 272 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 271) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_271
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 272 - ((192511/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_272).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_273 : ((9138529/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 273, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 273, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 272, cos834o2c k) + cos834o2c 273 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 272) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_272
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 273 - ((-11593/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_273).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_274 : ((17294561/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 274, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 274, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 273, cos834o2c k) + cos834o2c 274 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 273) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_273
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 274 - ((-982397/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_274).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_275 : ((3486049/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 275, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 275, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 274, cos834o2c k) + cos834o2c 275 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 274) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_274
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 275 - ((16973/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_275).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_276 : ((18427023/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 276, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 276, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 275, cos834o2c k) + cos834o2c 276 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 275) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_275
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 276 - ((498439/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_276).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_277 : ((18410521/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 277, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 277, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 276, cos834o2c k) + cos834o2c 277 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 276) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_276
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 277 - ((-8201/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_277).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_278 : ((17411757/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 278, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 278, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 277, cos834o2c k) + cos834o2c 278 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 277) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_277
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 278 - ((-124833/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_278).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_279 : ((691471/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 279, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 279, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 278, cos834o2c k) + cos834o2c 279 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 278) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_278
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 279 - ((-62441/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_279).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_280 : ((3653187/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 280, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 280, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 279, cos834o2c k) + cos834o2c 280 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 279) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_279
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 280 - ((48963/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_280).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_281 : ((9275037/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 281, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 281, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 280, cos834o2c k) + cos834o2c 281 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 280) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_280
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 281 - ((284239/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_281).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_282 : ((17620443/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 282, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 282, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 281, cos834o2c k) + cos834o2c 282 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 281) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_281
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 282 - ((-929531/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_282).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_283 : ((4291339/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 283, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 283, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 282, cos834o2c k) + cos834o2c 283 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 282) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_282
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 283 - ((-454987/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_283).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_284 : ((18005953/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 284, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 284, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 283, cos834o2c k) + cos834o2c 284 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 283) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_283
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 284 - ((840697/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_284).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_285 : ((18632553/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 285, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 285, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 284, cos834o2c k) + cos834o2c 285 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 284) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_284
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 285 - ((6267/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_285).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_286 : ((17926821/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 286, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 286, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 285, cos834o2c k) + cos834o2c 286 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 285) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_285
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 286 - ((-22051/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_286).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_287 : ((17141669/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 287, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 287, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 286, cos834o2c k) + cos834o2c 287 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 286) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_286
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 287 - ((-196263/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_287).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_288 : ((17662233/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 288, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 288, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 287, cos834o2c k) + cos834o2c 288 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 287) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_287
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 288 - ((65083/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_288).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_289 : ((18574307/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 289, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 289, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 288, cos834o2c k) + cos834o2c 289 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 288) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_288
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 289 - ((456087/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_289).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_290 : ((18286449/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 290, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 290, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 289, cos834o2c k) + cos834o2c 290 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 289) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_289
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 290 - ((-143879/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_290).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_291 : ((8649287/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 291, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 291, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 290, cos834o2c k) + cos834o2c 291 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 290) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_290
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 291 - ((-39511/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_291).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_292 : ((4328691/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 292, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 292, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 291, cos834o2c k) + cos834o2c 292 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 291) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_291
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 292 - ((1629/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_292).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_293 : ((4576593/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 293, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 293, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 292, cos834o2c k) + cos834o2c 293 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 292) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_292
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 293 - ((247927/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_293).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_294 : ((4645393/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 294, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 294, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 293, cos834o2c k) + cos834o2c 294 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 293) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_293
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 294 - ((2753/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_294).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_295 : ((17674069/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 295, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 295, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 294, cos834o2c k) + cos834o2c 295 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 294) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_294
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 295 - ((-907403/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_295).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_296 : ((855741/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 296, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 296, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 295, cos834o2c k) + cos834o2c 296 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 295) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_295
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 296 - ((-559149/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_296).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_297 : ((17841111/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 297, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 297, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 296, cos834o2c k) + cos834o2c 297 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 296) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_296
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 297 - ((726391/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_297).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_298 : ((9320379/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 298, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 298, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 297, cos834o2c k) + cos834o2c 298 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 297) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_297
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 298 - ((799747/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_298).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_299 : ((9093833/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 299, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 299, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 298, cos834o2c k) + cos834o2c 299 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 298) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_298
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 299 - ((-7078/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_299).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_300 : ((17229793/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 300, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 300, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 299, cos834o2c k) + cos834o2c 300 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 299) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_299
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 300 - ((-957773/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_300).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_301 : ((17338019/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 301, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 301, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 300, cos834o2c k) + cos834o2c 301 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 300) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_300
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 301 - ((54163/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_301).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_302 : ((4583697/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 302, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 302, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 301, cos834o2c k) + cos834o2c 302 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 301) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_301
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 302 - ((996869/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_302).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_303 : ((18602797/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 303, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 303, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 302, cos834o2c k) + cos834o2c 303 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 302) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_302
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 303 - ((268109/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_303).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_304 : ((17710339/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 304, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 304, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 303, cos834o2c k) + cos834o2c 304 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 303) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_303
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 304 - ((-446179/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_304).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_305 : ((17089551/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 305, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 305, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 304, cos834o2c k) + cos834o2c 305 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 304) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_304
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 305 - ((-38793/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_305).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_306 : ((8865067/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 306, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 306, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 305, cos834o2c k) + cos834o2c 306 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 305) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_305
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 306 - ((640683/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_306).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_307 : ((3722933/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 307, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 307, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 306, cos834o2c k) + cos834o2c 307 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 306) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_306
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 307 - ((884631/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_307).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_308 : ((3669493/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 308, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 308, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 307, cos834o2c k) + cos834o2c 308 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 307) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_307
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 308 - ((-2671/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_308).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_309 : ((433717/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 309, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 309, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 308, cos834o2c k) + cos834o2c 309 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 308) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_308
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 309 - ((-199737/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_309).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_310 : ((4294313/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 310, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 310, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 309, cos834o2c k) + cos834o2c 310 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 309) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_309
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 310 - ((-2677/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_310).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_311 : ((4524559/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 311, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 311, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 310, cos834o2c k) + cos834o2c 311 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 310) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_310
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 311 - ((230271/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_311).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_312 : ((4672241/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 312, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 312, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 311, cos834o2c k) + cos834o2c 312 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 311) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_311
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 312 - ((147707/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_312).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_313 : ((18042877/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 313, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 313, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 312, cos834o2c k) + cos834o2c 313 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 312) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_312
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 313 - ((-645987/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_313).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_314 : ((3429493/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 314, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 314, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 313, cos834o2c k) + cos834o2c 314 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 313) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_313
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 314 - ((-55957/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_314).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_315 : ((8681237/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 315, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 315, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 314, cos834o2c k) + cos834o2c 315 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 314) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_314
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 315 - ((215109/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_315).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_316 : ((18361853/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 316, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 316, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 315, cos834o2c k) + cos834o2c 316 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 315) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_315
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 316 - ((999479/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_316).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_317 : ((9321721/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 317, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 317, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 316, cos834o2c k) + cos834o2c 317 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 316) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_316
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 317 - ((281689/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_317).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_318 : ((17787163/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 318, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 318, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 317, cos834o2c k) + cos834o2c 318 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 317) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_317
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 318 - ((-856179/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_318).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_319 : ((8533301/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 319, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 319, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 318, cos834o2c k) + cos834o2c 319 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 318) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_318
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 319 - ((-720461/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_319).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_320 : ((17546507/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 320, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 320, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 319, cos834o2c k) + cos834o2c 320 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 319) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_319
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 320 - ((96001/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_320).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_321 : ((2314981/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 321, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 321, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 320, cos834o2c k) + cos834o2c 321 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 320) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_320
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 321 - ((973441/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_321).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_322 : ((4640627/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 322, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 322, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 321, cos834o2c k) + cos834o2c 322 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 321) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_321
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 322 - ((1069/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_322).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_323 : ((17613341/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 323, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 323, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 322, cos834o2c k) + cos834o2c 323 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 322) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_322
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 323 - ((-949067/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_323).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_324 : ((17046701/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 324, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 324, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 323, cos834o2c k) + cos834o2c 324 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 323) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_323
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 324 - ((-28327/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_324).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_325 : ((17677511/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 325, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 325, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 324, cos834o2c k) + cos834o2c 325 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 324) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_324
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 325 - ((63091/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_325).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_326 : ((18601161/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 326, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 326, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 325, cos834o2c k) + cos834o2c 326 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 325) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_325
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 326 - ((739/800 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_326).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_327 : ((18501797/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 327, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 327, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 326, cos834o2c k) + cos834o2c 327 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 326) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_326
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 327 - ((-1551/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_327).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_328 : ((17521247/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 328, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 328, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 327, cos834o2c k) + cos834o2c 328 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 327) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_327
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 328 - ((-19609/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_328).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_329 : ((17042191/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 329, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 329, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 328, cos834o2c k) + cos834o2c 329 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 328) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_328
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 329 - ((-119739/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_329).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_330 : ((4433853/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 330, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 330, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 329, cos834o2c k) + cos834o2c 330 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 329) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_329
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 330 - ((693321/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_330).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_331 : ((1164543/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 331, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 331, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 330, cos834o2c k) + cos834o2c 331 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 330) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_330
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 331 - ((28043/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_331).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_332 : ((2311119/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 332, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 332, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 331, cos834o2c k) + cos834o2c 332 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 331) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_331
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 332 - ((-35909/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_332).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_333 : ((17503699/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 333, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 333, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 332, cos834o2c k) + cos834o2c 333 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 332) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_332
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 333 - ((-985153/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_333).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_334 : ((17030367/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 334, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 334, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 333, cos834o2c k) + cos834o2c 334 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 333) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_333
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 334 - ((-29577/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_334).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_335 : ((8857307/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 335, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 335, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 334, cos834o2c k) + cos834o2c 335 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 334) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_334
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 335 - ((684347/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_335).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_336 : ((9312607/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 336, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 336, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 335, cos834o2c k) + cos834o2c 336 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 335) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_335
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 336 - ((9107/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_336).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_337 : ((4632747/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 337, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 337, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 336, cos834o2c k) + cos834o2c 337 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 336) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_336
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 337 - ((-47063/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_337).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_338 : ((17559789/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 338, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 338, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 337, cos834o2c k) + cos834o2c 338 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 337) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_337
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 338 - ((-971099/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_338).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_339 : ((8505893/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 339, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 339, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 338, cos834o2c k) + cos834o2c 339 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 338) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_338
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 339 - ((-547903/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_339).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_340 : ((17615613/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 340, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 340, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 339, cos834o2c k) + cos834o2c 340 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 339) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_339
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 340 - ((603927/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_340).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_341 : ((18570177/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 341, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 341, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 340, cos834o2c k) + cos834o2c 341 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 340) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_340
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 341 - ((119333/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_341).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_342 : ((18617487/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 342, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 342, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 341, cos834o2c k) + cos834o2c 342 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 341) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_341
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 342 - ((4741/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_342).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_343 : ((8848301/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 343, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 343, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 342, cos834o2c k) + cos834o2c 343 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 342) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_342
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 343 - ((-184157/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_343).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_344 : ((17009369/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 344, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 344, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 343, cos834o2c k) + cos834o2c 344 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 343) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_343
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 344 - ((-687133/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_344).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_345 : ((17446873/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 345, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 345, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 344, cos834o2c k) + cos834o2c 345 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 344) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_344
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 345 - ((109401/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_345).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_346 : ((1844281/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 346, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 346, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 345, cos834o2c k) + cos834o2c 346 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 345) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_345
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 346 - ((996037/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_346).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_347 : ((18717407/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 347, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 347, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 346, cos834o2c k) + cos834o2c 347 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 346) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_346
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 347 - ((274697/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_347).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_348 : ((17920661/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 348, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 348, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 347, cos834o2c k) + cos834o2c 348 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 347) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_347
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 348 - ((-398323/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_348).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_349 : ((8533369/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 349, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 349, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 348, cos834o2c k) + cos834o2c 349 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 348) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_348
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 349 - ((-853823/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_349).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_350 : ((8617829/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 350, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 350, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 349, cos834o2c k) + cos834o2c 350 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 349) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_349
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 350 - ((8451/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_350).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_351 : ((9106667/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 351, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 351, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 350, cos834o2c k) + cos834o2c 351 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 350) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_350
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 351 - ((61111/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_351).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_352 : ((3754863/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 352, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 352, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 351, cos834o2c k) + cos834o2c 352 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 351) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_351
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 352 - ((561081/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_352).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_353 : ((18220103/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 353, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 353, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 352, cos834o2c k) + cos834o2c 353 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 352) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_352
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 353 - ((-8658/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_353).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_354 : ((17239179/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 354, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 354, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 353, cos834o2c k) + cos834o2c 354 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 353) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_353
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 354 - ((-122603/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_354).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_355 : ((8521003/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 355, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 355, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 354, cos834o2c k) + cos834o2c 355 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 354) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_354
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 355 - ((-197073/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_355).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_356 : ((17869411/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 356, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 356, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 355, cos834o2c k) + cos834o2c 356 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 355) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_355
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 356 - ((165501/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_356).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_357 : ((18709297/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 357, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 357, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 356, cos834o2c k) + cos834o2c 357 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 356) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_356
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 357 - ((419993/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_357).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_358 : ((18540829/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 358, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 358, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 357, cos834o2c k) + cos834o2c 358 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 357) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_357
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 358 - ((-10523/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_358).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_359 : ((8784511/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 359, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 359, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 358, cos834o2c k) + cos834o2c 359 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 358) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_358
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 359 - ((-971707/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_359).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_360 : ((16964317/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 360, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 360, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 359, cos834o2c k) + cos834o2c 360 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 359) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_359
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 360 - ((-120921/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_360).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_361 : ((4362541/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 361, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 361, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 360, cos834o2c k) + cos834o2c 361 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 360) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_360
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 361 - ((485947/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_361).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_362 : ((18445999/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 362, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 362, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 361, cos834o2c k) + cos834o2c 362 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 361) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_361
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 362 - ((199187/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_362).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_363 : ((18770191/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 363, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 363, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 362, cos834o2c k) + cos834o2c 363 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 362) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_362
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 363 - ((81073/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_363).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_364 : ((18041061/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 364, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 364, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 363, cos834o2c k) + cos834o2c 364 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 363) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_363
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 364 - ((-72903/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_364).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_365 : ((4279027/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 365, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 365, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 364, cos834o2c k) + cos834o2c 365 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 364) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_364
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 365 - ((-924853/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_365).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_366 : ((17076281/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 366, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 366, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 365, cos834o2c k) + cos834o2c 366 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 365) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_365
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 366 - ((-39727/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_366).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_367 : ((17966501/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 367, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 367, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 366, cos834o2c k) + cos834o2c 367 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 366) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_366
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 367 - ((11129/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_367).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_368 : ((4688799/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 368, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 368, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 367, cos834o2c k) + cos834o2c 368 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 367) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_367
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 368 - ((157759/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_368).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_369 : ((18534167/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 369, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 369, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 368, cos834o2c k) + cos834o2c 369 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 368) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_368
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 369 - ((-220929/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_369).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_370 : ((4389513/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 370, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 370, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 369, cos834o2c k) + cos834o2c 370 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 369) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_369
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 370 - ((-195203/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_370).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_371 : ((1694107/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 371, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 371, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 370, cos834o2c k) + cos834o2c 371 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 370) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_370
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 371 - ((-308441/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_371).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_372 : ((17382861/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 372, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 372, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 371, cos834o2c k) + cos834o2c 372 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 371) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_371
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 372 - ((441891/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_372).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_373 : ((18382741/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 373, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 373, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 372, cos834o2c k) + cos834o2c 373 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 372) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_372
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 373 - ((49999/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_373).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_374 : ((9407891/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 374, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 374, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 373, cos834o2c k) + cos834o2c 374 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 373) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_373
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 374 - ((433141/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_374).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_375 : ((18198197/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 375, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 375, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 374, cos834o2c k) + cos834o2c 375 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 374) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_374
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 375 - ((-123497/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_375).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_376 : ((1076193/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 376, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 376, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 375, cos834o2c k) + cos834o2c 376 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 375) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_375
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 376 - ((-979009/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_376).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_377 : ((16963853/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 377, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 377, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 376, cos834o2c k) + cos834o2c 377 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 376) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_376
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 377 - ((-51027/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_377).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_378 : ((1107051/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 378, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 378, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 377, cos834o2c k) + cos834o2c 378 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 377) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_377
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 378 - ((749063/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_378).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_379 : ((9321133/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 379, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 379, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 378, cos834o2c k) + cos834o2c 379 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 378) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_378
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 379 - ((18591/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_379).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_380 : ((9368211/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 380, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 380, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 379, cos834o2c k) + cos834o2c 380 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 379) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_379
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 380 - ((5891/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_380).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_381 : ((1789403/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 381, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 381, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 380, cos834o2c k) + cos834o2c 381 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 380) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_380
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 381 - ((-210573/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_381).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_382 : ((17028009/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 382, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 382, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 381, cos834o2c k) + cos834o2c 382 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 381) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_381
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 382 - ((-865921/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_382).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_383 : ((1707107/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 383, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 383, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 382, cos834o2c k) + cos834o2c 383 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 382) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_382
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 383 - ((43161/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_383).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_384 : ((8987807/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 384, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 384, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 383, cos834o2c k) + cos834o2c 384 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 383) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_383
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 384 - ((226161/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_384).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_385 : ((9387523/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 385, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 385, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 384, cos834o2c k) + cos834o2c 385 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 384) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_384
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 385 - ((199883/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_385).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_386 : ((9310193/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 386, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 386, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 385, cos834o2c k) + cos834o2c 386 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 385) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_385
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 386 - ((-483/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_386).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_387 : ((17676439/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 387, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 387, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 386, cos834o2c k) + cos834o2c 387 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 386) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_386
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 387 - ((-943847/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_387).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_388 : ((8468747/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 388, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 388, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 387, cos834o2c k) + cos834o2c 388 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 387) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_387
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 388 - ((-147769/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_388).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_389 : ((8588521/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 389, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 389, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 388, cos834o2c k) + cos834o2c 389 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 388) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_388
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 389 - ((7489/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_389).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_390 : ((18143797/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 390, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 390, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 389, cos834o2c k) + cos834o2c 390 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 389) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_389
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 390 - ((193371/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_390).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_391 : ((18833437/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 391, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 391, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 390, cos834o2c k) + cos834o2c 391 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 390) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_390
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 391 - ((34487/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_391).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_392 : ((3706797/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 392, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 392, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 391, cos834o2c k) + cos834o2c 392 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 391) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_391
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 392 - ((-37419/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_392).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_393 : ((4388673/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 393, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 393, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 392, cos834o2c k) + cos834o2c 393 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 392) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_392
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 393 - ((-979193/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_393).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_394 : ((8449327/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 394, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 394, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 393, cos834o2c k) + cos834o2c 394 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 393) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_393
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 394 - ((-327969/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_394).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_395 : ((17233537/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 395, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 395, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 394, cos834o2c k) + cos834o2c 395 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 394) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_394
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 395 - ((334983/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_395).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_396 : ((9109097/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 396, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 396, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 395, cos834o2c k) + cos834o2c 396 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 395) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_395
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 396 - ((984757/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_396).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_397 : ((1885767/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 397, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 397, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 396, cos834o2c k) + cos834o2c 397 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 396) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_396
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 397 - ((79947/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_397).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_398 : ((18509847/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 398, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 398, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 397, cos834o2c k) + cos834o2c 398 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 397) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_397
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 398 - ((-347723/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_398).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_399 : ((17524033/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 399, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 399, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 398, cos834o2c k) + cos834o2c 399 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 398) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_398
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 399 - ((-492857/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_399).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_400 : ((16882597/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 400, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 400, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 399, cos834o2c k) + cos834o2c 400 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 399) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_399
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 400 - ((-80167/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_400).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_401 : ((2152583/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 401, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 401, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 400, cos834o2c k) + cos834o2c 401 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 400) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_400
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 401 - ((338167/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_401).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_402 : ((4550771/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 402, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 402, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 401, cos834o2c k) + cos834o2c 402 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 401) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_401
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 402 - ((24563/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_402).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_403 : ((4715969/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 403, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 403, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 402, cos834o2c k) + cos834o2c 403 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 402) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_402
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 403 - ((165223/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_403).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_404 : ((18557343/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 404, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 404, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 403, cos834o2c k) + cos834o2c 404 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 403) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_403
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 404 - ((-306433/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_404).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_405 : ((17583223/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 405, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 405, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 404, cos834o2c k) + cos834o2c 405 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 404) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_404
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 405 - ((-48701/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_405).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_406 : ((8443179/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 406, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 406, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 405, cos834o2c k) + cos834o2c 406 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 405) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_405
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 406 - ((-139353/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_406).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_407 : ((1071153/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 407, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 407, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 406, cos834o2c k) + cos834o2c 407 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 406) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_406
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 407 - ((25219/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_407).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_408 : ((2261983/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 408, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 408, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 407, cos834o2c k) + cos834o2c 408 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 407) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_407
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 408 - ((239379/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_408).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_409 : ((4710521/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 409, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 409, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 408, cos834o2c k) + cos834o2c 409 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 408) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_408
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 409 - ((9329/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_409).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_410 : ((1866709/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 410, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 410, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 409, cos834o2c k) + cos834o2c 410 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 409) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_409
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 410 - ((-87447/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_410).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_411 : ((17738009/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 411, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 411, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 410, cos834o2c k) + cos834o2c 411 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 410) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_410
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 411 - ((-928981/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_411).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_412 : ((16932367/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 412, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 412, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 411, cos834o2c k) + cos834o2c 412 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 411) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_411
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 412 - ((-402771/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_412).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_413 : ((17006501/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 413, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 413, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 412, cos834o2c k) + cos834o2c 413 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 412) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_412
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 413 - ((37117/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_413).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_414 : ((17889663/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 414, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 414, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 413, cos834o2c k) + cos834o2c 414 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 413) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_413
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 414 - ((441631/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_414).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_415 : ((9379179/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 415, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 415, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 414, cos834o2c k) + cos834o2c 415 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 414) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_414
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 415 - ((173759/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_415).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_416 : ((1175463/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 416, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 416, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 415, cos834o2c k) + cos834o2c 416 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 415) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_415
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 416 - ((983/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_416).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_417 : ((281136/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 417, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 417, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 416, cos834o2c k) + cos834o2c 417 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 416) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_416
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 417 - ((-203651/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_417).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_418 : ((8531979/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 418, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 418, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 417, cos834o2c k) + cos834o2c 418 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 417) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_417
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 418 - ((-464323/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_418).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_419 : ((16870753/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 419, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 419, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 418, cos834o2c k) + cos834o2c 419 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 418) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_418
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 419 - ((-38621/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_419).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_420 : ((17587813/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 420, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 420, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 419, cos834o2c k) + cos834o2c 420 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 419) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_419
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 420 - ((17929/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_420).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_421 : ((18563481/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 421, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 421, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 420, cos834o2c k) + cos834o2c 421 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 420) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_420
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 421 - ((121971/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_421).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_422 : ((18916473/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 422, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 422, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 421, cos834o2c k) + cos834o2c 422 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 421) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_421
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 422 - ((88273/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_422).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_423 : ((18330399/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 423, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 423, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 422, cos834o2c k) + cos834o2c 423 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 422) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_422
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 423 - ((-292987/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_423).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_424 : ((17331097/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 424, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 424, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 423, cos834o2c k) + cos834o2c 424 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 423) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_423
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 424 - ((-499601/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_424).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_425 : ((16809571/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 425, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 425, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 424, cos834o2c k) + cos834o2c 425 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 424) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_424
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 425 - ((-260713/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_425).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_426 : ((4306929/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 426, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 426, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 425, cos834o2c k) + cos834o2c 426 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 425) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_425
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 426 - ((83649/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_426).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_427 : ((4553649/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 427, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 427, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 426, cos834o2c k) + cos834o2c 427 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 426) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_426
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 427 - ((49349/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_427).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_428 : ((9450597/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 428, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 428, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 427, cos834o2c k) + cos834o2c 428 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 427) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_427
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 428 - ((343349/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_428).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_429 : ((18686517/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 429, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 429, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 428, cos834o2c k) + cos834o2c 429 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 428) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_428
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 429 - ((-214577/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_429).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_430 : ((4439777/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 430, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 430, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 429, cos834o2c k) + cos834o2c 430 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 429) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_429
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 430 - ((-927309/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_430).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_431 : ((105783/6250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 431, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 431, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 430, cos834o2c k) + cos834o2c 431 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 430) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_430
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 431 - ((-13027/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_431).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_432 : ((16905753/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 432, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 432, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 431, cos834o2c k) + cos834o2c 432 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 431) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_431
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 432 - ((-19427/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_432).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_433 : ((17716009/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 433, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 433, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 432, cos834o2c k) + cos834o2c 433 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 432) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_432
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 433 - ((202589/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_433).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_434 : ((2332503/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 434, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 434, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 433, cos834o2c k) + cos834o2c 434 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 433) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_433
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 434 - ((188823/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_434).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_435 : ((18931637/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 435, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 435, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 434, cos834o2c k) + cos834o2c 435 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 434) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_434
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 435 - ((271713/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_435).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_436 : ((4575231/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 436, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 436, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 435, cos834o2c k) + cos834o2c 436 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 435) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_435
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 436 - ((-630613/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_436).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_437 : ((8651529/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 437, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 437, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 436, cos834o2c k) + cos834o2c 437 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 436) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_436
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 437 - ((-498883/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_437).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_438 : ((8389809/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 438, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 438, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 437, cos834o2c k) + cos834o2c 438 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 437) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_437
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 438 - ((-26167/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_438).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_439 : ((17169123/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 439, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 439, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 438, cos834o2c k) + cos834o2c 439 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 438) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_438
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 439 - ((77921/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_439).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_440 : ((1134033/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 440, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 440, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 439, cos834o2c k) + cos834o2c 440 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 439) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_439
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 440 - ((195101/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_440).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_441 : ((3778607/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 441, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 441, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 440, cos834o2c k) + cos834o2c 441 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 440) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_440
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 441 - ((748607/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_441).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_442 : ((4698637/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 442, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 442, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 441, cos834o2c k) + cos834o2c 442 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 441) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_441
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 442 - ((-98387/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_442).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_443 : ((2241447/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 443, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 443, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 442, cos834o2c k) + cos834o2c 443 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 442) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_442
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 443 - ((-107859/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_443).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_444 : ((17014507/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 444, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 444, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 443, cos834o2c k) + cos834o2c 444 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 443) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_443
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 444 - ((-916969/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_444).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_445 : ((8396971/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 445, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 445, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 444, cos834o2c k) + cos834o2c 445 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 444) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_444
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 445 - ((-44093/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_445).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_446 : ((8724257/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 446, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 446, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 445, cos834o2c k) + cos834o2c 446 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 445) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_445
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 446 - ((40917/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_446).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_447 : ((18445461/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 447, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 447, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 446, cos834o2c k) + cos834o2c 447 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 446) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_446
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 447 - ((997047/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_447).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_448 : ((4744573/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 448, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 448, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 447, cos834o2c k) + cos834o2c 448 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 447) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_447
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 448 - ((532931/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_448).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_449 : ((9309369/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 449, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 449, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 448, cos834o2c k) + cos834o2c 449 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 448) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_448
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 449 - ((-179727/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_449).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_450 : ((706253/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 450, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 450, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 449, cos834o2c k) + cos834o2c 450 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 449) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_449
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 450 - ((-962313/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_450).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_451 : ((263442/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 451, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 451, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 450, cos834o2c k) + cos834o2c 451 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 450) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_450
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 451 - ((-795937/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_451).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_452 : ((8431603/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 452, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 452, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 451, cos834o2c k) + cos834o2c 452 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 451) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_451
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 452 - ((1509/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_452).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_453 : ((17661479/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 453, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 453, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 452, cos834o2c k) + cos834o2c 453 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 452) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_452
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 453 - ((798373/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_453).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_454 : ((18624271/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 454, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 454, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 453, cos834o2c k) + cos834o2c 454 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 453) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_453
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 454 - ((240723/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_454).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_455 : ((9497543/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 455, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 455, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 454, cos834o2c k) + cos834o2c 455 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 454) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_454
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 455 - ((74183/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_455).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_456 : ((9242363/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 456, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 456, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 455, cos834o2c k) + cos834o2c 456 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 455) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_455
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 456 - ((-25513/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_456).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_457 : ((17492043/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 457, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 457, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 456, cos834o2c k) + cos834o2c 457 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 456) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_456
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 457 - ((-992583/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_457).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_458 : ((16787819/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 458, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 458, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 457, cos834o2c k) + cos834o2c 458 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 457) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_457
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 458 - ((-176031/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_458).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_459 : ((8457849/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 459, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 459, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 458, cos834o2c k) + cos834o2c 459 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 458) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_458
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 459 - ((127979/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_459).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_460 : ((277748/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 460, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 460, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 459, cos834o2c k) + cos834o2c 460 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 459) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_459
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 460 - ((430137/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_460).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_461 : ((9353947/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 461, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 461, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 460, cos834o2c k) + cos834o2c 461 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 460) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_460
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 461 - ((466061/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_461).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_462 : ((3800027/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 462, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 462, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 461, cos834o2c k) + cos834o2c 462 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 461) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_461
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 462 - ((292341/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_462).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_463 : ((18431303/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 463, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 463, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 462, cos834o2c k) + cos834o2c 463 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 462) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_462
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 463 - ((-142183/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_463).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_464 : ((1743339/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 464, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 464, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 463, cos834o2c k) + cos834o2c 464 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 463) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_463
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 464 - ((-997813/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_464).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_465 : ((16759599/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 465, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 465, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 464, cos834o2c k) + cos834o2c 465 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 464) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_464
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 465 - ((-673691/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_465).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_466 : ((16915467/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 466, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 466, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 465, cos834o2c k) + cos834o2c 466 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 465) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_465
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 466 - ((2437/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_466).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_467 : ((17783033/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 467, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 467, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 466, cos834o2c k) + cos834o2c 467 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 466) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_466
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 467 - ((433833/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_467).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_468 : ((18714661/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 468, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 468, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 467, cos834o2c k) + cos834o2c 468 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 467) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_467
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 468 - ((58233/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_468).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_469 : ((19018719/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 469, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 469, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 468, cos834o2c k) + cos834o2c 469 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 468) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_468
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 469 - ((152079/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_469).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_470 : ((18471337/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 470, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 470, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 469, cos834o2c k) + cos834o2c 470 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 469) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_469
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 470 - ((-273641/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_470).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_471 : ((3495357/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 471, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 471, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 470, cos834o2c k) + cos834o2c 471 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 470) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_470
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 471 - ((-248613/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_471).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_472 : ((8382543/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 472, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 472, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 471, cos834o2c k) + cos834o2c 472 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 471) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_471
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 472 - ((-711599/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_472).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_473 : ((4213907/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 473, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 473, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 472, cos834o2c k) + cos834o2c 473 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 472) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_472
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 473 - ((45321/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_473).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_474 : ((4420311/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 474, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 474, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 473, cos834o2c k) + cos834o2c 474 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 473) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_473
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 474 - ((206429/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_474).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_475 : ((18642337/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 475, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 475, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 474, cos834o2c k) + cos834o2c 475 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 474) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_474
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 475 - ((961193/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_475).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_476 : ((9522413/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 476, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 476, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 475, cos834o2c k) + cos834o2c 476 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 475) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_475
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 476 - ((402589/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_476).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_477 : ((3720017/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 477, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 477, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 476, cos834o2c k) + cos834o2c 477 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 476) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_476
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 477 - ((-444641/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_477).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_478 : ((4406967/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 478, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 478, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 477, cos834o2c k) + cos834o2c 478 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 477) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_477
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 478 - ((-972117/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_478).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_479 : ((8411273/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 479, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 479, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 478, cos834o2c k) + cos834o2c 479 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 478) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_478
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 479 - ((-402611/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_479).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_480 : ((837807/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 480, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 480, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 479, cos834o2c k) + cos834o2c 480 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 479) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_479
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 480 - ((-33153/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_480).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_481 : ((3494883/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 481, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 481, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 480, cos834o2c k) + cos834o2c 481 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 480) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_480
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 481 - ((5747/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_481).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_482 : ((461741/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 482, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 482, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 481, cos834o2c k) + cos834o2c 482 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 481) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_481
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 482 - ((39813/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_482).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_483 : ((19042267/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 483, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 483, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 482, cos834o2c k) + cos834o2c 483 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 482) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_482
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 483 - ((572727/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_483).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_484 : ((9396097/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 484, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 484, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 483, cos834o2c k) + cos834o2c 484 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 483) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_483
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 484 - ((-249973/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_484).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_485 : ((8947467/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 485, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 485, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 484, cos834o2c k) + cos834o2c 485 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 484) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_484
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 485 - ((-22429/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_485).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_486 : ((8487167/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 486, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 486, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 485, cos834o2c k) + cos834o2c 486 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 485) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_485
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 486 - ((-1841/2000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_486).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_487 : ((16667067/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 487, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 487, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 486, cos834o2c k) + cos834o2c 487 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 486) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_486
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 487 - ((-307167/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_487).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_488 : ((8591913/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 488, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 488, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 487, cos834o2c k) + cos834o2c 488 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 487) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_487
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 488 - ((516859/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_488).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_489 : ((18168623/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 489, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 489, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 488, cos834o2c k) + cos834o2c 489 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 488) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_488
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 489 - ((984897/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_489).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_490 : ((9473717/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 490, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 490, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 489, cos834o2c k) + cos834o2c 490 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 489) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_489
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 490 - ((778911/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_490).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_491 : ((4747517/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 491, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 491, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 490, cos834o2c k) + cos834o2c 491 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 490) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_490
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 491 - ((21367/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_491).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_492 : ((3653733/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 492, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 492, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 491, cos834o2c k) + cos834o2c 492 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 491) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_491
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 492 - ((-721303/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_492).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_493 : ((17271889/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 493, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 493, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 492, cos834o2c k) + cos834o2c 493 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 492) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_492
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 493 - ((-249169/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_493).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_494 : ((16671209/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 494, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 494, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 493, cos834o2c k) + cos834o2c 494 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 493) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_493
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 494 - ((-30029/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_494).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_495 : ((16868829/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 495, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 495, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 494, cos834o2c k) + cos834o2c 495 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 494) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_494
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 495 - ((4943/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_495).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_496 : ((17731447/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 496, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 496, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 495, cos834o2c k) + cos834o2c 496 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 495) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_495
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 496 - ((431359/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_496).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_497 : ((18683771/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 497, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 497, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 496, cos834o2c k) + cos834o2c 497 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 496) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_496
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 497 - ((119053/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_497).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_498 : ((9547049/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 498, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 498, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 497, cos834o2c k) + cos834o2c 498 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 497) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_497
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 498 - ((410427/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_498).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_499 : ((4673027/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 499, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 499, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 498, cos834o2c k) + cos834o2c 499 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 498) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_498
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 499 - ((-40189/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_499).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum834o2_500 : ((709741/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 500, cos834o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 500, cos834o2c k)
      = (∑ k ∈ Finset.Icc 11 499, cos834o2c k) + cos834o2c 500 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 499) (by norm_num) cos834o2c
    simpa using h
  have hprev := psum834o2_499
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos834o2c 500 - ((-948483/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos834o2_br_500).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 16384 in
theorem psum834o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 500 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos834o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum834o2_11
  · exact le_trans (by norm_num) psum834o2_12
  · exact le_trans (by norm_num) psum834o2_13
  · exact le_trans (by norm_num) psum834o2_14
  · exact le_trans (by norm_num) psum834o2_15
  · exact le_trans (by norm_num) psum834o2_16
  · exact le_trans (by norm_num) psum834o2_17
  · exact le_trans (by norm_num) psum834o2_18
  · exact le_trans (by norm_num) psum834o2_19
  · exact le_trans (by norm_num) psum834o2_20
  · exact le_trans (by norm_num) psum834o2_21
  · exact le_trans (by norm_num) psum834o2_22
  · exact le_trans (by norm_num) psum834o2_23
  · exact le_trans (by norm_num) psum834o2_24
  · exact le_trans (by norm_num) psum834o2_25
  · exact le_trans (by norm_num) psum834o2_26
  · exact le_trans (by norm_num) psum834o2_27
  · exact le_trans (by norm_num) psum834o2_28
  · exact le_trans (by norm_num) psum834o2_29
  · exact le_trans (by norm_num) psum834o2_30
  · exact le_trans (by norm_num) psum834o2_31
  · exact le_trans (by norm_num) psum834o2_32
  · exact le_trans (by norm_num) psum834o2_33
  · exact le_trans (by norm_num) psum834o2_34
  · exact le_trans (by norm_num) psum834o2_35
  · exact le_trans (by norm_num) psum834o2_36
  · exact le_trans (by norm_num) psum834o2_37
  · exact le_trans (by norm_num) psum834o2_38
  · exact le_trans (by norm_num) psum834o2_39
  · exact le_trans (by norm_num) psum834o2_40
  · exact le_trans (by norm_num) psum834o2_41
  · exact le_trans (by norm_num) psum834o2_42
  · exact le_trans (by norm_num) psum834o2_43
  · exact le_trans (by norm_num) psum834o2_44
  · exact le_trans (by norm_num) psum834o2_45
  · exact le_trans (by norm_num) psum834o2_46
  · exact le_trans (by norm_num) psum834o2_47
  · exact le_trans (by norm_num) psum834o2_48
  · exact le_trans (by norm_num) psum834o2_49
  · exact le_trans (by norm_num) psum834o2_50
  · exact le_trans (by norm_num) psum834o2_51
  · exact le_trans (by norm_num) psum834o2_52
  · exact le_trans (by norm_num) psum834o2_53
  · exact le_trans (by norm_num) psum834o2_54
  · exact le_trans (by norm_num) psum834o2_55
  · exact le_trans (by norm_num) psum834o2_56
  · exact le_trans (by norm_num) psum834o2_57
  · exact le_trans (by norm_num) psum834o2_58
  · exact le_trans (by norm_num) psum834o2_59
  · exact le_trans (by norm_num) psum834o2_60
  · exact le_trans (by norm_num) psum834o2_61
  · exact le_trans (by norm_num) psum834o2_62
  · exact le_trans (by norm_num) psum834o2_63
  · exact le_trans (by norm_num) psum834o2_64
  · exact le_trans (by norm_num) psum834o2_65
  · exact le_trans (by norm_num) psum834o2_66
  · exact le_trans (by norm_num) psum834o2_67
  · exact le_trans (by norm_num) psum834o2_68
  · exact le_trans (by norm_num) psum834o2_69
  · exact le_trans (by norm_num) psum834o2_70
  · exact le_trans (by norm_num) psum834o2_71
  · exact le_trans (by norm_num) psum834o2_72
  · exact le_trans (by norm_num) psum834o2_73
  · exact le_trans (by norm_num) psum834o2_74
  · exact le_trans (by norm_num) psum834o2_75
  · exact le_trans (by norm_num) psum834o2_76
  · exact le_trans (by norm_num) psum834o2_77
  · exact le_trans (by norm_num) psum834o2_78
  · exact le_trans (by norm_num) psum834o2_79
  · exact le_trans (by norm_num) psum834o2_80
  · exact le_trans (by norm_num) psum834o2_81
  · exact le_trans (by norm_num) psum834o2_82
  · exact le_trans (by norm_num) psum834o2_83
  · exact le_trans (by norm_num) psum834o2_84
  · exact le_trans (by norm_num) psum834o2_85
  · exact le_trans (by norm_num) psum834o2_86
  · exact le_trans (by norm_num) psum834o2_87
  · exact le_trans (by norm_num) psum834o2_88
  · exact le_trans (by norm_num) psum834o2_89
  · exact le_trans (by norm_num) psum834o2_90
  · exact le_trans (by norm_num) psum834o2_91
  · exact le_trans (by norm_num) psum834o2_92
  · exact le_trans (by norm_num) psum834o2_93
  · exact le_trans (by norm_num) psum834o2_94
  · exact le_trans (by norm_num) psum834o2_95
  · exact le_trans (by norm_num) psum834o2_96
  · exact le_trans (by norm_num) psum834o2_97
  · exact le_trans (by norm_num) psum834o2_98
  · exact le_trans (by norm_num) psum834o2_99
  · exact le_trans (by norm_num) psum834o2_100
  · exact le_trans (by norm_num) psum834o2_101
  · exact le_trans (by norm_num) psum834o2_102
  · exact le_trans (by norm_num) psum834o2_103
  · exact le_trans (by norm_num) psum834o2_104
  · exact le_trans (by norm_num) psum834o2_105
  · exact le_trans (by norm_num) psum834o2_106
  · exact le_trans (by norm_num) psum834o2_107
  · exact le_trans (by norm_num) psum834o2_108
  · exact le_trans (by norm_num) psum834o2_109
  · exact le_trans (by norm_num) psum834o2_110
  · exact le_trans (by norm_num) psum834o2_111
  · exact le_trans (by norm_num) psum834o2_112
  · exact le_trans (by norm_num) psum834o2_113
  · exact le_trans (by norm_num) psum834o2_114
  · exact le_trans (by norm_num) psum834o2_115
  · exact le_trans (by norm_num) psum834o2_116
  · exact le_trans (by norm_num) psum834o2_117
  · exact le_trans (by norm_num) psum834o2_118
  · exact le_trans (by norm_num) psum834o2_119
  · exact le_trans (by norm_num) psum834o2_120
  · exact le_trans (by norm_num) psum834o2_121
  · exact le_trans (by norm_num) psum834o2_122
  · exact le_trans (by norm_num) psum834o2_123
  · exact le_trans (by norm_num) psum834o2_124
  · exact le_trans (by norm_num) psum834o2_125
  · exact le_trans (by norm_num) psum834o2_126
  · exact le_trans (by norm_num) psum834o2_127
  · exact le_trans (by norm_num) psum834o2_128
  · exact le_trans (by norm_num) psum834o2_129
  · exact le_trans (by norm_num) psum834o2_130
  · exact le_trans (by norm_num) psum834o2_131
  · exact le_trans (by norm_num) psum834o2_132
  · exact le_trans (by norm_num) psum834o2_133
  · exact le_trans (by norm_num) psum834o2_134
  · exact le_trans (by norm_num) psum834o2_135
  · exact le_trans (by norm_num) psum834o2_136
  · exact le_trans (by norm_num) psum834o2_137
  · exact le_trans (by norm_num) psum834o2_138
  · exact le_trans (by norm_num) psum834o2_139
  · exact le_trans (by norm_num) psum834o2_140
  · exact le_trans (by norm_num) psum834o2_141
  · exact le_trans (by norm_num) psum834o2_142
  · exact le_trans (by norm_num) psum834o2_143
  · exact le_trans (by norm_num) psum834o2_144
  · exact le_trans (by norm_num) psum834o2_145
  · exact le_trans (by norm_num) psum834o2_146
  · exact le_trans (by norm_num) psum834o2_147
  · exact le_trans (by norm_num) psum834o2_148
  · exact le_trans (by norm_num) psum834o2_149
  · exact le_trans (by norm_num) psum834o2_150
  · exact le_trans (by norm_num) psum834o2_151
  · exact le_trans (by norm_num) psum834o2_152
  · exact le_trans (by norm_num) psum834o2_153
  · exact le_trans (by norm_num) psum834o2_154
  · exact le_trans (by norm_num) psum834o2_155
  · exact le_trans (by norm_num) psum834o2_156
  · exact le_trans (by norm_num) psum834o2_157
  · exact le_trans (by norm_num) psum834o2_158
  · exact le_trans (by norm_num) psum834o2_159
  · exact le_trans (by norm_num) psum834o2_160
  · exact le_trans (by norm_num) psum834o2_161
  · exact le_trans (by norm_num) psum834o2_162
  · exact le_trans (by norm_num) psum834o2_163
  · exact le_trans (by norm_num) psum834o2_164
  · exact le_trans (by norm_num) psum834o2_165
  · exact le_trans (by norm_num) psum834o2_166
  · exact le_trans (by norm_num) psum834o2_167
  · exact le_trans (by norm_num) psum834o2_168
  · exact le_trans (by norm_num) psum834o2_169
  · exact le_trans (by norm_num) psum834o2_170
  · exact le_trans (by norm_num) psum834o2_171
  · exact le_trans (by norm_num) psum834o2_172
  · exact le_trans (by norm_num) psum834o2_173
  · exact le_trans (by norm_num) psum834o2_174
  · exact le_trans (by norm_num) psum834o2_175
  · exact le_trans (by norm_num) psum834o2_176
  · exact le_trans (by norm_num) psum834o2_177
  · exact le_trans (by norm_num) psum834o2_178
  · exact le_trans (by norm_num) psum834o2_179
  · exact le_trans (by norm_num) psum834o2_180
  · exact le_trans (by norm_num) psum834o2_181
  · exact le_trans (by norm_num) psum834o2_182
  · exact le_trans (by norm_num) psum834o2_183
  · exact le_trans (by norm_num) psum834o2_184
  · exact le_trans (by norm_num) psum834o2_185
  · exact le_trans (by norm_num) psum834o2_186
  · exact le_trans (by norm_num) psum834o2_187
  · exact le_trans (by norm_num) psum834o2_188
  · exact le_trans (by norm_num) psum834o2_189
  · exact le_trans (by norm_num) psum834o2_190
  · exact le_trans (by norm_num) psum834o2_191
  · exact le_trans (by norm_num) psum834o2_192
  · exact le_trans (by norm_num) psum834o2_193
  · exact le_trans (by norm_num) psum834o2_194
  · exact le_trans (by norm_num) psum834o2_195
  · exact le_trans (by norm_num) psum834o2_196
  · exact le_trans (by norm_num) psum834o2_197
  · exact le_trans (by norm_num) psum834o2_198
  · exact le_trans (by norm_num) psum834o2_199
  · exact le_trans (by norm_num) psum834o2_200
  · exact le_trans (by norm_num) psum834o2_201
  · exact le_trans (by norm_num) psum834o2_202
  · exact le_trans (by norm_num) psum834o2_203
  · exact le_trans (by norm_num) psum834o2_204
  · exact le_trans (by norm_num) psum834o2_205
  · exact le_trans (by norm_num) psum834o2_206
  · exact le_trans (by norm_num) psum834o2_207
  · exact le_trans (by norm_num) psum834o2_208
  · exact le_trans (by norm_num) psum834o2_209
  · exact le_trans (by norm_num) psum834o2_210
  · exact le_trans (by norm_num) psum834o2_211
  · exact le_trans (by norm_num) psum834o2_212
  · exact le_trans (by norm_num) psum834o2_213
  · exact le_trans (by norm_num) psum834o2_214
  · exact le_trans (by norm_num) psum834o2_215
  · exact le_trans (by norm_num) psum834o2_216
  · exact le_trans (by norm_num) psum834o2_217
  · exact le_trans (by norm_num) psum834o2_218
  · exact le_trans (by norm_num) psum834o2_219
  · exact le_trans (by norm_num) psum834o2_220
  · exact le_trans (by norm_num) psum834o2_221
  · exact le_trans (by norm_num) psum834o2_222
  · exact le_trans (by norm_num) psum834o2_223
  · exact le_trans (by norm_num) psum834o2_224
  · exact le_trans (by norm_num) psum834o2_225
  · exact le_trans (by norm_num) psum834o2_226
  · exact le_trans (by norm_num) psum834o2_227
  · exact le_trans (by norm_num) psum834o2_228
  · exact le_trans (by norm_num) psum834o2_229
  · exact le_trans (by norm_num) psum834o2_230
  · exact le_trans (by norm_num) psum834o2_231
  · exact le_trans (by norm_num) psum834o2_232
  · exact le_trans (by norm_num) psum834o2_233
  · exact le_trans (by norm_num) psum834o2_234
  · exact le_trans (by norm_num) psum834o2_235
  · exact le_trans (by norm_num) psum834o2_236
  · exact le_trans (by norm_num) psum834o2_237
  · exact le_trans (by norm_num) psum834o2_238
  · exact le_trans (by norm_num) psum834o2_239
  · exact le_trans (by norm_num) psum834o2_240
  · exact le_trans (by norm_num) psum834o2_241
  · exact le_trans (by norm_num) psum834o2_242
  · exact le_trans (by norm_num) psum834o2_243
  · exact le_trans (by norm_num) psum834o2_244
  · exact le_trans (by norm_num) psum834o2_245
  · exact le_trans (by norm_num) psum834o2_246
  · exact le_trans (by norm_num) psum834o2_247
  · exact le_trans (by norm_num) psum834o2_248
  · exact le_trans (by norm_num) psum834o2_249
  · exact le_trans (by norm_num) psum834o2_250
  · exact le_trans (by norm_num) psum834o2_251
  · exact le_trans (by norm_num) psum834o2_252
  · exact le_trans (by norm_num) psum834o2_253
  · exact le_trans (by norm_num) psum834o2_254
  · exact le_trans (by norm_num) psum834o2_255
  · exact le_trans (by norm_num) psum834o2_256
  · exact le_trans (by norm_num) psum834o2_257
  · exact le_trans (by norm_num) psum834o2_258
  · exact le_trans (by norm_num) psum834o2_259
  · exact le_trans (by norm_num) psum834o2_260
  · exact le_trans (by norm_num) psum834o2_261
  · exact le_trans (by norm_num) psum834o2_262
  · exact le_trans (by norm_num) psum834o2_263
  · exact le_trans (by norm_num) psum834o2_264
  · exact le_trans (by norm_num) psum834o2_265
  · exact le_trans (by norm_num) psum834o2_266
  · exact le_trans (by norm_num) psum834o2_267
  · exact le_trans (by norm_num) psum834o2_268
  · exact le_trans (by norm_num) psum834o2_269
  · exact le_trans (by norm_num) psum834o2_270
  · exact le_trans (by norm_num) psum834o2_271
  · exact le_trans (by norm_num) psum834o2_272
  · exact le_trans (by norm_num) psum834o2_273
  · exact le_trans (by norm_num) psum834o2_274
  · exact le_trans (by norm_num) psum834o2_275
  · exact le_trans (by norm_num) psum834o2_276
  · exact le_trans (by norm_num) psum834o2_277
  · exact le_trans (by norm_num) psum834o2_278
  · exact le_trans (by norm_num) psum834o2_279
  · exact le_trans (by norm_num) psum834o2_280
  · exact le_trans (by norm_num) psum834o2_281
  · exact le_trans (by norm_num) psum834o2_282
  · exact le_trans (by norm_num) psum834o2_283
  · exact le_trans (by norm_num) psum834o2_284
  · exact le_trans (by norm_num) psum834o2_285
  · exact le_trans (by norm_num) psum834o2_286
  · exact le_trans (by norm_num) psum834o2_287
  · exact le_trans (by norm_num) psum834o2_288
  · exact le_trans (by norm_num) psum834o2_289
  · exact le_trans (by norm_num) psum834o2_290
  · exact le_trans (by norm_num) psum834o2_291
  · exact le_trans (by norm_num) psum834o2_292
  · exact le_trans (by norm_num) psum834o2_293
  · exact le_trans (by norm_num) psum834o2_294
  · exact le_trans (by norm_num) psum834o2_295
  · exact le_trans (by norm_num) psum834o2_296
  · exact le_trans (by norm_num) psum834o2_297
  · exact le_trans (by norm_num) psum834o2_298
  · exact le_trans (by norm_num) psum834o2_299
  · exact le_trans (by norm_num) psum834o2_300
  · exact le_trans (by norm_num) psum834o2_301
  · exact le_trans (by norm_num) psum834o2_302
  · exact le_trans (by norm_num) psum834o2_303
  · exact le_trans (by norm_num) psum834o2_304
  · exact le_trans (by norm_num) psum834o2_305
  · exact le_trans (by norm_num) psum834o2_306
  · exact le_trans (by norm_num) psum834o2_307
  · exact le_trans (by norm_num) psum834o2_308
  · exact le_trans (by norm_num) psum834o2_309
  · exact le_trans (by norm_num) psum834o2_310
  · exact le_trans (by norm_num) psum834o2_311
  · exact le_trans (by norm_num) psum834o2_312
  · exact le_trans (by norm_num) psum834o2_313
  · exact le_trans (by norm_num) psum834o2_314
  · exact le_trans (by norm_num) psum834o2_315
  · exact le_trans (by norm_num) psum834o2_316
  · exact le_trans (by norm_num) psum834o2_317
  · exact le_trans (by norm_num) psum834o2_318
  · exact le_trans (by norm_num) psum834o2_319
  · exact le_trans (by norm_num) psum834o2_320
  · exact le_trans (by norm_num) psum834o2_321
  · exact le_trans (by norm_num) psum834o2_322
  · exact le_trans (by norm_num) psum834o2_323
  · exact le_trans (by norm_num) psum834o2_324
  · exact le_trans (by norm_num) psum834o2_325
  · exact le_trans (by norm_num) psum834o2_326
  · exact le_trans (by norm_num) psum834o2_327
  · exact le_trans (by norm_num) psum834o2_328
  · exact le_trans (by norm_num) psum834o2_329
  · exact le_trans (by norm_num) psum834o2_330
  · exact le_trans (by norm_num) psum834o2_331
  · exact le_trans (by norm_num) psum834o2_332
  · exact le_trans (by norm_num) psum834o2_333
  · exact le_trans (by norm_num) psum834o2_334
  · exact le_trans (by norm_num) psum834o2_335
  · exact le_trans (by norm_num) psum834o2_336
  · exact le_trans (by norm_num) psum834o2_337
  · exact le_trans (by norm_num) psum834o2_338
  · exact le_trans (by norm_num) psum834o2_339
  · exact le_trans (by norm_num) psum834o2_340
  · exact le_trans (by norm_num) psum834o2_341
  · exact le_trans (by norm_num) psum834o2_342
  · exact le_trans (by norm_num) psum834o2_343
  · exact le_trans (by norm_num) psum834o2_344
  · exact le_trans (by norm_num) psum834o2_345
  · exact le_trans (by norm_num) psum834o2_346
  · exact le_trans (by norm_num) psum834o2_347
  · exact le_trans (by norm_num) psum834o2_348
  · exact le_trans (by norm_num) psum834o2_349
  · exact le_trans (by norm_num) psum834o2_350
  · exact le_trans (by norm_num) psum834o2_351
  · exact le_trans (by norm_num) psum834o2_352
  · exact le_trans (by norm_num) psum834o2_353
  · exact le_trans (by norm_num) psum834o2_354
  · exact le_trans (by norm_num) psum834o2_355
  · exact le_trans (by norm_num) psum834o2_356
  · exact le_trans (by norm_num) psum834o2_357
  · exact le_trans (by norm_num) psum834o2_358
  · exact le_trans (by norm_num) psum834o2_359
  · exact le_trans (by norm_num) psum834o2_360
  · exact le_trans (by norm_num) psum834o2_361
  · exact le_trans (by norm_num) psum834o2_362
  · exact le_trans (by norm_num) psum834o2_363
  · exact le_trans (by norm_num) psum834o2_364
  · exact le_trans (by norm_num) psum834o2_365
  · exact le_trans (by norm_num) psum834o2_366
  · exact le_trans (by norm_num) psum834o2_367
  · exact le_trans (by norm_num) psum834o2_368
  · exact le_trans (by norm_num) psum834o2_369
  · exact le_trans (by norm_num) psum834o2_370
  · exact le_trans (by norm_num) psum834o2_371
  · exact le_trans (by norm_num) psum834o2_372
  · exact le_trans (by norm_num) psum834o2_373
  · exact le_trans (by norm_num) psum834o2_374
  · exact le_trans (by norm_num) psum834o2_375
  · exact le_trans (by norm_num) psum834o2_376
  · exact le_trans (by norm_num) psum834o2_377
  · exact le_trans (by norm_num) psum834o2_378
  · exact le_trans (by norm_num) psum834o2_379
  · exact le_trans (by norm_num) psum834o2_380
  · exact le_trans (by norm_num) psum834o2_381
  · exact le_trans (by norm_num) psum834o2_382
  · exact le_trans (by norm_num) psum834o2_383
  · exact le_trans (by norm_num) psum834o2_384
  · exact le_trans (by norm_num) psum834o2_385
  · exact le_trans (by norm_num) psum834o2_386
  · exact le_trans (by norm_num) psum834o2_387
  · exact le_trans (by norm_num) psum834o2_388
  · exact le_trans (by norm_num) psum834o2_389
  · exact le_trans (by norm_num) psum834o2_390
  · exact le_trans (by norm_num) psum834o2_391
  · exact le_trans (by norm_num) psum834o2_392
  · exact le_trans (by norm_num) psum834o2_393
  · exact le_trans (by norm_num) psum834o2_394
  · exact le_trans (by norm_num) psum834o2_395
  · exact le_trans (by norm_num) psum834o2_396
  · exact le_trans (by norm_num) psum834o2_397
  · exact le_trans (by norm_num) psum834o2_398
  · exact le_trans (by norm_num) psum834o2_399
  · exact le_trans (by norm_num) psum834o2_400
  · exact le_trans (by norm_num) psum834o2_401
  · exact le_trans (by norm_num) psum834o2_402
  · exact le_trans (by norm_num) psum834o2_403
  · exact le_trans (by norm_num) psum834o2_404
  · exact le_trans (by norm_num) psum834o2_405
  · exact le_trans (by norm_num) psum834o2_406
  · exact le_trans (by norm_num) psum834o2_407
  · exact le_trans (by norm_num) psum834o2_408
  · exact le_trans (by norm_num) psum834o2_409
  · exact le_trans (by norm_num) psum834o2_410
  · exact le_trans (by norm_num) psum834o2_411
  · exact le_trans (by norm_num) psum834o2_412
  · exact le_trans (by norm_num) psum834o2_413
  · exact le_trans (by norm_num) psum834o2_414
  · exact le_trans (by norm_num) psum834o2_415
  · exact le_trans (by norm_num) psum834o2_416
  · exact le_trans (by norm_num) psum834o2_417
  · exact le_trans (by norm_num) psum834o2_418
  · exact le_trans (by norm_num) psum834o2_419
  · exact le_trans (by norm_num) psum834o2_420
  · exact le_trans (by norm_num) psum834o2_421
  · exact le_trans (by norm_num) psum834o2_422
  · exact le_trans (by norm_num) psum834o2_423
  · exact le_trans (by norm_num) psum834o2_424
  · exact le_trans (by norm_num) psum834o2_425
  · exact le_trans (by norm_num) psum834o2_426
  · exact le_trans (by norm_num) psum834o2_427
  · exact le_trans (by norm_num) psum834o2_428
  · exact le_trans (by norm_num) psum834o2_429
  · exact le_trans (by norm_num) psum834o2_430
  · exact le_trans (by norm_num) psum834o2_431
  · exact le_trans (by norm_num) psum834o2_432
  · exact le_trans (by norm_num) psum834o2_433
  · exact le_trans (by norm_num) psum834o2_434
  · exact le_trans (by norm_num) psum834o2_435
  · exact le_trans (by norm_num) psum834o2_436
  · exact le_trans (by norm_num) psum834o2_437
  · exact le_trans (by norm_num) psum834o2_438
  · exact le_trans (by norm_num) psum834o2_439
  · exact le_trans (by norm_num) psum834o2_440
  · exact le_trans (by norm_num) psum834o2_441
  · exact le_trans (by norm_num) psum834o2_442
  · exact le_trans (by norm_num) psum834o2_443
  · exact le_trans (by norm_num) psum834o2_444
  · exact le_trans (by norm_num) psum834o2_445
  · exact le_trans (by norm_num) psum834o2_446
  · exact le_trans (by norm_num) psum834o2_447
  · exact le_trans (by norm_num) psum834o2_448
  · exact le_trans (by norm_num) psum834o2_449
  · exact le_trans (by norm_num) psum834o2_450
  · exact le_trans (by norm_num) psum834o2_451
  · exact le_trans (by norm_num) psum834o2_452
  · exact le_trans (by norm_num) psum834o2_453
  · exact le_trans (by norm_num) psum834o2_454
  · exact le_trans (by norm_num) psum834o2_455
  · exact le_trans (by norm_num) psum834o2_456
  · exact le_trans (by norm_num) psum834o2_457
  · exact le_trans (by norm_num) psum834o2_458
  · exact le_trans (by norm_num) psum834o2_459
  · exact le_trans (by norm_num) psum834o2_460
  · exact le_trans (by norm_num) psum834o2_461
  · exact le_trans (by norm_num) psum834o2_462
  · exact le_trans (by norm_num) psum834o2_463
  · exact le_trans (by norm_num) psum834o2_464
  · exact le_trans (by norm_num) psum834o2_465
  · exact le_trans (by norm_num) psum834o2_466
  · exact le_trans (by norm_num) psum834o2_467
  · exact le_trans (by norm_num) psum834o2_468
  · exact le_trans (by norm_num) psum834o2_469
  · exact le_trans (by norm_num) psum834o2_470
  · exact le_trans (by norm_num) psum834o2_471
  · exact le_trans (by norm_num) psum834o2_472
  · exact le_trans (by norm_num) psum834o2_473
  · exact le_trans (by norm_num) psum834o2_474
  · exact le_trans (by norm_num) psum834o2_475
  · exact le_trans (by norm_num) psum834o2_476
  · exact le_trans (by norm_num) psum834o2_477
  · exact le_trans (by norm_num) psum834o2_478
  · exact le_trans (by norm_num) psum834o2_479
  · exact le_trans (by norm_num) psum834o2_480
  · exact le_trans (by norm_num) psum834o2_481
  · exact le_trans (by norm_num) psum834o2_482
  · exact le_trans (by norm_num) psum834o2_483
  · exact le_trans (by norm_num) psum834o2_484
  · exact le_trans (by norm_num) psum834o2_485
  · exact le_trans (by norm_num) psum834o2_486
  · exact le_trans (by norm_num) psum834o2_487
  · exact le_trans (by norm_num) psum834o2_488
  · exact le_trans (by norm_num) psum834o2_489
  · exact le_trans (by norm_num) psum834o2_490
  · exact le_trans (by norm_num) psum834o2_491
  · exact le_trans (by norm_num) psum834o2_492
  · exact le_trans (by norm_num) psum834o2_493
  · exact le_trans (by norm_num) psum834o2_494
  · exact le_trans (by norm_num) psum834o2_495
  · exact le_trans (by norm_num) psum834o2_496
  · exact le_trans (by norm_num) psum834o2_497
  · exact le_trans (by norm_num) psum834o2_498
  · exact le_trans (by norm_num) psum834o2_499
  · exact le_trans (by norm_num) psum834o2_500

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum834o2_floor
#print axioms CriticalLinePhasor.DVP.psum834o2_500
end AxiomAudit
