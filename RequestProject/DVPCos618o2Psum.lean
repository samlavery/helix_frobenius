import RequestProject.DVPCos618o2Table

/-!
# The cosine partial-sum floor, `t = 618/2` (N = 500)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 618/2` segment certificate. -/
def cos618o2c (n : ℕ) : ℝ := Real.cos (((618:ℕ):ℝ) * (Real.log n / 2))

theorem psum618o2_11 : ((55823/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos618o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 11 - ((223317/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum618o2_12 : ((234509/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos618o2c k) + cos618o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_11
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 12 - ((279477/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_13 : ((180341/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos618o2c k) + cos618o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_12
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 13 - ((126193/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_14 : ((2026833/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos618o2c k) + cos618o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_13
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 14 - ((223523/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_15 : ((2458919/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos618o2c k) + cos618o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_14
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 15 - ((216093/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_16 : ((1856881/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos618o2c k) + cos618o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_15
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 16 - ((-300969/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_17 : ((135179/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos618o2c k) + cos618o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_16
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 17 - ((-504991/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_18 : ((392683/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos618o2c k) + cos618o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_17
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 18 - ((24469/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_19 : ((574333/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos618o2c k) + cos618o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_18
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 19 - ((334017/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_20 : ((1833477/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos618o2c k) + cos618o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_19
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 20 - ((-92751/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_21 : ((1684371/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos618o2c k) + cos618o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_20
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 21 - ((-74503/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_22 : ((1340203/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos618o2c k) + cos618o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_21
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 22 - ((199227/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_23 : ((2988801/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos618o2c k) + cos618o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_22
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 23 - ((61699/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_24 : ((680267/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos618o2c k) + cos618o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_23
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 24 - ((-267633/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_25 : ((1203883/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos618o2c k) + cos618o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_24
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 25 - ((-156601/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_26 : ((2535923/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos618o2c k) + cos618o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_25
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 26 - ((128257/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_27 : ((169739/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos618o2c k) + cos618o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_26
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 27 - ((858957/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_28 : ((4097683/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos618o2c k) + cos618o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_27
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 28 - ((703003/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_29 : ((1643969/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos618o2c k) + cos618o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_28
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 29 - ((-161929/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_30 : ((636161/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos618o2c k) + cos618o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_29
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 30 - ((-107033/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_31 : ((781623/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos618o2c k) + cos618o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_30
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 31 - ((72741/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_32 : ((46499/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos618o2c k) + cos618o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_31
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 32 - ((-932079/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_33 : ((1967461/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos618o2c k) + cos618o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_32
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 33 - ((479543/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_34 : ((1525597/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos618o2c k) + cos618o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_33
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 34 - ((-220907/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_35 : ((2268/625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos618o2c k) + cos618o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_34
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 35 - ((288853/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_36 : ((3732567/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos618o2c k) + cos618o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_35
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 36 - ((103867/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_37 : ((357359/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos618o2c k) + cos618o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_36
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 37 - ((-174719/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_38 : ((3638823/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos618o2c k) + cos618o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_37
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 38 - ((780051/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_39 : ((2060653/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos618o2c k) + cos618o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_38
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 39 - ((482583/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_40 : ((3260623/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos618o2c k) + cos618o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_39
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 40 - ((-860583/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_41 : ((1286399/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos618o2c k) + cos618o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_40
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 41 - ((-27509/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_42 : ((2966369/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos618o2c k) + cos618o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_41
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 42 - ((393671/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_43 : ((493799/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos618o2c k) + cos618o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_42
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 43 - ((984123/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_44 : ((4751111/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos618o2c k) + cos618o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_43
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 44 - ((800819/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_45 : ((200623/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos618o2c k) + cos618o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_44
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 45 - ((66141/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_46 : ((955449/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos618o2c k) + cos618o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_45
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 46 - ((-23823/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_47 : ((421019/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos618o2c k) + cos618o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_46
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 47 - ((-113391/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_48 : ((3475461/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos618o2c k) + cos618o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_47
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 48 - ((-734629/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_49 : ((167741/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos618o2c k) + cos618o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_48
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 49 - ((-158301/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_50 : ((958829/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos618o2c k) + cos618o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_49
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 50 - ((-383049/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_51 : ((1266813/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos618o2c k) + cos618o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_50
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 51 - ((-130149/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_52 : ((85387/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos618o2c k) + cos618o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_51
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 52 - ((-412843/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_53 : ((206373/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos618o2c k) + cos618o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_52
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 53 - ((-14139/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_54 : ((321581/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos618o2c k) + cos618o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_53
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 54 - ((115233/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_55 : ((2173939/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos618o2c k) + cos618o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_54
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 55 - ((177543/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_56 : ((1572939/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos618o2c k) + cos618o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_55
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 56 - ((972039/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_57 : ((3642447/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos618o2c k) + cos618o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_56
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 57 - ((496669/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_58 : ((815687/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos618o2c k) + cos618o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_57
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 58 - ((-379599/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_59 : ((2278879/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos618o2c k) + cos618o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_58
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 59 - ((-983769/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_60 : ((1664539/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos618o2c k) + cos618o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_59
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 60 - ((-3839/6250 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_61 : ((431257/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos618o2c k) + cos618o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_60
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 61 - ((245923/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_62 : ((391979/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos618o2c k) + cos618o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_61
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 62 - ((979647/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_63 : ((3165359/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos618o2c k) + cos618o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_62
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 63 - ((29627/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_64 : ((1091021/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos618o2c k) + cos618o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_63
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 64 - ((-983217/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_65 : ((1923049/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos618o2c k) + cos618o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_64
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 65 - ((-258893/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_66 : ((1443739/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos618o2c k) + cos618o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_65
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 66 - ((964529/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_67 : ((617497/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos618o2c k) + cos618o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_66
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 67 - ((200107/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_68 : ((16717/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos618o2c k) + cos618o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_67
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 68 - ((-3118/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_69 : ((2223537/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos618o2c k) + cos618o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_68
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 69 - ((33503/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_70 : ((1572113/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos618o2c k) + cos618o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_69
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 70 - ((920789/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_71 : ((2477223/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos618o2c k) + cos618o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_70
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 71 - ((-666903/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_72 : ((2042041/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos618o2c k) + cos618o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_71
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 72 - ((-217541/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_73 : ((3041941/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos618o2c k) + cos618o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_72
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 73 - ((1 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_74 : ((2555071/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos618o2c k) + cos618o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_73
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 74 - ((-48677/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_75 : ((415503/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos618o2c k) + cos618o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_74
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 75 - ((-29841/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_76 : ((3069999/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos618o2c k) + cos618o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_75
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 76 - ((124073/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_77 : ((2356053/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos618o2c k) + cos618o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_76
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 77 - ((-356923/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_78 : ((144087/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos618o2c k) + cos618o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_77
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 78 - ((-50561/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_79 : ((3053489/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos618o2c k) + cos618o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_78
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 79 - ((748197/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_80 : ((410717/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos618o2c k) + cos618o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_79
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 80 - ((-249951/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_81 : ((2807423/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos618o2c k) + cos618o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_80
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 81 - ((376969/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_82 : ((2604571/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos618o2c k) + cos618o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_81
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 82 - ((-3168/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_83 : ((27691/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos618o2c k) + cos618o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_82
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 83 - ((-389191/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_84 : ((3033677/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos618o2c k) + cos618o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_83
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 84 - ((818497/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_85 : ((1019127/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos618o2c k) + cos618o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_84
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 85 - ((-995323/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_86 : ((1484199/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos618o2c k) + cos618o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_85
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 86 - ((232561/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_87 : ((569057/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos618o2c k) + cos618o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_86
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 87 - ((-69207/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_88 : ((1320957/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos618o2c k) + cos618o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_87
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 88 - ((182893/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_89 : ((654323/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos618o2c k) + cos618o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_88
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 89 - ((-12261/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_90 : ((116733/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos618o2c k) + cos618o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_89
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 90 - ((-70633/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_91 : ((573021/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos618o2c k) + cos618o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_90
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 91 - ((106109/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_92 : ((537833/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos618o2c k) + cos618o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_91
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 92 - ((-713673/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_93 : ((747321/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos618o2c k) + cos618o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_92
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 93 - ((209513/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_94 : ((1296/625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos618o2c k) + cos618o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_93
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 94 - ((-14306/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_95 : ((3033003/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos618o2c k) + cos618o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_94
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 95 - ((959503/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_96 : ((512797/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos618o2c k) + cos618o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_95
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 96 - ((-196343/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_97 : ((1521259/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos618o2c k) + cos618o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_96
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 97 - ((99143/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_98 : ((2047753/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos618o2c k) + cos618o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_97
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 98 - ((-198933/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_99 : ((3041843/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos618o2c k) + cos618o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_98
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 99 - ((99419/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_100 : ((1026039/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos618o2c k) + cos618o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_99
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 100 - ((-197933/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_101 : ((3029839/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos618o2c k) + cos618o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_100
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 101 - ((977861/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_102 : ((2076811/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos618o2c k) + cos618o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_101
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 102 - ((-29779/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_103 : ((2983579/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos618o2c k) + cos618o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_102
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 103 - ((226717/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_104 : ((1076567/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos618o2c k) + cos618o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_103
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 104 - ((-166069/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_105 : ((1433487/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos618o2c k) + cos618o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_104
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 105 - ((35697/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_106 : ((463363/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos618o2c k) + cos618o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_105
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 106 - ((-550059/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_107 : ((66309/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos618o2c k) + cos618o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_106
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 107 - ((67129/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_108 : ((2577191/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos618o2c k) + cos618o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_107
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 108 - ((-75069/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_109 : ((1180151/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos618o2c k) + cos618o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_108
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 109 - ((-216789/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_110 : ((2872771/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos618o2c k) + cos618o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_109
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 110 - ((512569/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_111 : ((2099803/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos618o2c k) + cos618o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_110
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 111 - ((-193217/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_112 : ((304983/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos618o2c k) + cos618o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_111
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 112 - ((950127/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_113 : ((8211/4000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos618o2c k) + cos618o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_112
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 113 - ((-49849/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_114 : ((366467/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos618o2c k) + cos618o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_113
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 114 - ((439543/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_115 : ((1170817/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos618o2c k) + cos618o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_114
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 115 - ((-295001/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_116 : ((125279/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos618o2c k) + cos618o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_115
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 116 - ((82023/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_117 : ((2824227/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos618o2c k) + cos618o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_116
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 117 - ((318747/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_118 : ((208203/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos618o2c k) + cos618o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_117
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 118 - ((-742097/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_119 : ((3061877/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos618o2c k) + cos618o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_118
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 119 - ((979947/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_120 : ((531049/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos618o2c k) + cos618o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_119
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 120 - ((-937581/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_121 : ((1359981/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos618o2c k) + cos618o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_120
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 121 - ((297933/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_122 : ((2679897/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos618o2c k) + cos618o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_121
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 122 - ((-7993/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_123 : ((1066239/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos618o2c k) + cos618o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_122
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 123 - ((-547319/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_124 : ((614207/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos618o2c k) + cos618o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_123
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 124 - ((938657/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_125 : ((105893/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos618o2c k) + cos618o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_124
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 125 - ((-38123/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_126 : ((667243/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos618o2c k) + cos618o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_125
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 126 - ((137803/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_127 : ((2783719/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos618o2c k) + cos618o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_126
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 127 - ((114847/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_128 : ((2043569/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos618o2c k) + cos618o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_127
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 128 - ((-14801/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_129 : ((3043469/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos618o2c k) + cos618o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_128
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 129 - ((1 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_130 : ((578729/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos618o2c k) + cos618o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_129
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 130 - ((-728453/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_131 : ((2357107/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos618o2c k) + cos618o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_130
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 131 - ((42291/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_132 : ((189891/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos618o2c k) + cos618o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_131
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 132 - ((681249/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_133 : ((1019113/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos618o2c k) + cos618o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_132
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 133 - ((-99993/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_134 : ((2723877/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos618o2c k) + cos618o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_133
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 134 - ((685751/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_135 : ((2812219/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos618o2c k) + cos618o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_134
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 135 - ((44221/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_136 : ((999439/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos618o2c k) + cos618o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_135
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 136 - ((-813241/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_137 : ((2966003/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos618o2c k) + cos618o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_136
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 137 - ((38689/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_138 : ((1279191/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos618o2c k) + cos618o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_137
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 138 - ((-407521/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_139 : ((1043483/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos618o2c k) + cos618o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_138
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 139 - ((-117829/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_140 : ((307511/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos618o2c k) + cos618o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_139
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 140 - ((247061/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_141 : ((2370333/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos618o2c k) + cos618o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_140
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 141 - ((-704677/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_142 : ((1097639/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos618o2c k) + cos618o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_141
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 142 - ((-34991/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_143 : ((3107539/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos618o2c k) + cos618o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_142
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 143 - ((912361/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_144 : ((1131831/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos618o2c k) + cos618o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_143
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 144 - ((-843777/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_145 : ((2264687/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos618o2c k) + cos618o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_144
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 145 - ((9/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_146 : ((622997/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos618o2c k) + cos618o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_145
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 146 - ((425199/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_147 : ((1113561/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos618o2c k) + cos618o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_146
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 147 - ((-887763/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_148 : ((1136401/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos618o2c k) + cos618o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_147
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 148 - ((2289/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_149 : ((3122161/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos618o2c k) + cos618o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_148
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 149 - ((849459/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_150 : ((2253689/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos618o2c k) + cos618o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_149
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 150 - ((-217093/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_151 : ((277137/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos618o2c k) + cos618o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_150
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 151 - ((-36493/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_152 : ((48828/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos618o2c k) + cos618o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_151
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 152 - ((226999/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_153 : ((2349233/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos618o2c k) + cos618o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_152
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 153 - ((-775659/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_154 : ((1055331/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos618o2c k) + cos618o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_153
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 154 - ((-238471/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_155 : ((48326/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos618o2c k) + cos618o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_154
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 155 - ((491151/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_156 : ((1262097/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos618o2c k) + cos618o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_155
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 156 - ((-56857/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_157 : ((398179/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos618o2c k) + cos618o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_156
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 157 - ((-533199/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_158 : ((744041/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos618o2c k) + cos618o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_157
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 158 - ((985369/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_159 : ((1385037/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos618o2c k) + cos618o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_158
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 159 - ((-20599/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_160 : ((193023/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos618o2c k) + cos618o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_159
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 160 - ((-13121/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_161 : ((6827/2500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos618o2c k) + cos618o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_160
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 161 - ((80067/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_162 : ((1513039/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos618o2c k) + cos618o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_161
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 162 - ((147689/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_163 : ((253307/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos618o2c k) + cos618o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_162
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 163 - ((-499761/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_164 : ((236927/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos618o2c k) + cos618o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_163
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 164 - ((171457/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_165 : ((790153/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos618o2c k) + cos618o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_164
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 165 - ((395721/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_166 : ((234483/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos618o2c k) + cos618o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_165
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 166 - ((-407841/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_167 : ((2018983/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos618o2c k) + cos618o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_166
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 167 - ((-325747/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_168 : ((3017211/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos618o2c k) + cos618o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_167
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 168 - ((124791/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_169 : ((175833/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos618o2c k) + cos618o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_168
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 169 - ((-203783/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_170 : ((958019/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos618o2c k) + cos618o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_169
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 170 - ((-89719/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_171 : ((2559353/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos618o2c k) + cos618o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_170
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 171 - ((128683/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_172 : ((631433/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos618o2c k) + cos618o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_171
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 172 - ((74739/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_173 : ((1122067/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos618o2c k) + cos618o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_172
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 173 - ((-912931/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_174 : ((2035379/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos618o2c k) + cos618o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_173
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 174 - ((-41731/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_175 : ((3035227/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos618o2c k) + cos618o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_174
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 175 - ((249987/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_176 : ((89263/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos618o2c k) + cos618o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_175
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 176 - ((-178711/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_177 : ((1920283/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos618o2c k) + cos618o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_176
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 177 - ((-936033/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_178 : ((2425423/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos618o2c k) + cos618o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_177
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 178 - ((12631/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_179 : ((639317/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos618o2c k) + cos618o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_178
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 179 - ((385631/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_180 : ((245143/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos618o2c k) + cos618o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_179
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 180 - ((-149011/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_181 : ((473939/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos618o2c k) + cos618o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_180
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 181 - ((-277787/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_182 : ((2792867/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos618o2c k) + cos618o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_181
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 182 - ((897211/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_183 : ((62431/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos618o2c k) + cos618o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_182
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 183 - ((328783/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_184 : ((1072983/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos618o2c k) + cos618o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_183
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 184 - ((-243871/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_185 : ((2028269/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos618o2c k) + cos618o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_184
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 185 - ((-117597/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_186 : ((3027907/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos618o2c k) + cos618o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_185
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 186 - ((499869/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_187 : ((370587/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos618o2c k) + cos618o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_186
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 187 - ((-63111/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_188 : ((493607/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos618o2c k) + cos618o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_187
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 188 - ((-123771/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_189 : ((2181639/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos618o2c k) + cos618o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_188
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 189 - ((207311/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_190 : ((3145677/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos618o2c k) + cos618o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_189
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 190 - ((482069/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_191 : ((1415557/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos618o2c k) + cos618o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_190
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 191 - ((-314463/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_192 : ((948029/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos618o2c k) + cos618o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_191
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 192 - ((-233739/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_193 : ((456533/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos618o2c k) + cos618o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_192
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 193 - ((386707/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_194 : ((638871/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos618o2c k) + cos618o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_193
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 194 - ((91179/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_195 : ((691837/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos618o2c k) + cos618o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_194
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 195 - ((-426907/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_196 : ((933583/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos618o2c k) + cos618o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_195
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 196 - ((-450041/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_197 : ((2304349/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos618o2c k) + cos618o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_196
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 197 - ((437283/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_198 : ((3206283/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos618o2c k) + cos618o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_197
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 198 - ((451017/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_199 : ((2787293/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos618o2c k) + cos618o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_198
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 199 - ((-41889/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_200 : ((1870187/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos618o2c k) + cos618o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_199
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 200 - ((-458503/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_201 : ((2241621/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos618o2c k) + cos618o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_200
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 201 - ((185767/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_202 : ((3183157/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos618o2c k) + cos618o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_201
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 202 - ((235409/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_203 : ((90281/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos618o2c k) + cos618o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_202
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 203 - ((-58813/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_204 : ((119939/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos618o2c k) + cos618o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_203
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 204 - ((-242467/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_205 : ((263021/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos618o2c k) + cos618o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_204
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 205 - ((46311/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_206 : ((1548487/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos618o2c k) + cos618o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_205
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 206 - ((496453/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_207 : ((1526071/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos618o2c k) + cos618o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_206
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 207 - ((-11183/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_208 : ((1026361/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos618o2c k) + cos618o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_207
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 208 - ((-24983/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_209 : ((30114/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos618o2c k) + cos618o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_208
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 209 - ((-62663/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_210 : ((725691/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos618o2c k) + cos618o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_209
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 210 - ((60973/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_211 : ((322137/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos618o2c k) + cos618o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_210
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 211 - ((159353/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_212 : ((2314053/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos618o2c k) + cos618o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_211
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 212 - ((-907217/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_213 : ((1790541/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos618o2c k) + cos618o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_212
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 213 - ((-130853/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_214 : ((642893/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos618o2c k) + cos618o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_213
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 214 - ((781131/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_215 : ((1645999/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos618o2c k) + cos618o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_214
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 215 - ((360263/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_216 : ((27033/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos618o2c k) + cos618o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_215
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 216 - ((-294299/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_217 : ((1818883/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos618o2c k) + cos618o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_216
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 217 - ((-884317/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_218 : ((134261/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos618o2c k) + cos618o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_217
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 218 - ((329393/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_219 : ((3132087/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos618o2c k) + cos618o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_218
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 219 - ((984011/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_220 : ((1557989/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos618o2c k) + cos618o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_219
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 220 - ((-16009/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_221 : ((1063811/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos618o2c k) + cos618o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_220
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 221 - ((-30883/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_222 : ((902121/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos618o2c k) + cos618o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_221
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 222 - ((-4041/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_223 : ((267629/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos618o2c k) + cos618o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_222
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 223 - ((218037/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_224 : ((1659997/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos618o2c k) + cos618o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_223
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 224 - ((160951/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_225 : ((107739/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos618o2c k) + cos618o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_224
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 225 - ((-626419/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_226 : ((1804737/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos618o2c k) + cos618o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_225
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 226 - ((-444319/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_227 : ((2071257/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos618o2c k) + cos618o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_226
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 227 - ((13331/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_228 : ((1534757/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos618o2c k) + cos618o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_227
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 228 - ((998357/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_229 : ((3229877/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos618o2c k) + cos618o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_228
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 229 - ((160463/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_230 : ((1151593/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos618o2c k) + cos618o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_229
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 230 - ((-926591/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_231 : ((172549/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos618o2c k) + cos618o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_230
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 231 - ((-144399/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_232 : ((596001/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos618o2c k) + cos618o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_231
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 232 - ((329307/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_233 : ((163609/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos618o2c k) + cos618o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_232
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 233 - ((222069/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_234 : ((19027/6250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos618o2c k) + cos618o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_233
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 234 - ((-2847/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_235 : ((511123/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos618o2c k) + cos618o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_234
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 235 - ((-62483/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_236 : ((883053/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos618o2c k) + cos618o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_235
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 236 - ((-139143/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_237 : ((2620479/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos618o2c k) + cos618o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_236
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 237 - ((854473/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_238 : ((3348799/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos618o2c k) + cos618o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_237
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 238 - ((36421/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_239 : ((2887281/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos618o2c k) + cos618o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_238
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 239 - ((-230709/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_240 : ((381383/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos618o2c k) + cos618o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_239
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 240 - ((-490133/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_241 : ((909973/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos618o2c k) + cos618o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_240
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 241 - ((-86869/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_242 : ((85911/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos618o2c k) + cos618o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_241
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 242 - ((464653/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_243 : ((134953/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos618o2c k) + cos618o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_242
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 243 - ((624773/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_244 : ((351739/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos618o2c k) + cos618o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_243
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 244 - ((-559813/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_245 : ((1854759/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos618o2c k) + cos618o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_244
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 245 - ((-959053/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_246 : ((1829689/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos618o2c k) + cos618o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_245
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 246 - ((-2497/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_247 : ((1385801/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos618o2c k) + cos618o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_246
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 247 - ((942013/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_248 : ((105881/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos618o2c k) + cos618o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_247
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 248 - ((61669/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_249 : ((113639/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos618o2c k) + cos618o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_248
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 249 - ((-547117/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_250 : ((1871133/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos618o2c k) + cos618o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_249
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 250 - ((-484871/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_251 : ((1780511/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 251, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 251, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 250, cos618o2c k) + cos618o2c 251 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 250) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_250
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 251 - ((-45261/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_251).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_252 : ((537639/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 252, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 252, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 251, cos618o2c k) + cos618o2c 252 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 251) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_251
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 252 - ((113473/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_252).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_253 : ((135651/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 253, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 253, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 252, cos618o2c k) + cos618o2c 253 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 252) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_252
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 253 - ((35159/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_253).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_254 : ((593213/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 254, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 254, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 253, cos618o2c k) + cos618o2c 254 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 253) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_253
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 254 - ((-42511/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_254).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_255 : ((1969361/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 255, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 255, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 254, cos618o2c k) + cos618o2c 255 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 254) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_254
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 255 - ((-249151/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_255).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_256 : ((338781/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 256, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 256, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 255, cos618o2c k) + cos618o2c 256 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 255) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_255
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 256 - ((-68839/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_256).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_257 : ((2492851/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 257, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 257, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 256, cos618o2c k) + cos618o2c 257 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 256) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_256
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 257 - ((399523/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_257).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_258 : ((1671349/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 258, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 258, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 257, cos618o2c k) + cos618o2c 258 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 257) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_257
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 258 - ((849947/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_258).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_259 : ((1582039/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 259, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 259, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 258, cos618o2c k) + cos618o2c 259 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 258) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_258
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 259 - ((-4463/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_259).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_260 : ((2184021/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 260, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 260, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 259, cos618o2c k) + cos618o2c 260 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 259) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_259
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 260 - ((-979957/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_260).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_261 : ((1631589/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 261, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 261, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 260, cos618o2c k) + cos618o2c 261 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 260) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_260
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 261 - ((-138083/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_261).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_262 : ((2193229/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 262, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 262, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 261, cos618o2c k) + cos618o2c 262 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 261) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_261
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 262 - ((28087/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_262).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_263 : ((317263/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 263, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 263, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 262, cos618o2c k) + cos618o2c 263 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 262) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_262
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 263 - ((979501/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_263).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_264 : ((1683287/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 264, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 264, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 263, cos618o2c k) + cos618o2c 264 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 263) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_263
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 264 - ((48511/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_264).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_265 : ((1269961/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 265, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 265, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 264, cos618o2c k) + cos618o2c 265 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 264) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_264
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 265 - ((-103319/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_265).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_266 : ((423943/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 266, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 266, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 265, cos618o2c k) + cos618o2c 266 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 265) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_265
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 266 - ((-16881/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_266).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_267 : ((924863/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 267, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 267, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 266, cos618o2c k) + cos618o2c 267 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 266) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_266
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 267 - ((77027/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_267).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_268 : ((35197/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 268, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 268, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 267, cos618o2c k) + cos618o2c 268 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 267) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_267
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 268 - ((483067/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_268).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_269 : ((344519/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 269, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 269, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 268, cos618o2c k) + cos618o2c 269 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 268) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_268
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 269 - ((62953/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_269).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_270 : ((2996107/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 270, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 270, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 269, cos618o2c k) + cos618o2c 270 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 269) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_269
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 270 - ((-448983/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_270).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_271 : ((998349/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 271, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 271, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 270, cos618o2c k) + cos618o2c 271 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 270) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_270
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 271 - ((-999309/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_271).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_272 : ((322263/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 272, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 272, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 271, cos618o2c k) + cos618o2c 272 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 271) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_271
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 272 - ((-385283/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_272).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_273 : ((2284337/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 273, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 273, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 272, cos618o2c k) + cos618o2c 273 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 272) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_272
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 273 - ((336561/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_273).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_274 : ((3240323/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 274, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 274, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 273, cos618o2c k) + cos618o2c 274 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 273) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_273
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 274 - ((478043/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_274).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_275 : ((3387373/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 275, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 275, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 274, cos618o2c k) + cos618o2c 275 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 274) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_274
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 275 - ((2943/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_275).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_276 : ((2560177/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 276, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 276, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 275, cos618o2c k) + cos618o2c 276 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 275) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_275
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 276 - ((-103387/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_276).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_277 : ((1692599/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 277, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 277, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 276, cos618o2c k) + cos618o2c 277 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 276) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_276
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 277 - ((-433739/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_277).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_278 : ((877929/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 278, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 278, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 277, cos618o2c k) + cos618o2c 278 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 277) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_277
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 278 - ((63359/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_278).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_279 : ((535527/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 279, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 279, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 278, cos618o2c k) + cos618o2c 279 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 278) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_278
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 279 - ((921877/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_279).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_280 : ((3437413/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 280, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 280, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 279, cos618o2c k) + cos618o2c 280 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 279) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_279
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 280 - ((379939/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_280).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_281 : ((1600553/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 281, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 281, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 280, cos618o2c k) + cos618o2c 281 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 280) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_280
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 281 - ((-236207/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_281).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_282 : ((2228409/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 282, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 282, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 281, cos618o2c k) + cos618o2c 282 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 281) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_281
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 282 - ((-972597/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_282).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_283 : ((1575231/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 283, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 283, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 282, cos618o2c k) + cos618o2c 283 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 282) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_282
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 283 - ((-326539/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_283).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_284 : ((388899/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 284, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 284, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 283, cos618o2c k) + cos618o2c 284 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 283) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_283
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 284 - ((92341/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_284).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_285 : ((2938743/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 285, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 285, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 284, cos618o2c k) + cos618o2c 285 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 284) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_284
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 285 - ((248587/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_285).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_286 : ((3499011/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 286, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 286, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 285, cos618o2c k) + cos618o2c 286 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 285) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_285
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 286 - ((35023/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_286).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_287 : ((60677/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 287, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 287, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 286, cos618o2c k) + cos618o2c 287 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 286) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_286
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 287 - ((-465061/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_287).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_288 : ((1016913/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 288, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 288, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 287, cos618o2c k) + cos618o2c 288 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 287) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_287
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 288 - ((-249981/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_288).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_289 : ((24121/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 289, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 289, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 288, cos618o2c k) + cos618o2c 289 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 288) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_288
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 289 - ((-244991/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_289).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_290 : ((41417/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 290, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 290, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 289, cos618o2c k) + cos618o2c 290 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 289) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_289
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 290 - ((263603/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_290).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_291 : ((3069589/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 291, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 291, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 290, cos618o2c k) + cos618o2c 291 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 290) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_290
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 291 - ((998839/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_291).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_292 : ((3515727/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 292, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 292, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 291, cos618o2c k) + cos618o2c 292 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 291) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_291
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 292 - ((223119/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_292).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_293 : ((295607/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 293, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 293, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 292, cos618o2c k) + cos618o2c 293 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 292) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_292
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 293 - ((-559557/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_293).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_294 : ((391769/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 294, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 294, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 293, cos618o2c k) + cos618o2c 294 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 293) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_293
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 294 - ((-7977/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_294).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_295 : ((30553/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 295, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 295, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 294, cos618o2c k) + cos618o2c 295 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 294) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_294
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 295 - ((-86219/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_295).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_296 : ((130761/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 296, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 296, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 295, cos618o2c k) + cos618o2c 296 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 295) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_295
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 296 - ((282313/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_296).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_297 : ((772383/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 297, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 297, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 296, cos618o2c k) + cos618o2c 297 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 296) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_296
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 297 - ((62341/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_297).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_298 : ((1767051/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 298, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 298, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 297, cos618o2c k) + cos618o2c 298 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 297) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_297
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 298 - ((44467/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_298).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_299 : ((747673/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 299, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 299, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 298, cos618o2c k) + cos618o2c 299 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 298) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_298
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 299 - ((-54331/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_299).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_300 : ((398243/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 300, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 300, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 299, cos618o2c k) + cos618o2c 300 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 299) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_299
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 300 - ((-999377/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_300).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_301 : ((1505377/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 301, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 301, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 300, cos618o2c k) + cos618o2c 301 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 300) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_300
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 301 - ((-242869/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_301).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_302 : ((1000073/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 302, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 302, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 301, cos618o2c k) + cos618o2c 302 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 301) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_301
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 302 - ((494869/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_302).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_303 : ((1499773/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 303, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 303, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 302, cos618o2c k) + cos618o2c 303 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 302) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_302
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 303 - ((1999/2000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_303).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_304 : ((221941/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 304, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 304, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 303, cos618o2c k) + cos618o2c 304 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 303) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_303
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 304 - ((55161/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_304).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_305 : ((97927/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 305, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 305, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 304, cos618o2c k) + cos618o2c 305 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 304) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_304
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 305 - ((-104323/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_305).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_306 : ((1070927/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 306, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 306, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 305, cos618o2c k) + cos618o2c 306 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 305) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_305
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 306 - ((-99171/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_306).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_307 : ((188007/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 307, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 307, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 306, cos618o2c k) + cos618o2c 307 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 306) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_306
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 307 - ((-318849/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_307).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_308 : ((362443/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 308, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 308, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 307, cos618o2c k) + cos618o2c 308 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 307) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_307
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 308 - ((308259/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_308).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_309 : ((1389787/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 309, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 309, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 308, cos618o2c k) + cos618o2c 309 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 308) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_308
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 309 - ((967459/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_309).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_310 : ((219763/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 310, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 310, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 309, cos618o2c k) + cos618o2c 310 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 309) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_309
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 310 - ((368367/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_310).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_311 : ((1674957/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 311, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 311, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 310, cos618o2c k) + cos618o2c 311 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 310) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_310
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 311 - ((-83097/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_311).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_312 : ((2433443/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 312, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 312, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 311, cos618o2c k) + cos618o2c 312 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 311) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_311
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 312 - ((-916371/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_312).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_313 : ((1595199/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 313, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 313, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 312, cos618o2c k) + cos618o2c 313 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 312) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_312
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 313 - ((-13096/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_313).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_314 : ((2539/1600 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 314, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 314, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 313, cos618o2c k) + cos618o2c 314 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 313) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_313
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 314 - ((-257/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_314).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_315 : ((1207043/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 315, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 315, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 314, cos618o2c k) + cos618o2c 315 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 314) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_314
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 315 - ((827311/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_315).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_316 : ((1670783/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 316, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 316, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 315, cos618o2c k) + cos618o2c 316 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 315) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_315
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 316 - ((46379/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_316).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_317 : ((55492/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 317, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 317, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 316, cos618o2c k) + cos618o2c 317 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 316) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_316
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 317 - ((105011/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_317).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_318 : ((2861287/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 318, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 318, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 317, cos618o2c k) + cos618o2c 318 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 317) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_317
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 318 - ((-690101/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_318).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_319 : ((468531/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 319, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 319, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 318, cos618o2c k) + cos618o2c 319 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 318) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_318
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 319 - ((-987063/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_319).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_320 : ((722841/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 320, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 320, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 319, cos618o2c k) + cos618o2c 320 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 319) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_319
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 320 - ((-214171/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_320).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_321 : ((311/160 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 321, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 321, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 320, cos618o2c k) + cos618o2c 321 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 320) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_320
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 321 - ((62271/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_321).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_322 : ((2939763/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 322, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 322, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 321, cos618o2c k) + cos618o2c 322 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 321) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_321
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 322 - ((996113/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_322).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_323 : ((3584529/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 323, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 323, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 322, cos618o2c k) + cos618o2c 323 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 322) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_322
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 323 - ((322433/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_323).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_324 : ((3332829/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 324, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 324, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 323, cos618o2c k) + cos618o2c 324 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 323) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_323
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 324 - ((-629/2500 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_324).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_325 : ((2398337/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 325, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 325, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 324, cos618o2c k) + cos618o2c 325 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 324) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_324
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 325 - ((-116799/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_325).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_326 : ((1564559/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 326, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 326, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 325, cos618o2c k) + cos618o2c 326 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 325) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_325
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 326 - ((-416839/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_326).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_327 : ((1525139/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 327, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 327, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 326, cos618o2c k) + cos618o2c 327 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 326) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_326
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 327 - ((-983/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_327).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_328 : ((2310971/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 328, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 328, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 327, cos618o2c k) + cos618o2c 328 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 327) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_327
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 328 - ((196483/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_328).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_329 : ((1636779/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 329, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 329, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 328, cos618o2c k) + cos618o2c 329 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 328) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_328
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 329 - ((962687/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_329).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_330 : ((3624777/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 330, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 330, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 329, cos618o2c k) + cos618o2c 330 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 329) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_329
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 330 - ((351319/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_330).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_331 : ((770009/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 331, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 331, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 330, cos618o2c k) + cos618o2c 331 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 330) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_330
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 331 - ((-544641/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_331).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_332 : ((2081901/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 332, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 332, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 331, cos618o2c k) + cos618o2c 332 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 331) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_331
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 332 - ((-199607/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_332).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_333 : ((1434389/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 333, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 333, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 332, cos618o2c k) + cos618o2c 333 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 332) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_332
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 333 - ((-161853/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_333).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_334 : ((1654813/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 334, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 334, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 333, cos618o2c k) + cos618o2c 334 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 333) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_333
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 334 - ((55131/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_334).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_335 : ((2565893/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 335, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 335, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 334, cos618o2c k) + cos618o2c 335 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 334) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_334
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 335 - ((45559/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_335).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_336 : ((3445121/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 336, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 336, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 335, cos618o2c k) + cos618o2c 336 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 335) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_335
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 336 - ((27479/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_336).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_337 : ((72011/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 337, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 337, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 336, cos618o2c k) + cos618o2c 337 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 336) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_336
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 337 - ((155529/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_337).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_338 : ((2911983/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 338, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 338, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 337, cos618o2c k) + cos618o2c 338 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 337) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_337
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 338 - ((-688467/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_338).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_339 : ((76681/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 339, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 339, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 338, cos618o2c k) + cos618o2c 339 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 338) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_338
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 339 - ((-497429/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_339).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_340 : ((1386433/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 340, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 340, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 339, cos618o2c k) + cos618o2c 340 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 339) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_339
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 340 - ((-132623/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_340).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_341 : ((215953/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 341, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 341, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 340, cos618o2c k) + cos618o2c 341 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 340) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_340
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 341 - ((341291/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_341).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_342 : ((669373/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 342, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 342, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 341, cos618o2c k) + cos618o2c 342 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 341) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_341
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 342 - ((59373/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_342).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_343 : ((1755683/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 343, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 343, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 342, cos618o2c k) + cos618o2c 343 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 342) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_342
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 343 - ((416987/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_343).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_344 : ((3597867/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 344, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 344, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 343, cos618o2c k) + cos618o2c 344 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 343) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_343
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 344 - ((86601/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_344).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_345 : ((359163/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 345, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 345, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 344, cos618o2c k) + cos618o2c 345 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 344) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_344
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 345 - ((-724463/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_345).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_346 : ((941071/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 346, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 346, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 345, cos618o2c k) + cos618o2c 346 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 345) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_345
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 346 - ((-495531/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_346).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_347 : ((170429/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 347, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 347, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 346, cos618o2c k) + cos618o2c 347 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 346) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_346
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 347 - ((-51861/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_347).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_348 : ((1700573/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 348, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 348, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 347, cos618o2c k) + cos618o2c 348 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 347) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_347
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 348 - ((337241/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_348).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_349 : ((1321591/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 349, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 349, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 348, cos618o2c k) + cos618o2c 349 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 348) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_348
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 349 - ((942709/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_349).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_350 : ((174937/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 350, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 350, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 349, cos618o2c k) + cos618o2c 350 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 349) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_349
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 350 - ((427829/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_350).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_351 : ((227709/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 351, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 351, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 350, cos618o2c k) + cos618o2c 351 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 350) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_350
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 351 - ((2261/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_351).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_352 : ((2973503/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 352, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 352, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 351, cos618o2c k) + cos618o2c 352 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 351) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_351
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 352 - ((-669741/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_352).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_353 : ((197419/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 353, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 353, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 352, cos618o2c k) + cos618o2c 353 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 352) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_352
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 353 - ((-999213/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_353).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_354 : ((681673/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 354, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 354, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 353, cos618o2c k) + cos618o2c 354 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 353) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_353
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 354 - ((-76343/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_354).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_355 : ((1576229/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 355, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 355, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 354, cos618o2c k) + cos618o2c 355 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 354) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_354
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 355 - ((212983/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_355).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_356 : ((614973/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 356, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 356, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 355, cos618o2c k) + cos618o2c 356 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 355) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_355
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 356 - ((883763/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_356).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_357 : ((3388533/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 357, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 357, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 356, cos618o2c k) + cos618o2c 357 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 356) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_356
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 357 - ((928741/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_357).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_358 : ((3709323/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 358, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 358, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 357, cos618o2c k) + cos618o2c 358 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 357) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_357
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 358 - ((32089/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_358).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_359 : ((1599581/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 359, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 359, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 358, cos618o2c k) + cos618o2c 359 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 358) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_358
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 359 - ((-510061/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_359).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_360 : ((2214509/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 360, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 360, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 359, cos618o2c k) + cos618o2c 360 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 359) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_359
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 360 - ((-984553/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_360).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_361 : ((718777/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 361, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 361, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 360, cos618o2c k) + cos618o2c 361 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 360) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_360
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 361 - ((-155371/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_361).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_362 : ((1402591/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 362, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 362, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 361, cos618o2c k) + cos618o2c 362 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 361) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_361
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 362 - ((-34863/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_362).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_363 : ((426391/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 363, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 363, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 362, cos618o2c k) + cos618o2c 363 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 362) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_362
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 363 - ((91183/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_363).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_364 : ((3127173/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 364, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 364, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 363, cos618o2c k) + cos618o2c 364 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 363) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_363
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 364 - ((497659/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_364).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_365 : ((3713187/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 365, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 365, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 364, cos618o2c k) + cos618o2c 365 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 364) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_364
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 365 - ((293057/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_365).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_366 : ((873917/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 366, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 366, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 365, cos618o2c k) + cos618o2c 366 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 365) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_365
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 366 - ((-217419/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_366).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_367 : ((1311051/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 367, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 367, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 366, cos618o2c k) + cos618o2c 367 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 366) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_366
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 367 - ((-436733/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_367).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_368 : ((1676707/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 368, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 368, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 367, cos618o2c k) + cos618o2c 368 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 367) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_367
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 368 - ((-189059/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_368).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_369 : ((643611/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 369, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 369, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 368, cos618o2c k) + cos618o2c 369 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 368) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_368
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 369 - ((-77877/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_369).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_370 : ((427431/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 370, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 370, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 369, cos618o2c k) + cos618o2c 370 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 369) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_369
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 370 - ((211301/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_370).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_371 : ((532963/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 371, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 371, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 370, cos618o2c k) + cos618o2c 371 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 370) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_370
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 371 - ((955191/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_371).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_372 : ((3526877/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 372, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 372, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 371, cos618o2c k) + cos618o2c 372 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 371) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_371
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 372 - ((431081/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_372).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_373 : ((3735217/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 373, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 373, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 372, cos618o2c k) + cos618o2c 373 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 372) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_372
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 373 - ((5211/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_373).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_374 : ((789069/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 374, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 374, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 373, cos618o2c k) + cos618o2c 374 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 373) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_373
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 374 - ((-578841/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_374).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_375 : ((541101/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 375, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 375, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 374, cos618o2c k) + cos618o2c 375 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 374) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_374
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 375 - ((-247943/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_375).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_376 : ((27919/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 376, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 376, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 375, cos618o2c k) + cos618o2c 376 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 375) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_375
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 376 - ((-384177/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_376).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_377 : ((1340317/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 377, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 377, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 376, cos618o2c k) + cos618o2c 377 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 376) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_376
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 377 - ((-55533/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_377).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_378 : ((406259/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 378, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 378, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 377, cos618o2c k) + cos618o2c 378 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 377) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_377
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 378 - ((345539/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_378).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_379 : ((1515579/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 379, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 379, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 378, cos618o2c k) + cos618o2c 379 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 378) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_378
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 379 - ((999963/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_379).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_380 : ((148449/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 380, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 380, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 379, cos618o2c k) + cos618o2c 380 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 379) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_379
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 380 - ((680167/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_380).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_381 : ((911769/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 381, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 381, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 380, cos618o2c k) + cos618o2c 381 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 380) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_380
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 381 - ((-64049/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_381).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_382 : ((1440013/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 382, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 382, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 381, cos618o2c k) + cos618o2c 382 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 381) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_381
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 382 - ((-15339/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_382).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_383 : ((1886091/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 383, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 383, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 382, cos618o2c k) + cos618o2c 383 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 382) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_382
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 383 - ((-198767/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_383).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_384 : ((39927/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 384, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 384, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 383, cos618o2c k) + cos618o2c 384 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 383) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_383
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 384 - ((-608327/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_384).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_385 : ((713351/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 385, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 385, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 384, cos618o2c k) + cos618o2c 385 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 384) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_384
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 385 - ((74569/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_385).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_386 : ((112037/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 386, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 386, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 385, cos618o2c k) + cos618o2c 386 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 385) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_385
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 386 - ((407069/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_386).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_387 : ((1612249/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 387, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 387, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 386, cos618o2c k) + cos618o2c 387 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 386) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_386
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 387 - ((491929/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_387).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_388 : ((3783613/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 388, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 388, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 387, cos618o2c k) + cos618o2c 388 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 387) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_387
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 388 - ((111843/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_388).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_389 : ((716591/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 389, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 389, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 388, cos618o2c k) + cos618o2c 389 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 388) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_388
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 389 - ((-100279/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_389).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_390 : ((2743957/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 390, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 390, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 389, cos618o2c k) + cos618o2c 390 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 389) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_389
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 390 - ((-419449/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_390).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_391 : ((5522/3125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 391, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 391, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 390, cos618o2c k) + cos618o2c 391 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 390) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_390
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 391 - ((-976817/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_391).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_392 : ((153859/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 392, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 392, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 391, cos618o2c k) + cos618o2c 392 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 391) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_391
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 392 - ((-134017/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_392).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_393 : ((1450463/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 393, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 393, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 392, cos618o2c k) + cos618o2c 393 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 392) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_392
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 393 - ((219691/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_393).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_394 : ((2295467/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 394, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 394, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 393, cos618o2c k) + cos618o2c 394 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 393) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_393
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 394 - ((52819/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_394).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_395 : ((654287/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 395, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 395, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 394, cos618o2c k) + cos618o2c 395 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 394) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_394
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 395 - ((244017/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_395).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_396 : ((3811197/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 396, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 396, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 395, cos618o2c k) + cos618o2c 396 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 395) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_395
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 396 - ((269931/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_396).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_397 : ((3603591/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 397, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 397, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 396, cos618o2c k) + cos618o2c 397 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 396) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_396
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 397 - ((-103753/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_397).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_398 : ((1384721/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 398, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 398, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 397, cos618o2c k) + cos618o2c 398 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 397) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_397
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 398 - ((-834049/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_398).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_399 : ((178753/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 399, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 399, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 398, cos618o2c k) + cos618o2c 399 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 398) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_398
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 399 - ((-245453/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_399).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_400 : ((60879/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 400, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 400, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 399, cos618o2c k) + cos618o2c 400 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 399) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_399
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 400 - ((-11397/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_400).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_401 : ((345487/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 401, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 401, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 400, cos618o2c k) + cos618o2c 401 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 400) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_400
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 401 - ((41117/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_401).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_402 : ((2186337/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 402, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 402, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 401, cos618o2c k) + cos618o2c 402 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 401) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_401
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 402 - ((804489/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_402).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_403 : ((3177573/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 403, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 403, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 402, cos618o2c k) + cos618o2c 403 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 402) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_402
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 403 - ((123917/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_403).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_404 : ((3801021/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 404, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 404, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 403, cos618o2c k) + cos618o2c 404 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 403) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_403
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 404 - ((155887/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_404).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_405 : ((3710409/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 405, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 405, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 404, cos618o2c k) + cos618o2c 405 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 404) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_404
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 405 - ((-5657/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_405).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_406 : ((118291/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 406, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 406, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 405, cos618o2c k) + cos618o2c 406 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 405) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_405
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 406 - ((-376517/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_406).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_407 : ((1958057/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 407, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 407, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 406, cos618o2c k) + cos618o2c 407 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 406) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_406
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 407 - ((-499559/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_407).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_408 : ((1261459/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 408, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 408, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 407, cos618o2c k) + cos618o2c 408 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 407) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_407
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 408 - ((-348249/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_408).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_409 : ((623643/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 409, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 409, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 408, cos618o2c k) + cos618o2c 409 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 408) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_408
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 409 - ((-14073/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_409).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_410 : ((1921847/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 410, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 410, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 409, cos618o2c k) + cos618o2c 410 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 409) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_409
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 410 - ((674661/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_410).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_411 : ((2918743/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 411, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 411, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 410, cos618o2c k) + cos618o2c 411 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 410) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_410
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 411 - ((249249/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_411).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_412 : ((3700371/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 412, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 412, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 411, cos618o2c k) + cos618o2c 412 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 411) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_411
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 412 - ((24429/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_412).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_413 : ((1924041/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 413, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 413, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 412, cos618o2c k) + cos618o2c 413 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 412) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_412
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 413 - ((147811/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_413).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_414 : ((1642111/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 414, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 414, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 413, cos618o2c k) + cos618o2c 414 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 413) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_413
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 414 - ((-7047/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_414).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_415 : ((461927/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 415, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 415, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 414, cos618o2c k) + cos618o2c 415 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 414) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_414
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 415 - ((-974487/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_415).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_416 : ((1440377/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 416, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 416, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 415, cos618o2c k) + cos618o2c 416 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 415) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_415
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 416 - ((-434579/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_416).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_417 : ((566853/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 417, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 417, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 416, cos618o2c k) + cos618o2c 417 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 416) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_416
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 417 - ((-306571/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_417).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_418 : ((1549139/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 418, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 418, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 417, cos618o2c k) + cos618o2c 418 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 417) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_417
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 418 - ((415533/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_418).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_419 : ((2468569/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 419, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 419, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 418, cos618o2c k) + cos618o2c 419 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 418) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_418
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 419 - ((91953/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_419).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_420 : ((3413639/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 420, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 420, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 419, cos618o2c k) + cos618o2c 420 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 419) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_419
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 420 - ((94517/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_420).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_421 : ((1947921/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 421, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 421, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 420, cos618o2c k) + cos618o2c 421 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 420) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_420
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 421 - ((482303/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_421).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_422 : ((3667939/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 422, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 422, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 421, cos618o2c k) + cos618o2c 422 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 421) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_421
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 422 - ((-227803/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_422).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_423 : ((1423991/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 423, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 423, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 422, cos618o2c k) + cos618o2c 423 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 422) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_422
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 423 - ((-819857/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_423).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_424 : ((927537/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 424, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 424, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 423, cos618o2c k) + cos618o2c 424 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 423) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_423
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 424 - ((-124101/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_424).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_425 : ((1193429/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 425, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 425, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 424, cos618o2c k) + cos618o2c 425 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 424) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_424
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 425 - ((-132309/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_425).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_426 : ((1196663/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 426, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 426, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 425, cos618o2c k) + cos618o2c 426 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 425) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_425
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 426 - ((1667/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_426).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_427 : ((930913/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 427, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 427, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 426, cos618o2c k) + cos618o2c 427 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 426) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_426
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 427 - ((665263/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_427).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_428 : ((570903/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 428, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 428, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 427, cos618o2c k) + cos618o2c 428 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 427) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_427
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 428 - ((992789/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_428).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_429 : ((3679199/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 429, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 429, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 428, cos618o2c k) + cos618o2c 429 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 428) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_428
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 429 - ((51549/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_429).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_430 : ((3926867/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 430, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 430, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 429, cos618o2c k) + cos618o2c 430 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 429) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_429
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 430 - ((30971/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_430).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_431 : ((3476227/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 431, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 431, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 430, cos618o2c k) + cos618o2c 431 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 430) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_430
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 431 - ((-22527/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_431).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_432 : ((1275101/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 432, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 432, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 431, cos618o2c k) + cos618o2c 432 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 431) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_431
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 432 - ((-37037/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_432).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_433 : ((80157/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 433, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 433, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 432, cos618o2c k) + cos618o2c 433 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 432) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_432
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 433 - ((-473481/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_433).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_434 : ((548389/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 434, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 434, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 433, cos618o2c k) + cos618o2c 434 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 433) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_433
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 434 - ((-253131/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_434).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_435 : ((638011/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 435, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 435, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 434, cos618o2c k) + cos618o2c 435 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 434) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_434
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 435 - ((11209/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_435).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_436 : ((64153/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 436, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 436, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 435, cos618o2c k) + cos618o2c 436 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 435) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_435
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 436 - ((388487/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_436).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_437 : ((3052433/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 437, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 437, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 436, cos618o2c k) + cos618o2c 437 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 436) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_436
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 437 - ((999637/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_437).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_438 : ((3795337/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 438, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 438, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 437, cos618o2c k) + cos618o2c 438 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 437) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_437
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 438 - ((185751/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_438).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_439 : ((3927719/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 439, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 439, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 438, cos618o2c k) + cos618o2c 439 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 438) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_438
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 439 - ((66241/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_439).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_440 : ((3387823/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 440, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 440, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 439, cos618o2c k) + cos618o2c 440 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 439) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_439
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 440 - ((-134949/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_440).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_441 : ((2432133/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 441, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 441, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 440, cos618o2c k) + cos618o2c 441 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 440) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_440
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 441 - ((-95559/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_441).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_442 : ((755631/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 442, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 442, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 441, cos618o2c k) + cos618o2c 442 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 441) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_441
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 442 - ((-920771/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_442).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_443 : ((528361/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 443, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 443, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 442, cos618o2c k) + cos618o2c 443 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 442) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_442
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 443 - ((-11361/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_443).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_444 : ((1279719/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 444, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 444, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 443, cos618o2c k) + cos618o2c 444 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 443) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_443
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 444 - ((223097/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_444).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_445 : ((207531/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 445, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 445, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 444, cos618o2c k) + cos618o2c 445 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 444) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_444
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 445 - ((795691/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_445).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_446 : ((3074287/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 446, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 446, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 445, cos618o2c k) + cos618o2c 446 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 445) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_445
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 446 - ((999077/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_446).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_447 : ((1908009/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 447, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 447, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 446, cos618o2c k) + cos618o2c 447 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 446) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_446
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 447 - ((741831/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_447).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_448 : ((1980341/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 448, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 448, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 447, cos618o2c k) + cos618o2c 448 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 447) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_447
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 448 - ((36191/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_448).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_449 : ((34433/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 449, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 449, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 448, cos618o2c k) + cos618o2c 449 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 448) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_448
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 449 - ((-258641/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_449).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_450 : ((2500343/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 450, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 450, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 449, cos618o2c k) + cos618o2c 450 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 449) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_449
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 450 - ((-942857/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_450).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_451 : ((1559583/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 451, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 451, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 450, cos618o2c k) + cos618o2c 451 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 450) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_450
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 451 - ((-47033/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_451).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_452 : ((522589/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 452, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 452, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 451, cos618o2c k) + cos618o2c 452 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 451) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_451
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 452 - ((-102861/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_452).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_453 : ((1187287/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 453, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 453, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 452, cos618o2c k) + cos618o2c 453 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 452) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_452
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 453 - ((142209/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_453).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_454 : ((960541/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 454, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 454, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 453, cos618o2c k) + cos618o2c 454 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 453) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_453
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 454 - ((146779/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_454).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_455 : ((2918747/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 455, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 455, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 454, cos618o2c k) + cos618o2c 455 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 454) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_454
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 455 - ((199553/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_455).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_456 : ((3737427/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 456, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 456, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 455, cos618o2c k) + cos618o2c 456 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 455) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_455
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 456 - ((40939/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_456).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_457 : ((2008003/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 457, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 457, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 456, cos618o2c k) + cos618o2c 457 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 456) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_456
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 457 - ((278679/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_457).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_458 : ((72659/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 458, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 458, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 457, cos618o2c k) + cos618o2c 458 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 457) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_457
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 458 - ((-95739/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_458).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_459 : ((689279/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 459, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 459, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 458, cos618o2c k) + cos618o2c 459 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 458) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_458
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 459 - ((-437867/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_459).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_460 : ((442799/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 460, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 460, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 459, cos618o2c k) + cos618o2c 460 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 459) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_459
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 460 - ((-49291/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_460).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_461 : ((275839/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 461, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 461, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 460, cos618o2c k) + cos618o2c 461 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 460) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_460
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 461 - ((-33387/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_461).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_462 : ((1041667/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 462, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 462, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 461, cos618o2c k) + cos618o2c 462 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 461) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_461
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 462 - ((-61589/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_462).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_463 : ((402889/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 463, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 463, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 462, cos618o2c k) + cos618o2c 463 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 462) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_462
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 463 - ((569989/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_463).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_464 : ((40117/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 464, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 464, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 463, cos618o2c k) + cos618o2c 464 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 463) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_463
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 464 - ((14938/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_464).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_465 : ((3500577/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 465, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 465, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 464, cos618o2c k) + cos618o2c 465 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 464) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_464
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 465 - ((933189/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_465).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_466 : ((1003523/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 466, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 466, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 465, cos618o2c k) + cos618o2c 466 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 465) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_465
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 466 - ((102723/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_466).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_467 : ((1945661/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 467, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 467, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 466, cos618o2c k) + cos618o2c 467 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 466) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_466
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 467 - ((-12267/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_467).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_468 : ((1592577/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 468, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 468, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 467, cos618o2c k) + cos618o2c 468 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 467) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_467
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 468 - ((-176517/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_468).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_469 : ((1096573/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 469, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 469, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 468, cos618o2c k) + cos618o2c 469 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 468) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_468
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 469 - ((-247977/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_469).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_470 : ((1330661/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 470, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 470, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 469, cos618o2c k) + cos618o2c 470 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 469) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_469
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 470 - ((-172477/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_470).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_471 : ((956657/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 471, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 471, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 470, cos618o2c k) + cos618o2c 471 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 470) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_470
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 471 - ((-23369/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_471).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_472 : ((612677/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 472, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 472, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 471, cos618o2c k) + cos618o2c 472 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 471) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_471
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 472 - ((268797/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_472).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_473 : ((2024543/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 473, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 473, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 472, cos618o2c k) + cos618o2c 473 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 472) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_472
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 473 - ((799289/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_473).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_474 : ((756103/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 474, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 474, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 473, cos618o2c k) + cos618o2c 474 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 473) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_473
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 474 - ((999969/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_474).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_475 : ((3814831/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 475, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 475, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 474, cos618o2c k) + cos618o2c 475 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 474) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_474
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 475 - ((790519/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_475).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_476 : ((2036789/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 476, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 476, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 475, cos618o2c k) + cos618o2c 476 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 475) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_475
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 476 - ((258847/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_476).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_477 : ((3696401/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 477, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 477, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 476, cos618o2c k) + cos618o2c 477 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 476) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_476
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 477 - ((-377077/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_477).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_478 : ((354633/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 478, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 478, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 477, cos618o2c k) + cos618o2c 478 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 477) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_477
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 478 - ((-859237/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_478).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_479 : ((1842869/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 479, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 479, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 478, cos618o2c k) + cos618o2c 479 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 478) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_478
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 479 - ((-198819/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_479).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_480 : ((1113251/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 480, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 480, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 479, cos618o2c k) + cos618o2c 480 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 479) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_479
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 480 - ((-364759/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_480).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_481 : ((939479/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 481, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 481, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 480, cos618o2c k) + cos618o2c 481 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 480) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_480
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 481 - ((-21709/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_481).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_482 : ((347443/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 482, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 482, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 481, cos618o2c k) + cos618o2c 482 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 481) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_481
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 482 - ((450393/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_482).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_483 : ((142769/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 483, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 483, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 482, cos618o2c k) + cos618o2c 483 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 482) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_482
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 483 - ((111829/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_483).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_484 : ((3268771/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 484, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 484, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 483, cos618o2c k) + cos618o2c 484 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 483) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_483
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 484 - ((984567/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_484).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_485 : ((3955513/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 485, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 485, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 484, cos618o2c k) + cos618o2c 485 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 484) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_484
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 485 - ((343421/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_485).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_486 : ((4075777/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 486, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 486, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 485, cos618o2c k) + cos618o2c 486 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 485) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_485
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 486 - ((30091/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_486).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_487 : ((111987/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 487, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 487, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 486, cos618o2c k) + cos618o2c 487 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 486) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_486
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 487 - ((-492093/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_487).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_488 : ((1335699/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 488, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 488, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 487, cos618o2c k) + cos618o2c 488 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 487) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_487
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 488 - ((-456043/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_488).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_489 : ((846641/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 489, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 489, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 488, cos618o2c k) + cos618o2c 489 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 488) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_488
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 489 - ((-30563/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_489).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_490 : ((256677/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 490, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 490, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 489, cos618o2c k) + cos618o2c 490 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 489) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_489
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 490 - ((-333237/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_490).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_491 : ((231823/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 491, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 491, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 490, cos618o2c k) + cos618o2c 491 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 490) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_490
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 491 - ((-24829/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_491).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_492 : ((286409/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 492, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 492, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 491, cos618o2c k) + cos618o2c 492 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 491) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_491
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 492 - ((504853/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_492).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_493 : ((2347387/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 493, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 493, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 492, cos618o2c k) + cos618o2c 493 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 492) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_492
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 493 - ((457721/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_493).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_494 : ((1662453/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 494, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 494, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 493, cos618o2c k) + cos618o2c 494 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 493) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_493
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 494 - ((977619/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_494).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_495 : ((3994629/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 495, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 495, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 494, cos618o2c k) + cos618o2c 495 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 494) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_494
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 495 - ((669823/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_495).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_496 : ((1026163/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 496, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 496, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 495, cos618o2c k) + cos618o2c 496 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 495) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_495
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 496 - ((110123/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_496).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_497 : ((3614621/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 497, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 497, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 496, cos618o2c k) + cos618o2c 497 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 496) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_496
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 497 - ((-489931/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_497).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_498 : ((270879/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 498, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 498, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 497, cos618o2c k) + cos618o2c 498 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 497) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_497
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 498 - ((-905731/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_498).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_499 : ((345047/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 499, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 499, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 498, cos618o2c k) + cos618o2c 499 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 498) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_498
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 499 - ((-196691/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_499).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum618o2_500 : ((205797/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 500, cos618o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 500, cos618o2c k)
      = (∑ k ∈ Finset.Icc 11 499, cos618o2c k) + cos618o2c 500 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 499) (by norm_num) cos618o2c
    simpa using h
  have hprev := psum618o2_499
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos618o2c 500 - ((-13923/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos618o2_br_500).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 16384 in
theorem psum618o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 500 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos618o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum618o2_11
  · exact le_trans (by norm_num) psum618o2_12
  · exact le_trans (by norm_num) psum618o2_13
  · exact le_trans (by norm_num) psum618o2_14
  · exact le_trans (by norm_num) psum618o2_15
  · exact le_trans (by norm_num) psum618o2_16
  · exact le_trans (by norm_num) psum618o2_17
  · exact le_trans (by norm_num) psum618o2_18
  · exact le_trans (by norm_num) psum618o2_19
  · exact le_trans (by norm_num) psum618o2_20
  · exact le_trans (by norm_num) psum618o2_21
  · exact le_trans (by norm_num) psum618o2_22
  · exact le_trans (by norm_num) psum618o2_23
  · exact le_trans (by norm_num) psum618o2_24
  · exact le_trans (by norm_num) psum618o2_25
  · exact le_trans (by norm_num) psum618o2_26
  · exact le_trans (by norm_num) psum618o2_27
  · exact le_trans (by norm_num) psum618o2_28
  · exact le_trans (by norm_num) psum618o2_29
  · exact le_trans (by norm_num) psum618o2_30
  · exact le_trans (by norm_num) psum618o2_31
  · exact le_trans (by norm_num) psum618o2_32
  · exact le_trans (by norm_num) psum618o2_33
  · exact le_trans (by norm_num) psum618o2_34
  · exact le_trans (by norm_num) psum618o2_35
  · exact le_trans (by norm_num) psum618o2_36
  · exact le_trans (by norm_num) psum618o2_37
  · exact le_trans (by norm_num) psum618o2_38
  · exact le_trans (by norm_num) psum618o2_39
  · exact le_trans (by norm_num) psum618o2_40
  · exact le_trans (by norm_num) psum618o2_41
  · exact le_trans (by norm_num) psum618o2_42
  · exact le_trans (by norm_num) psum618o2_43
  · exact le_trans (by norm_num) psum618o2_44
  · exact le_trans (by norm_num) psum618o2_45
  · exact le_trans (by norm_num) psum618o2_46
  · exact le_trans (by norm_num) psum618o2_47
  · exact le_trans (by norm_num) psum618o2_48
  · exact le_trans (by norm_num) psum618o2_49
  · exact le_trans (by norm_num) psum618o2_50
  · exact le_trans (by norm_num) psum618o2_51
  · exact le_trans (by norm_num) psum618o2_52
  · exact le_trans (by norm_num) psum618o2_53
  · exact le_trans (by norm_num) psum618o2_54
  · exact le_trans (by norm_num) psum618o2_55
  · exact le_trans (by norm_num) psum618o2_56
  · exact le_trans (by norm_num) psum618o2_57
  · exact le_trans (by norm_num) psum618o2_58
  · exact le_trans (by norm_num) psum618o2_59
  · exact le_trans (by norm_num) psum618o2_60
  · exact le_trans (by norm_num) psum618o2_61
  · exact le_trans (by norm_num) psum618o2_62
  · exact le_trans (by norm_num) psum618o2_63
  · exact le_trans (by norm_num) psum618o2_64
  · exact le_trans (by norm_num) psum618o2_65
  · exact le_trans (by norm_num) psum618o2_66
  · exact le_trans (by norm_num) psum618o2_67
  · exact le_trans (by norm_num) psum618o2_68
  · exact le_trans (by norm_num) psum618o2_69
  · exact le_trans (by norm_num) psum618o2_70
  · exact le_trans (by norm_num) psum618o2_71
  · exact le_trans (by norm_num) psum618o2_72
  · exact le_trans (by norm_num) psum618o2_73
  · exact le_trans (by norm_num) psum618o2_74
  · exact le_trans (by norm_num) psum618o2_75
  · exact le_trans (by norm_num) psum618o2_76
  · exact le_trans (by norm_num) psum618o2_77
  · exact le_trans (by norm_num) psum618o2_78
  · exact le_trans (by norm_num) psum618o2_79
  · exact le_trans (by norm_num) psum618o2_80
  · exact le_trans (by norm_num) psum618o2_81
  · exact le_trans (by norm_num) psum618o2_82
  · exact le_trans (by norm_num) psum618o2_83
  · exact le_trans (by norm_num) psum618o2_84
  · exact le_trans (by norm_num) psum618o2_85
  · exact le_trans (by norm_num) psum618o2_86
  · exact le_trans (by norm_num) psum618o2_87
  · exact le_trans (by norm_num) psum618o2_88
  · exact le_trans (by norm_num) psum618o2_89
  · exact le_trans (by norm_num) psum618o2_90
  · exact le_trans (by norm_num) psum618o2_91
  · exact le_trans (by norm_num) psum618o2_92
  · exact le_trans (by norm_num) psum618o2_93
  · exact le_trans (by norm_num) psum618o2_94
  · exact le_trans (by norm_num) psum618o2_95
  · exact le_trans (by norm_num) psum618o2_96
  · exact le_trans (by norm_num) psum618o2_97
  · exact le_trans (by norm_num) psum618o2_98
  · exact le_trans (by norm_num) psum618o2_99
  · exact le_trans (by norm_num) psum618o2_100
  · exact le_trans (by norm_num) psum618o2_101
  · exact le_trans (by norm_num) psum618o2_102
  · exact le_trans (by norm_num) psum618o2_103
  · exact le_trans (by norm_num) psum618o2_104
  · exact le_trans (by norm_num) psum618o2_105
  · exact le_trans (by norm_num) psum618o2_106
  · exact le_trans (by norm_num) psum618o2_107
  · exact le_trans (by norm_num) psum618o2_108
  · exact le_trans (by norm_num) psum618o2_109
  · exact le_trans (by norm_num) psum618o2_110
  · exact le_trans (by norm_num) psum618o2_111
  · exact le_trans (by norm_num) psum618o2_112
  · exact le_trans (by norm_num) psum618o2_113
  · exact le_trans (by norm_num) psum618o2_114
  · exact le_trans (by norm_num) psum618o2_115
  · exact le_trans (by norm_num) psum618o2_116
  · exact le_trans (by norm_num) psum618o2_117
  · exact le_trans (by norm_num) psum618o2_118
  · exact le_trans (by norm_num) psum618o2_119
  · exact le_trans (by norm_num) psum618o2_120
  · exact le_trans (by norm_num) psum618o2_121
  · exact le_trans (by norm_num) psum618o2_122
  · exact le_trans (by norm_num) psum618o2_123
  · exact le_trans (by norm_num) psum618o2_124
  · exact le_trans (by norm_num) psum618o2_125
  · exact le_trans (by norm_num) psum618o2_126
  · exact le_trans (by norm_num) psum618o2_127
  · exact le_trans (by norm_num) psum618o2_128
  · exact le_trans (by norm_num) psum618o2_129
  · exact le_trans (by norm_num) psum618o2_130
  · exact le_trans (by norm_num) psum618o2_131
  · exact le_trans (by norm_num) psum618o2_132
  · exact le_trans (by norm_num) psum618o2_133
  · exact le_trans (by norm_num) psum618o2_134
  · exact le_trans (by norm_num) psum618o2_135
  · exact le_trans (by norm_num) psum618o2_136
  · exact le_trans (by norm_num) psum618o2_137
  · exact le_trans (by norm_num) psum618o2_138
  · exact le_trans (by norm_num) psum618o2_139
  · exact le_trans (by norm_num) psum618o2_140
  · exact le_trans (by norm_num) psum618o2_141
  · exact le_trans (by norm_num) psum618o2_142
  · exact le_trans (by norm_num) psum618o2_143
  · exact le_trans (by norm_num) psum618o2_144
  · exact le_trans (by norm_num) psum618o2_145
  · exact le_trans (by norm_num) psum618o2_146
  · exact le_trans (by norm_num) psum618o2_147
  · exact le_trans (by norm_num) psum618o2_148
  · exact le_trans (by norm_num) psum618o2_149
  · exact le_trans (by norm_num) psum618o2_150
  · exact le_trans (by norm_num) psum618o2_151
  · exact le_trans (by norm_num) psum618o2_152
  · exact le_trans (by norm_num) psum618o2_153
  · exact le_trans (by norm_num) psum618o2_154
  · exact le_trans (by norm_num) psum618o2_155
  · exact le_trans (by norm_num) psum618o2_156
  · exact le_trans (by norm_num) psum618o2_157
  · exact le_trans (by norm_num) psum618o2_158
  · exact le_trans (by norm_num) psum618o2_159
  · exact le_trans (by norm_num) psum618o2_160
  · exact le_trans (by norm_num) psum618o2_161
  · exact le_trans (by norm_num) psum618o2_162
  · exact le_trans (by norm_num) psum618o2_163
  · exact le_trans (by norm_num) psum618o2_164
  · exact le_trans (by norm_num) psum618o2_165
  · exact le_trans (by norm_num) psum618o2_166
  · exact le_trans (by norm_num) psum618o2_167
  · exact le_trans (by norm_num) psum618o2_168
  · exact le_trans (by norm_num) psum618o2_169
  · exact le_trans (by norm_num) psum618o2_170
  · exact le_trans (by norm_num) psum618o2_171
  · exact le_trans (by norm_num) psum618o2_172
  · exact le_trans (by norm_num) psum618o2_173
  · exact le_trans (by norm_num) psum618o2_174
  · exact le_trans (by norm_num) psum618o2_175
  · exact le_trans (by norm_num) psum618o2_176
  · exact le_trans (by norm_num) psum618o2_177
  · exact le_trans (by norm_num) psum618o2_178
  · exact le_trans (by norm_num) psum618o2_179
  · exact le_trans (by norm_num) psum618o2_180
  · exact le_trans (by norm_num) psum618o2_181
  · exact le_trans (by norm_num) psum618o2_182
  · exact le_trans (by norm_num) psum618o2_183
  · exact le_trans (by norm_num) psum618o2_184
  · exact le_trans (by norm_num) psum618o2_185
  · exact le_trans (by norm_num) psum618o2_186
  · exact le_trans (by norm_num) psum618o2_187
  · exact le_trans (by norm_num) psum618o2_188
  · exact le_trans (by norm_num) psum618o2_189
  · exact le_trans (by norm_num) psum618o2_190
  · exact le_trans (by norm_num) psum618o2_191
  · exact le_trans (by norm_num) psum618o2_192
  · exact le_trans (by norm_num) psum618o2_193
  · exact le_trans (by norm_num) psum618o2_194
  · exact le_trans (by norm_num) psum618o2_195
  · exact le_trans (by norm_num) psum618o2_196
  · exact le_trans (by norm_num) psum618o2_197
  · exact le_trans (by norm_num) psum618o2_198
  · exact le_trans (by norm_num) psum618o2_199
  · exact le_trans (by norm_num) psum618o2_200
  · exact le_trans (by norm_num) psum618o2_201
  · exact le_trans (by norm_num) psum618o2_202
  · exact le_trans (by norm_num) psum618o2_203
  · exact le_trans (by norm_num) psum618o2_204
  · exact le_trans (by norm_num) psum618o2_205
  · exact le_trans (by norm_num) psum618o2_206
  · exact le_trans (by norm_num) psum618o2_207
  · exact le_trans (by norm_num) psum618o2_208
  · exact le_trans (by norm_num) psum618o2_209
  · exact le_trans (by norm_num) psum618o2_210
  · exact le_trans (by norm_num) psum618o2_211
  · exact le_trans (by norm_num) psum618o2_212
  · exact le_trans (by norm_num) psum618o2_213
  · exact le_trans (by norm_num) psum618o2_214
  · exact le_trans (by norm_num) psum618o2_215
  · exact le_trans (by norm_num) psum618o2_216
  · exact le_trans (by norm_num) psum618o2_217
  · exact le_trans (by norm_num) psum618o2_218
  · exact le_trans (by norm_num) psum618o2_219
  · exact le_trans (by norm_num) psum618o2_220
  · exact le_trans (by norm_num) psum618o2_221
  · exact le_trans (by norm_num) psum618o2_222
  · exact le_trans (by norm_num) psum618o2_223
  · exact le_trans (by norm_num) psum618o2_224
  · exact le_trans (by norm_num) psum618o2_225
  · exact le_trans (by norm_num) psum618o2_226
  · exact le_trans (by norm_num) psum618o2_227
  · exact le_trans (by norm_num) psum618o2_228
  · exact le_trans (by norm_num) psum618o2_229
  · exact le_trans (by norm_num) psum618o2_230
  · exact le_trans (by norm_num) psum618o2_231
  · exact le_trans (by norm_num) psum618o2_232
  · exact le_trans (by norm_num) psum618o2_233
  · exact le_trans (by norm_num) psum618o2_234
  · exact le_trans (by norm_num) psum618o2_235
  · exact le_trans (by norm_num) psum618o2_236
  · exact le_trans (by norm_num) psum618o2_237
  · exact le_trans (by norm_num) psum618o2_238
  · exact le_trans (by norm_num) psum618o2_239
  · exact le_trans (by norm_num) psum618o2_240
  · exact le_trans (by norm_num) psum618o2_241
  · exact le_trans (by norm_num) psum618o2_242
  · exact le_trans (by norm_num) psum618o2_243
  · exact le_trans (by norm_num) psum618o2_244
  · exact le_trans (by norm_num) psum618o2_245
  · exact le_trans (by norm_num) psum618o2_246
  · exact le_trans (by norm_num) psum618o2_247
  · exact le_trans (by norm_num) psum618o2_248
  · exact le_trans (by norm_num) psum618o2_249
  · exact le_trans (by norm_num) psum618o2_250
  · exact le_trans (by norm_num) psum618o2_251
  · exact le_trans (by norm_num) psum618o2_252
  · exact le_trans (by norm_num) psum618o2_253
  · exact le_trans (by norm_num) psum618o2_254
  · exact le_trans (by norm_num) psum618o2_255
  · exact le_trans (by norm_num) psum618o2_256
  · exact le_trans (by norm_num) psum618o2_257
  · exact le_trans (by norm_num) psum618o2_258
  · exact le_trans (by norm_num) psum618o2_259
  · exact le_trans (by norm_num) psum618o2_260
  · exact le_trans (by norm_num) psum618o2_261
  · exact le_trans (by norm_num) psum618o2_262
  · exact le_trans (by norm_num) psum618o2_263
  · exact le_trans (by norm_num) psum618o2_264
  · exact le_trans (by norm_num) psum618o2_265
  · exact le_trans (by norm_num) psum618o2_266
  · exact le_trans (by norm_num) psum618o2_267
  · exact le_trans (by norm_num) psum618o2_268
  · exact le_trans (by norm_num) psum618o2_269
  · exact le_trans (by norm_num) psum618o2_270
  · exact le_trans (by norm_num) psum618o2_271
  · exact le_trans (by norm_num) psum618o2_272
  · exact le_trans (by norm_num) psum618o2_273
  · exact le_trans (by norm_num) psum618o2_274
  · exact le_trans (by norm_num) psum618o2_275
  · exact le_trans (by norm_num) psum618o2_276
  · exact le_trans (by norm_num) psum618o2_277
  · exact le_trans (by norm_num) psum618o2_278
  · exact le_trans (by norm_num) psum618o2_279
  · exact le_trans (by norm_num) psum618o2_280
  · exact le_trans (by norm_num) psum618o2_281
  · exact le_trans (by norm_num) psum618o2_282
  · exact le_trans (by norm_num) psum618o2_283
  · exact le_trans (by norm_num) psum618o2_284
  · exact le_trans (by norm_num) psum618o2_285
  · exact le_trans (by norm_num) psum618o2_286
  · exact le_trans (by norm_num) psum618o2_287
  · exact le_trans (by norm_num) psum618o2_288
  · exact le_trans (by norm_num) psum618o2_289
  · exact le_trans (by norm_num) psum618o2_290
  · exact le_trans (by norm_num) psum618o2_291
  · exact le_trans (by norm_num) psum618o2_292
  · exact le_trans (by norm_num) psum618o2_293
  · exact le_trans (by norm_num) psum618o2_294
  · exact le_trans (by norm_num) psum618o2_295
  · exact le_trans (by norm_num) psum618o2_296
  · exact le_trans (by norm_num) psum618o2_297
  · exact le_trans (by norm_num) psum618o2_298
  · exact le_trans (by norm_num) psum618o2_299
  · exact le_trans (by norm_num) psum618o2_300
  · exact le_trans (by norm_num) psum618o2_301
  · exact le_trans (by norm_num) psum618o2_302
  · exact le_trans (by norm_num) psum618o2_303
  · exact le_trans (by norm_num) psum618o2_304
  · exact le_trans (by norm_num) psum618o2_305
  · exact le_trans (by norm_num) psum618o2_306
  · exact le_trans (by norm_num) psum618o2_307
  · exact le_trans (by norm_num) psum618o2_308
  · exact le_trans (by norm_num) psum618o2_309
  · exact le_trans (by norm_num) psum618o2_310
  · exact le_trans (by norm_num) psum618o2_311
  · exact le_trans (by norm_num) psum618o2_312
  · exact le_trans (by norm_num) psum618o2_313
  · exact le_trans (by norm_num) psum618o2_314
  · exact le_trans (by norm_num) psum618o2_315
  · exact le_trans (by norm_num) psum618o2_316
  · exact le_trans (by norm_num) psum618o2_317
  · exact le_trans (by norm_num) psum618o2_318
  · exact le_trans (by norm_num) psum618o2_319
  · exact le_trans (by norm_num) psum618o2_320
  · exact le_trans (by norm_num) psum618o2_321
  · exact le_trans (by norm_num) psum618o2_322
  · exact le_trans (by norm_num) psum618o2_323
  · exact le_trans (by norm_num) psum618o2_324
  · exact le_trans (by norm_num) psum618o2_325
  · exact le_trans (by norm_num) psum618o2_326
  · exact le_trans (by norm_num) psum618o2_327
  · exact le_trans (by norm_num) psum618o2_328
  · exact le_trans (by norm_num) psum618o2_329
  · exact le_trans (by norm_num) psum618o2_330
  · exact le_trans (by norm_num) psum618o2_331
  · exact le_trans (by norm_num) psum618o2_332
  · exact le_trans (by norm_num) psum618o2_333
  · exact le_trans (by norm_num) psum618o2_334
  · exact le_trans (by norm_num) psum618o2_335
  · exact le_trans (by norm_num) psum618o2_336
  · exact le_trans (by norm_num) psum618o2_337
  · exact le_trans (by norm_num) psum618o2_338
  · exact le_trans (by norm_num) psum618o2_339
  · exact le_trans (by norm_num) psum618o2_340
  · exact le_trans (by norm_num) psum618o2_341
  · exact le_trans (by norm_num) psum618o2_342
  · exact le_trans (by norm_num) psum618o2_343
  · exact le_trans (by norm_num) psum618o2_344
  · exact le_trans (by norm_num) psum618o2_345
  · exact le_trans (by norm_num) psum618o2_346
  · exact le_trans (by norm_num) psum618o2_347
  · exact le_trans (by norm_num) psum618o2_348
  · exact le_trans (by norm_num) psum618o2_349
  · exact le_trans (by norm_num) psum618o2_350
  · exact le_trans (by norm_num) psum618o2_351
  · exact le_trans (by norm_num) psum618o2_352
  · exact le_trans (by norm_num) psum618o2_353
  · exact le_trans (by norm_num) psum618o2_354
  · exact le_trans (by norm_num) psum618o2_355
  · exact le_trans (by norm_num) psum618o2_356
  · exact le_trans (by norm_num) psum618o2_357
  · exact le_trans (by norm_num) psum618o2_358
  · exact le_trans (by norm_num) psum618o2_359
  · exact le_trans (by norm_num) psum618o2_360
  · exact le_trans (by norm_num) psum618o2_361
  · exact le_trans (by norm_num) psum618o2_362
  · exact le_trans (by norm_num) psum618o2_363
  · exact le_trans (by norm_num) psum618o2_364
  · exact le_trans (by norm_num) psum618o2_365
  · exact le_trans (by norm_num) psum618o2_366
  · exact le_trans (by norm_num) psum618o2_367
  · exact le_trans (by norm_num) psum618o2_368
  · exact le_trans (by norm_num) psum618o2_369
  · exact le_trans (by norm_num) psum618o2_370
  · exact le_trans (by norm_num) psum618o2_371
  · exact le_trans (by norm_num) psum618o2_372
  · exact le_trans (by norm_num) psum618o2_373
  · exact le_trans (by norm_num) psum618o2_374
  · exact le_trans (by norm_num) psum618o2_375
  · exact le_trans (by norm_num) psum618o2_376
  · exact le_trans (by norm_num) psum618o2_377
  · exact le_trans (by norm_num) psum618o2_378
  · exact le_trans (by norm_num) psum618o2_379
  · exact le_trans (by norm_num) psum618o2_380
  · exact le_trans (by norm_num) psum618o2_381
  · exact le_trans (by norm_num) psum618o2_382
  · exact le_trans (by norm_num) psum618o2_383
  · exact le_trans (by norm_num) psum618o2_384
  · exact le_trans (by norm_num) psum618o2_385
  · exact le_trans (by norm_num) psum618o2_386
  · exact le_trans (by norm_num) psum618o2_387
  · exact le_trans (by norm_num) psum618o2_388
  · exact le_trans (by norm_num) psum618o2_389
  · exact le_trans (by norm_num) psum618o2_390
  · exact le_trans (by norm_num) psum618o2_391
  · exact le_trans (by norm_num) psum618o2_392
  · exact le_trans (by norm_num) psum618o2_393
  · exact le_trans (by norm_num) psum618o2_394
  · exact le_trans (by norm_num) psum618o2_395
  · exact le_trans (by norm_num) psum618o2_396
  · exact le_trans (by norm_num) psum618o2_397
  · exact le_trans (by norm_num) psum618o2_398
  · exact le_trans (by norm_num) psum618o2_399
  · exact le_trans (by norm_num) psum618o2_400
  · exact le_trans (by norm_num) psum618o2_401
  · exact le_trans (by norm_num) psum618o2_402
  · exact le_trans (by norm_num) psum618o2_403
  · exact le_trans (by norm_num) psum618o2_404
  · exact le_trans (by norm_num) psum618o2_405
  · exact le_trans (by norm_num) psum618o2_406
  · exact le_trans (by norm_num) psum618o2_407
  · exact le_trans (by norm_num) psum618o2_408
  · exact le_trans (by norm_num) psum618o2_409
  · exact le_trans (by norm_num) psum618o2_410
  · exact le_trans (by norm_num) psum618o2_411
  · exact le_trans (by norm_num) psum618o2_412
  · exact le_trans (by norm_num) psum618o2_413
  · exact le_trans (by norm_num) psum618o2_414
  · exact le_trans (by norm_num) psum618o2_415
  · exact le_trans (by norm_num) psum618o2_416
  · exact le_trans (by norm_num) psum618o2_417
  · exact le_trans (by norm_num) psum618o2_418
  · exact le_trans (by norm_num) psum618o2_419
  · exact le_trans (by norm_num) psum618o2_420
  · exact le_trans (by norm_num) psum618o2_421
  · exact le_trans (by norm_num) psum618o2_422
  · exact le_trans (by norm_num) psum618o2_423
  · exact le_trans (by norm_num) psum618o2_424
  · exact le_trans (by norm_num) psum618o2_425
  · exact le_trans (by norm_num) psum618o2_426
  · exact le_trans (by norm_num) psum618o2_427
  · exact le_trans (by norm_num) psum618o2_428
  · exact le_trans (by norm_num) psum618o2_429
  · exact le_trans (by norm_num) psum618o2_430
  · exact le_trans (by norm_num) psum618o2_431
  · exact le_trans (by norm_num) psum618o2_432
  · exact le_trans (by norm_num) psum618o2_433
  · exact le_trans (by norm_num) psum618o2_434
  · exact le_trans (by norm_num) psum618o2_435
  · exact le_trans (by norm_num) psum618o2_436
  · exact le_trans (by norm_num) psum618o2_437
  · exact le_trans (by norm_num) psum618o2_438
  · exact le_trans (by norm_num) psum618o2_439
  · exact le_trans (by norm_num) psum618o2_440
  · exact le_trans (by norm_num) psum618o2_441
  · exact le_trans (by norm_num) psum618o2_442
  · exact le_trans (by norm_num) psum618o2_443
  · exact le_trans (by norm_num) psum618o2_444
  · exact le_trans (by norm_num) psum618o2_445
  · exact le_trans (by norm_num) psum618o2_446
  · exact le_trans (by norm_num) psum618o2_447
  · exact le_trans (by norm_num) psum618o2_448
  · exact le_trans (by norm_num) psum618o2_449
  · exact le_trans (by norm_num) psum618o2_450
  · exact le_trans (by norm_num) psum618o2_451
  · exact le_trans (by norm_num) psum618o2_452
  · exact le_trans (by norm_num) psum618o2_453
  · exact le_trans (by norm_num) psum618o2_454
  · exact le_trans (by norm_num) psum618o2_455
  · exact le_trans (by norm_num) psum618o2_456
  · exact le_trans (by norm_num) psum618o2_457
  · exact le_trans (by norm_num) psum618o2_458
  · exact le_trans (by norm_num) psum618o2_459
  · exact le_trans (by norm_num) psum618o2_460
  · exact le_trans (by norm_num) psum618o2_461
  · exact le_trans (by norm_num) psum618o2_462
  · exact le_trans (by norm_num) psum618o2_463
  · exact le_trans (by norm_num) psum618o2_464
  · exact le_trans (by norm_num) psum618o2_465
  · exact le_trans (by norm_num) psum618o2_466
  · exact le_trans (by norm_num) psum618o2_467
  · exact le_trans (by norm_num) psum618o2_468
  · exact le_trans (by norm_num) psum618o2_469
  · exact le_trans (by norm_num) psum618o2_470
  · exact le_trans (by norm_num) psum618o2_471
  · exact le_trans (by norm_num) psum618o2_472
  · exact le_trans (by norm_num) psum618o2_473
  · exact le_trans (by norm_num) psum618o2_474
  · exact le_trans (by norm_num) psum618o2_475
  · exact le_trans (by norm_num) psum618o2_476
  · exact le_trans (by norm_num) psum618o2_477
  · exact le_trans (by norm_num) psum618o2_478
  · exact le_trans (by norm_num) psum618o2_479
  · exact le_trans (by norm_num) psum618o2_480
  · exact le_trans (by norm_num) psum618o2_481
  · exact le_trans (by norm_num) psum618o2_482
  · exact le_trans (by norm_num) psum618o2_483
  · exact le_trans (by norm_num) psum618o2_484
  · exact le_trans (by norm_num) psum618o2_485
  · exact le_trans (by norm_num) psum618o2_486
  · exact le_trans (by norm_num) psum618o2_487
  · exact le_trans (by norm_num) psum618o2_488
  · exact le_trans (by norm_num) psum618o2_489
  · exact le_trans (by norm_num) psum618o2_490
  · exact le_trans (by norm_num) psum618o2_491
  · exact le_trans (by norm_num) psum618o2_492
  · exact le_trans (by norm_num) psum618o2_493
  · exact le_trans (by norm_num) psum618o2_494
  · exact le_trans (by norm_num) psum618o2_495
  · exact le_trans (by norm_num) psum618o2_496
  · exact le_trans (by norm_num) psum618o2_497
  · exact le_trans (by norm_num) psum618o2_498
  · exact le_trans (by norm_num) psum618o2_499
  · exact le_trans (by norm_num) psum618o2_500

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum618o2_floor
#print axioms CriticalLinePhasor.DVP.psum618o2_500
end AxiomAudit
