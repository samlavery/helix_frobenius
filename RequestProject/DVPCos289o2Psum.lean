import RequestProject.DVPCos289o2Table

/-!
# The cosine partial-sum floor, `t = 289/2`
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 289/2` segment certificate. -/
def cos289o2c (n : ℕ) : ℝ := Real.cos (((289:ℕ):ℝ) * (Real.log n / 2))

theorem psum289o2_11 : ((302623/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos289o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 11 - ((302643/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum289o2_12 : ((1205083/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos289o2c k) + cos289o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_11
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 12 - ((599877/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_13 : ((1101199/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos289o2c k) + cos289o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_12
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 13 - ((199471/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_14 : ((370069/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos289o2c k) + cos289o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_13
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 14 - ((-352013/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_15 : ((833191/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos289o2c k) + cos289o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_14
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 15 - ((-183923/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_16 : ((1752247/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos289o2c k) + cos289o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_15
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 16 - ((17181/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_17 : ((1149493/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos289o2c k) + cos289o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_16
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 17 - ((546779/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_18 : ((1313891/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos289o2c k) + cos289o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_17
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 18 - ((-197011/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_19 : ((1101113/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos289o2c k) + cos289o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_18
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 19 - ((-106369/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_20 : ((1893221/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos289o2c k) + cos289o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_19
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 20 - ((198037/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_21 : ((72177/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos289o2c k) + cos289o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_20
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 21 - ((993899/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_22 : ((1869919/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos289o2c k) + cos289o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_21
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 22 - ((426399/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_23 : ((4511313/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos289o2c k) + cos289o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_22
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 23 - ((154303/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_24 : ((83758/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos289o2c k) + cos289o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_23
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 24 - ((849239/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_25 : ((6345743/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos289o2c k) + cos289o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_24
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 25 - ((985271/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_26 : ((7248767/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos289o2c k) + cos289o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_25
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 26 - ((112883/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_27 : ((942689/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos289o2c k) + cos289o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_26
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 27 - ((58557/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_28 : ((6873921/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos289o2c k) + cos289o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_27
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 28 - ((-667551/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_29 : ((5942501/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos289o2c k) + cos289o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_28
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 29 - ((-46569/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_30 : ((6127619/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos289o2c k) + cos289o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_29
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 30 - ((92579/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_31 : ((7114729/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos289o2c k) + cos289o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_30
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 31 - ((19743/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_32 : ((1708339/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos289o2c k) + cos289o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_31
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 32 - ((-281333/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_33 : ((1196271/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos289o2c k) + cos289o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_32
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 33 - ((-851961/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_34 : ((21233/3125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos289o2c k) + cos289o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_33
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 34 - ((162649/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_35 : ((86147/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos289o2c k) + cos289o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_34
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 35 - ((2431/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_36 : ((603623/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos289o2c k) + cos289o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_35
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 36 - ((-85549/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_37 : ((1399817/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos289o2c k) + cos289o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_36
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 37 - ((192579/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_38 : ((644637/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos289o2c k) + cos289o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_37
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 38 - ((-22107/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_39 : ((6420037/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos289o2c k) + cos289o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_38
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 39 - ((-26293/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_40 : ((1734203/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos289o2c k) + cos289o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_39
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 40 - ((103363/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_41 : ((1222421/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos289o2c k) + cos289o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_40
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 41 - ((-824667/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_42 : ((3539141/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos289o2c k) + cos289o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_41
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 42 - ((966217/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_43 : ((1519561/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos289o2c k) + cos289o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_42
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 43 - ((-499999/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_44 : ((3531177/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos289o2c k) + cos289o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_43
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 44 - ((19683/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_45 : ((3051187/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos289o2c k) + cos289o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_44
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 45 - ((-47997/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_46 : ((3526041/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos289o2c k) + cos289o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_45
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 46 - ((237437/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_47 : ((3046111/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos289o2c k) + cos289o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_46
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 47 - ((-47991/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_48 : ((7075107/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos289o2c k) + cos289o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_47
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 48 - ((39317/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_49 : ((607533/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos289o2c k) + cos289o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_48
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 49 - ((-999737/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_50 : ((3527743/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos289o2c k) + cos289o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_49
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 50 - ((245049/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_51 : ((1542051/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos289o2c k) + cos289o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_50
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 51 - ((-443621/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_52 : ((685393/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos289o2c k) + cos289o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_51
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 52 - ((342883/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_53 : ((3247757/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos289o2c k) + cos289o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_52
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 53 - ((-44797/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_54 : ((1284297/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos289o2c k) + cos289o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_53
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 54 - ((-73989/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_55 : ((6956189/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos289o2c k) + cos289o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_54
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 55 - ((66843/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_56 : ((303199/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos289o2c k) + cos289o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_55
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 56 - ((-892169/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_57 : ((7057297/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos289o2c k) + cos289o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_56
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 57 - ((993357/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_58 : ((79017/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos289o2c k) + cos289o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_57
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 58 - ((-735897/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_59 : ((6476233/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos289o2c k) + cos289o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_58
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 59 - ((154913/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_60 : ((3502599/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos289o2c k) + cos289o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_59
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 60 - ((105801/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_61 : ((1207767/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos289o2c k) + cos289o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_60
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 61 - ((-966323/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_62 : ((3450373/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos289o2c k) + cos289o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_61
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 62 - ((861951/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_63 : ((3346333/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos289o2c k) + cos289o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_62
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 63 - ((-5201/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_64 : ((6082363/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos289o2c k) + cos289o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_63
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 64 - ((-610263/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_65 : ((1770559/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos289o2c k) + cos289o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_64
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 65 - ((999913/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_66 : ((809773/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos289o2c k) + cos289o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_65
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 66 - ((-151003/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_67 : ((1540873/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos289o2c k) + cos289o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_66
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 67 - ((-78663/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_68 : ((713239/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos289o2c k) + cos289o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_67
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 68 - ((484469/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_69 : ((1284593/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos289o2c k) + cos289o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_68
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 69 - ((-141877/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_70 : ((6152533/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos289o2c k) + cos289o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_69
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 70 - ((-33799/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_71 : ((3565769/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos289o2c k) + cos289o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_70
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 71 - ((195809/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_72 : ((6522099/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos289o2c k) + cos289o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_71
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 72 - ((-609399/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_73 : ((6048649/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos289o2c k) + cos289o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_72
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 73 - ((-47341/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_74 : ((880477/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos289o2c k) + cos289o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_73
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 74 - ((995207/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_75 : ((6776181/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos289o2c k) + cos289o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_74
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 75 - ((-53519/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_76 : ((5958809/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos289o2c k) + cos289o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_75
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 76 - ((-204333/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_77 : ((3380837/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos289o2c k) + cos289o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_76
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 77 - ((160581/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_78 : ((1419947/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos289o2c k) + cos289o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_77
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 78 - ((338101/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_79 : ((6102499/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos289o2c k) + cos289o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_78
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 79 - ((-249299/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_80 : ((784193/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos289o2c k) + cos289o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_79
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 80 - ((34217/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_81 : ((1799011/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos289o2c k) + cos289o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_80
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 81 - ((46127/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_82 : ((6632667/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos289o2c k) + cos289o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_81
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 82 - ((-563337/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_83 : ((5921127/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos289o2c k) + cos289o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_82
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 83 - ((-1423/2000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_84 : ((6728009/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos289o2c k) + cos289o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_83
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 84 - ((403461/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_85 : ((90011/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos289o2c k) + cos289o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_84
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 85 - ((472911/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_86 : ((6269717/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos289o2c k) + cos289o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_85
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 86 - ((-931123/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_87 : ((2999757/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos289o2c k) + cos289o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_86
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 87 - ((-270163/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_88 : ((1745231/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos289o2c k) + cos289o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_87
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 88 - ((19629/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_89 : ((7111441/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos289o2c k) + cos289o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_88
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 89 - ((130557/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_90 : ((6115199/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos289o2c k) + cos289o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_89
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 90 - ((-498101/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_91 : ((37837/6250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos289o2c k) + cos289o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_90
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 91 - ((-61239/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_92 : ((1410497/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos289o2c k) + cos289o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_91
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 92 - ((199721/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_93 : ((3556927/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos289o2c k) + cos289o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_92
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 93 - ((61409/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_94 : ((764697/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos289o2c k) + cos289o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_93
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 94 - ((-498119/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_95 : ((5989433/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos289o2c k) + cos289o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_94
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 95 - ((-128103/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_96 : ((6972117/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos289o2c k) + cos289o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_95
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 96 - ((245681/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_97 : ((1445739/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos289o2c k) + cos289o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_96
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 97 - ((128309/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_98 : ((1257737/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos289o2c k) + cos289o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_97
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 98 - ((-93997/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_99 : ((2925927/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos289o2c k) + cos289o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_98
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 99 - ((-436791/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_100 : ((1338683/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos289o2c k) + cos289o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_99
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 100 - ((841601/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_101 : ((7340281/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos289o2c k) + cos289o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_100
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 101 - ((323453/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_102 : ((6680753/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos289o2c k) + cos289o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_101
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 102 - ((-20609/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_103 : ((5832979/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos289o2c k) + cos289o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_102
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 103 - ((-423867/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_104 : ((1241597/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos289o2c k) + cos289o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_103
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 104 - ((187523/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_105 : ((898589/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos289o2c k) + cos289o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_104
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 105 - ((980767/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_106 : ((3596677/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos289o2c k) + cos289o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_105
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 106 - ((2341/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_107 : ((6217123/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos289o2c k) + cos289o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_106
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 107 - ((-976191/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_108 : ((2893199/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos289o2c k) + cos289o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_107
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 108 - ((-86137/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_109 : ((1640313/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos289o2c k) + cos289o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_108
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 109 - ((387447/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_110 : ((230189/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos289o2c k) + cos289o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_109
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 110 - ((201209/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_111 : ((3501119/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos289o2c k) + cos289o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_110
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 111 - ((-36377/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_112 : ((1201389/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos289o2c k) + cos289o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_111
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 112 - ((-995253/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_113 : ((181849/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos289o2c k) + cos289o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_112
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 113 - ((-187737/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_114 : ((1675773/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos289o2c k) + cos289o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_113
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 114 - ((220991/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_115 : ((59337/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos289o2c k) + cos289o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_114
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 115 - ((714073/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_116 : ((6976921/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos289o2c k) + cos289o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_115
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 116 - ((-110041/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_117 : ((2992363/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos289o2c k) + cos289o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_116
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 117 - ((-198431/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_118 : ((2885349/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos289o2c k) + cos289o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_117
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 118 - ((-53497/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_119 : ((132283/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos289o2c k) + cos289o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_118
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 119 - ((210873/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_120 : ((3707453/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos289o2c k) + cos289o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_119
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 120 - ((200199/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_121 : ((17869/2500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos289o2c k) + cos289o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_120
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 121 - ((-133633/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_122 : ((6153707/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos289o2c k) + cos289o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_121
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 122 - ((-993853/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_123 : ((567237/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos289o2c k) + cos289o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_122
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 123 - ((-481297/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_124 : ((6291677/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos289o2c k) + cos289o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_123
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 124 - ((619347/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_125 : ((3629299/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos289o2c k) + cos289o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_124
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 125 - ((966961/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_126 : ((7419479/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos289o2c k) + cos289o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_125
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 126 - ((160921/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_127 : ((1647143/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos289o2c k) + cos289o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_126
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 127 - ((-830867/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_128 : ((2866239/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos289o2c k) + cos289o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_127
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 128 - ((-428027/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_129 : ((5829227/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos289o2c k) + cos289o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_128
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 129 - ((96789/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_130 : ((6765777/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos289o2c k) + cos289o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_129
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 130 - ((93659/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_131 : ((937241/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos289o2c k) + cos289o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_130
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 131 - ((732191/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_132 : ((7224099/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos289o2c k) + cos289o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_131
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 132 - ((-273789/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_133 : ((1561143/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos289o2c k) + cos289o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_132
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 133 - ((-979487/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_134 : ((5606999/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos289o2c k) + cos289o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_133
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 134 - ((-637533/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_135 : ((2990359/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos289o2c k) + cos289o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_134
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 135 - ((373759/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_136 : ((435833/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos289o2c k) + cos289o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_135
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 136 - ((19853/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_137 : ((118207/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos289o2c k) + cos289o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_136
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 137 - ((14799/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_138 : ((111872/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos289o2c k) + cos289o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_137
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 138 - ((-2027/5000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_139 : ((6165817/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos289o2c k) + cos289o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_138
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 139 - ((-993951/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_140 : ((5564583/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos289o2c k) + cos289o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_139
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 140 - ((-300597/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_141 : ((5938683/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos289o2c k) + cos289o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_140
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 141 - ((18707/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_142 : ((6924877/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos289o2c k) + cos289o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_141
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 142 - ((493117/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_143 : ((948297/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos289o2c k) + cos289o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_142
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 143 - ((661539/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_144 : ((7306049/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos289o2c k) + cos289o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_143
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 144 - ((-280287/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_145 : ((793353/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos289o2c k) + cos289o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_144
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 145 - ((-191837/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_146 : ((1396527/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos289o2c k) + cos289o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_145
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 146 - ((-190169/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_147 : ((1141551/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos289o2c k) + cos289o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_146
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 147 - ((121687/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_148 : ((824959/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos289o2c k) + cos289o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_147
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 148 - ((891957/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_149 : ((186883/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos289o2c k) + cos289o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_148
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 149 - ((109461/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_150 : ((303017/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos289o2c k) + cos289o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_149
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 150 - ((20029/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_151 : ((1704413/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos289o2c k) + cos289o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_150
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 151 - ((-757733/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_152 : ((730869/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos289o2c k) + cos289o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_151
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 152 - ((-48533/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_153 : ((2737803/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos289o2c k) + cos289o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_152
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 153 - ((-185653/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_154 : ((1501891/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos289o2c k) + cos289o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_153
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 154 - ((265999/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_155 : ((3502373/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos289o2c k) + cos289o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_154
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 155 - ((498611/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_156 : ((1915287/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos289o2c k) + cos289o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_155
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 156 - ((328221/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_157 : ((1491071/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos289o2c k) + cos289o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_156
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 157 - ((-205753/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_158 : ((327659/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos289o2c k) + cos289o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_157
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 158 - ((-180427/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_159 : ((5659577/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos289o2c k) + cos289o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_158
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 159 - ((-893563/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_160 : ((546159/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos289o2c k) + cos289o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_159
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 160 - ((-197947/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_161 : ((3053283/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos289o2c k) + cos289o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_160
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 161 - ((80627/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_162 : ((3553107/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos289o2c k) + cos289o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_161
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 162 - ((124961/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_163 : ((308663/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos289o2c k) + cos289o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_162
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 163 - ((610401/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_164 : ((374563/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos289o2c k) + cos289o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_163
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 164 - ((-9011/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_165 : ((6597469/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos289o2c k) + cos289o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_164
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 165 - ((-893751/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_166 : ((1135899/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos289o2c k) + cos289o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_165
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 166 - ((-458967/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_167 : ((1077751/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos289o2c k) + cos289o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_166
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 167 - ((-2907/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_168 : ((5926427/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos289o2c k) + cos289o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_167
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 168 - ((33607/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_169 : ((6915821/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos289o2c k) + cos289o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_168
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 169 - ((494717/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_170 : ((7676089/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos289o2c k) + cos289o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_169
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 170 - ((190077/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_171 : ((961541/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos289o2c k) + cos289o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_170
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 171 - ((16279/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_172 : ((6956869/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos289o2c k) + cos289o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_171
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 172 - ((-735419/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_173 : ((2980583/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos289o2c k) + cos289o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_172
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 173 - ((-995663/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_174 : ((536011/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos289o2c k) + cos289o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_173
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 174 - ((-75127/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_175 : ((138559/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos289o2c k) + cos289o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_174
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 175 - ((18229/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_176 : ((6387379/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos289o2c k) + cos289o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_175
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 176 - ((845059/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_177 : ((3677553/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos289o2c k) + cos289o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_176
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 177 - ((967767/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_178 : ((1567271/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos289o2c k) + cos289o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_177
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 178 - ((481289/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_179 : ((7533727/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos289o2c k) + cos289o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_178
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 179 - ((-75647/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_180 : ((1659229/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos289o2c k) + cos289o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_179
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 180 - ((-896771/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_181 : ((113897/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos289o2c k) + cos289o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_180
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 181 - ((-471013/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_182 : ((5275687/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos289o2c k) + cos289o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_181
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 182 - ((-419123/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_183 : ((2813637/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos289o2c k) + cos289o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_182
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 183 - ((351627/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_184 : ((1634669/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos289o2c k) + cos289o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_183
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 184 - ((455721/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_185 : ((373741/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos289o2c k) + cos289o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_184
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 185 - ((117023/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_186 : ((7894051/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos289o2c k) + cos289o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_185
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 186 - ((419271/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_187 : ((3779241/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos289o2c k) + cos289o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_186
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 187 - ((-335529/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_188 : ((6661489/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos289o2c k) + cos289o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_187
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 188 - ((-896953/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_189 : ((1141739/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos289o2c k) + cos289o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_188
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 189 - ((-476377/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_190 : ((163423/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos289o2c k) + cos289o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_189
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 190 - ((-479119/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_191 : ((5485501/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos289o2c k) + cos289o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_190
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 191 - ((51201/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_192 : ((1583531/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos289o2c k) + cos289o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_191
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 192 - ((848663/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_193 : ((7315459/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos289o2c k) + cos289o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_192
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 193 - ((7851/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_194 : ((3952571/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos289o2c k) + cos289o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_193
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 194 - ((589723/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_195 : ((7793121/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos289o2c k) + cos289o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_194
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 195 - ((-111981/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_196 : ((7040911/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos289o2c k) + cos289o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_195
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 196 - ((-75217/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_197 : ((3020499/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos289o2c k) + cos289o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_196
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 197 - ((-999873/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_198 : ((2653809/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos289o2c k) + cos289o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_197
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 198 - ((-36667/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_199 : ((2606231/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos289o2c k) + cos289o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_198
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 199 - ((-23779/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_200 : ((1450199/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos289o2c k) + cos289o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_199
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 200 - ((294187/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_201 : ((271057/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos289o2c k) + cos289o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_200
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 201 - ((975669/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_202 : ((3827923/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos289o2c k) + cos289o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_201
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 202 - ((879461/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_203 : ((8009151/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos289o2c k) + cos289o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_202
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 203 - ((70669/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_204 : ((383361/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos289o2c k) + cos289o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_203
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 204 - ((-341891/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_205 : ((849627/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos289o2c k) + cos289o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_204
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 205 - ((-217541/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_206 : ((2907289/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos289o2c k) + cos289o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_205
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 206 - ((-491199/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_207 : ((5183309/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos289o2c k) + cos289o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_206
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 207 - ((-631229/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_208 : ((5196521/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos289o2c k) + cos289o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_207
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 208 - ((3313/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_209 : ((2922753/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos289o2c k) + cos289o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_208
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 209 - ((25961/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_210 : ((1707559/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos289o2c k) + cos289o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_209
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 210 - ((98477/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_211 : ((962763/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos289o2c k) + cos289o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_210
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 211 - ((217977/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_212 : ((8069151/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos289o2c k) + cos289o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_211
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 212 - ((367087/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_213 : ((7769651/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos289o2c k) + cos289o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_212
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 213 - ((-14973/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_214 : ((1387717/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos289o2c k) + cos289o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_213
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 214 - ((-415513/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_215 : ((1188411/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos289o2c k) + cos289o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_214
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 215 - ((-99649/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_216 : ((5213299/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos289o2c k) + cos289o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_215
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 216 - ((-182179/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_217 : ((1012959/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos289o2c k) + cos289o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_216
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 217 - ((-9279/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_218 : ((5557597/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos289o2c k) + cos289o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_217
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 218 - ((246421/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_219 : ((101264/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos289o2c k) + cos289o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_218
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 219 - ((923339/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_220 : ((7446157/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos289o2c k) + cos289o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_219
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 220 - ((965301/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_221 : ((503269/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos289o2c k) + cos289o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_220
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 221 - ((606187/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_222 : ((4025581/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos289o2c k) + cos289o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_221
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 222 - ((-551/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_223 : ((7445503/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos289o2c k) + cos289o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_222
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 223 - ((-605619/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_224 : ((648269/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos289o2c k) + cos289o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_223
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 224 - ((-962773/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_225 : ((2775151/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos289o2c k) + cos289o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_224
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 225 - ((-233087/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_226 : ((200761/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos289o2c k) + cos289o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_225
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 226 - ((-531237/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_227 : ((5096821/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos289o2c k) + cos289o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_226
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 227 - ((19459/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_228 : ((5750947/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos289o2c k) + cos289o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_227
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 228 - ((327083/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_229 : ((1681407/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos289o2c k) + cos289o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_228
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 229 - ((974721/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_230 : ((1528993/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos289o2c k) + cos289o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_229
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 230 - ((919377/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_231 : ((8158713/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos289o2c k) + cos289o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_230
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 231 - ((128447/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_232 : ((8074187/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos289o2c k) + cos289o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_231
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 232 - ((-42243/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_233 : ((3712639/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos289o2c k) + cos289o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_232
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 233 - ((-648869/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_234 : ((6455307/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos289o2c k) + cos289o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_233
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 234 - ((-969931/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_235 : ((1380767/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos289o2c k) + cos289o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_234
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 235 - ((-932199/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_236 : ((4969287/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos289o2c k) + cos289o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_235
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 236 - ((-553741/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_237 : ((624173/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos289o2c k) + cos289o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_236
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 237 - ((24137/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_238 : ((5584553/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos289o2c k) + cos289o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_237
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 238 - ((591209/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_239 : ((3264893/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos289o2c k) + cos289o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_238
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 239 - ((945273/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_240 : ((1498651/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos289o2c k) + cos289o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_239
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 240 - ((963509/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_241 : ((8136657/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos289o2c k) + cos289o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_240
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 241 - ((321721/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_242 : ((257409/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos289o2c k) + cos289o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_241
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 242 - ((100471/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_243 : ((776181/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos289o2c k) + cos289o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_242
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 243 - ((-237619/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_244 : ((85947/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos289o2c k) + cos289o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_243
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 244 - ((-88601/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_245 : ((147041/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos289o2c k) + cos289o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_244
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 245 - ((-6213/6250 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_246 : ((5115129/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos289o2c k) + cos289o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_245
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 246 - ((-766471/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_247 : ((603987/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos289o2c k) + cos289o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_246
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 247 - ((-283193/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_248 : ((2562119/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos289o2c k) + cos289o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_247
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 248 - ((146191/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_249 : ((1473447/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos289o2c k) + cos289o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_248
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 249 - ((76959/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum289o2_250 : ((3443661/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos289o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos289o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos289o2c k) + cos289o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos289o2c
    simpa using h
  have hprev := psum289o2_249
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos289o2c 250 - ((496787/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos289o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 3200000 in
/-- **The Abel floor at `t = 289/2`.** -/
theorem psum289o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 250 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos289o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum289o2_11
  · exact le_trans (by norm_num) psum289o2_12
  · exact le_trans (by norm_num) psum289o2_13
  · exact le_trans (by norm_num) psum289o2_14
  · exact le_trans (by norm_num) psum289o2_15
  · exact le_trans (by norm_num) psum289o2_16
  · exact le_trans (by norm_num) psum289o2_17
  · exact le_trans (by norm_num) psum289o2_18
  · exact le_trans (by norm_num) psum289o2_19
  · exact le_trans (by norm_num) psum289o2_20
  · exact le_trans (by norm_num) psum289o2_21
  · exact le_trans (by norm_num) psum289o2_22
  · exact le_trans (by norm_num) psum289o2_23
  · exact le_trans (by norm_num) psum289o2_24
  · exact le_trans (by norm_num) psum289o2_25
  · exact le_trans (by norm_num) psum289o2_26
  · exact le_trans (by norm_num) psum289o2_27
  · exact le_trans (by norm_num) psum289o2_28
  · exact le_trans (by norm_num) psum289o2_29
  · exact le_trans (by norm_num) psum289o2_30
  · exact le_trans (by norm_num) psum289o2_31
  · exact le_trans (by norm_num) psum289o2_32
  · exact le_trans (by norm_num) psum289o2_33
  · exact le_trans (by norm_num) psum289o2_34
  · exact le_trans (by norm_num) psum289o2_35
  · exact le_trans (by norm_num) psum289o2_36
  · exact le_trans (by norm_num) psum289o2_37
  · exact le_trans (by norm_num) psum289o2_38
  · exact le_trans (by norm_num) psum289o2_39
  · exact le_trans (by norm_num) psum289o2_40
  · exact le_trans (by norm_num) psum289o2_41
  · exact le_trans (by norm_num) psum289o2_42
  · exact le_trans (by norm_num) psum289o2_43
  · exact le_trans (by norm_num) psum289o2_44
  · exact le_trans (by norm_num) psum289o2_45
  · exact le_trans (by norm_num) psum289o2_46
  · exact le_trans (by norm_num) psum289o2_47
  · exact le_trans (by norm_num) psum289o2_48
  · exact le_trans (by norm_num) psum289o2_49
  · exact le_trans (by norm_num) psum289o2_50
  · exact le_trans (by norm_num) psum289o2_51
  · exact le_trans (by norm_num) psum289o2_52
  · exact le_trans (by norm_num) psum289o2_53
  · exact le_trans (by norm_num) psum289o2_54
  · exact le_trans (by norm_num) psum289o2_55
  · exact le_trans (by norm_num) psum289o2_56
  · exact le_trans (by norm_num) psum289o2_57
  · exact le_trans (by norm_num) psum289o2_58
  · exact le_trans (by norm_num) psum289o2_59
  · exact le_trans (by norm_num) psum289o2_60
  · exact le_trans (by norm_num) psum289o2_61
  · exact le_trans (by norm_num) psum289o2_62
  · exact le_trans (by norm_num) psum289o2_63
  · exact le_trans (by norm_num) psum289o2_64
  · exact le_trans (by norm_num) psum289o2_65
  · exact le_trans (by norm_num) psum289o2_66
  · exact le_trans (by norm_num) psum289o2_67
  · exact le_trans (by norm_num) psum289o2_68
  · exact le_trans (by norm_num) psum289o2_69
  · exact le_trans (by norm_num) psum289o2_70
  · exact le_trans (by norm_num) psum289o2_71
  · exact le_trans (by norm_num) psum289o2_72
  · exact le_trans (by norm_num) psum289o2_73
  · exact le_trans (by norm_num) psum289o2_74
  · exact le_trans (by norm_num) psum289o2_75
  · exact le_trans (by norm_num) psum289o2_76
  · exact le_trans (by norm_num) psum289o2_77
  · exact le_trans (by norm_num) psum289o2_78
  · exact le_trans (by norm_num) psum289o2_79
  · exact le_trans (by norm_num) psum289o2_80
  · exact le_trans (by norm_num) psum289o2_81
  · exact le_trans (by norm_num) psum289o2_82
  · exact le_trans (by norm_num) psum289o2_83
  · exact le_trans (by norm_num) psum289o2_84
  · exact le_trans (by norm_num) psum289o2_85
  · exact le_trans (by norm_num) psum289o2_86
  · exact le_trans (by norm_num) psum289o2_87
  · exact le_trans (by norm_num) psum289o2_88
  · exact le_trans (by norm_num) psum289o2_89
  · exact le_trans (by norm_num) psum289o2_90
  · exact le_trans (by norm_num) psum289o2_91
  · exact le_trans (by norm_num) psum289o2_92
  · exact le_trans (by norm_num) psum289o2_93
  · exact le_trans (by norm_num) psum289o2_94
  · exact le_trans (by norm_num) psum289o2_95
  · exact le_trans (by norm_num) psum289o2_96
  · exact le_trans (by norm_num) psum289o2_97
  · exact le_trans (by norm_num) psum289o2_98
  · exact le_trans (by norm_num) psum289o2_99
  · exact le_trans (by norm_num) psum289o2_100
  · exact le_trans (by norm_num) psum289o2_101
  · exact le_trans (by norm_num) psum289o2_102
  · exact le_trans (by norm_num) psum289o2_103
  · exact le_trans (by norm_num) psum289o2_104
  · exact le_trans (by norm_num) psum289o2_105
  · exact le_trans (by norm_num) psum289o2_106
  · exact le_trans (by norm_num) psum289o2_107
  · exact le_trans (by norm_num) psum289o2_108
  · exact le_trans (by norm_num) psum289o2_109
  · exact le_trans (by norm_num) psum289o2_110
  · exact le_trans (by norm_num) psum289o2_111
  · exact le_trans (by norm_num) psum289o2_112
  · exact le_trans (by norm_num) psum289o2_113
  · exact le_trans (by norm_num) psum289o2_114
  · exact le_trans (by norm_num) psum289o2_115
  · exact le_trans (by norm_num) psum289o2_116
  · exact le_trans (by norm_num) psum289o2_117
  · exact le_trans (by norm_num) psum289o2_118
  · exact le_trans (by norm_num) psum289o2_119
  · exact le_trans (by norm_num) psum289o2_120
  · exact le_trans (by norm_num) psum289o2_121
  · exact le_trans (by norm_num) psum289o2_122
  · exact le_trans (by norm_num) psum289o2_123
  · exact le_trans (by norm_num) psum289o2_124
  · exact le_trans (by norm_num) psum289o2_125
  · exact le_trans (by norm_num) psum289o2_126
  · exact le_trans (by norm_num) psum289o2_127
  · exact le_trans (by norm_num) psum289o2_128
  · exact le_trans (by norm_num) psum289o2_129
  · exact le_trans (by norm_num) psum289o2_130
  · exact le_trans (by norm_num) psum289o2_131
  · exact le_trans (by norm_num) psum289o2_132
  · exact le_trans (by norm_num) psum289o2_133
  · exact le_trans (by norm_num) psum289o2_134
  · exact le_trans (by norm_num) psum289o2_135
  · exact le_trans (by norm_num) psum289o2_136
  · exact le_trans (by norm_num) psum289o2_137
  · exact le_trans (by norm_num) psum289o2_138
  · exact le_trans (by norm_num) psum289o2_139
  · exact le_trans (by norm_num) psum289o2_140
  · exact le_trans (by norm_num) psum289o2_141
  · exact le_trans (by norm_num) psum289o2_142
  · exact le_trans (by norm_num) psum289o2_143
  · exact le_trans (by norm_num) psum289o2_144
  · exact le_trans (by norm_num) psum289o2_145
  · exact le_trans (by norm_num) psum289o2_146
  · exact le_trans (by norm_num) psum289o2_147
  · exact le_trans (by norm_num) psum289o2_148
  · exact le_trans (by norm_num) psum289o2_149
  · exact le_trans (by norm_num) psum289o2_150
  · exact le_trans (by norm_num) psum289o2_151
  · exact le_trans (by norm_num) psum289o2_152
  · exact le_trans (by norm_num) psum289o2_153
  · exact le_trans (by norm_num) psum289o2_154
  · exact le_trans (by norm_num) psum289o2_155
  · exact le_trans (by norm_num) psum289o2_156
  · exact le_trans (by norm_num) psum289o2_157
  · exact le_trans (by norm_num) psum289o2_158
  · exact le_trans (by norm_num) psum289o2_159
  · exact le_trans (by norm_num) psum289o2_160
  · exact le_trans (by norm_num) psum289o2_161
  · exact le_trans (by norm_num) psum289o2_162
  · exact le_trans (by norm_num) psum289o2_163
  · exact le_trans (by norm_num) psum289o2_164
  · exact le_trans (by norm_num) psum289o2_165
  · exact le_trans (by norm_num) psum289o2_166
  · exact le_trans (by norm_num) psum289o2_167
  · exact le_trans (by norm_num) psum289o2_168
  · exact le_trans (by norm_num) psum289o2_169
  · exact le_trans (by norm_num) psum289o2_170
  · exact le_trans (by norm_num) psum289o2_171
  · exact le_trans (by norm_num) psum289o2_172
  · exact le_trans (by norm_num) psum289o2_173
  · exact le_trans (by norm_num) psum289o2_174
  · exact le_trans (by norm_num) psum289o2_175
  · exact le_trans (by norm_num) psum289o2_176
  · exact le_trans (by norm_num) psum289o2_177
  · exact le_trans (by norm_num) psum289o2_178
  · exact le_trans (by norm_num) psum289o2_179
  · exact le_trans (by norm_num) psum289o2_180
  · exact le_trans (by norm_num) psum289o2_181
  · exact le_trans (by norm_num) psum289o2_182
  · exact le_trans (by norm_num) psum289o2_183
  · exact le_trans (by norm_num) psum289o2_184
  · exact le_trans (by norm_num) psum289o2_185
  · exact le_trans (by norm_num) psum289o2_186
  · exact le_trans (by norm_num) psum289o2_187
  · exact le_trans (by norm_num) psum289o2_188
  · exact le_trans (by norm_num) psum289o2_189
  · exact le_trans (by norm_num) psum289o2_190
  · exact le_trans (by norm_num) psum289o2_191
  · exact le_trans (by norm_num) psum289o2_192
  · exact le_trans (by norm_num) psum289o2_193
  · exact le_trans (by norm_num) psum289o2_194
  · exact le_trans (by norm_num) psum289o2_195
  · exact le_trans (by norm_num) psum289o2_196
  · exact le_trans (by norm_num) psum289o2_197
  · exact le_trans (by norm_num) psum289o2_198
  · exact le_trans (by norm_num) psum289o2_199
  · exact le_trans (by norm_num) psum289o2_200
  · exact le_trans (by norm_num) psum289o2_201
  · exact le_trans (by norm_num) psum289o2_202
  · exact le_trans (by norm_num) psum289o2_203
  · exact le_trans (by norm_num) psum289o2_204
  · exact le_trans (by norm_num) psum289o2_205
  · exact le_trans (by norm_num) psum289o2_206
  · exact le_trans (by norm_num) psum289o2_207
  · exact le_trans (by norm_num) psum289o2_208
  · exact le_trans (by norm_num) psum289o2_209
  · exact le_trans (by norm_num) psum289o2_210
  · exact le_trans (by norm_num) psum289o2_211
  · exact le_trans (by norm_num) psum289o2_212
  · exact le_trans (by norm_num) psum289o2_213
  · exact le_trans (by norm_num) psum289o2_214
  · exact le_trans (by norm_num) psum289o2_215
  · exact le_trans (by norm_num) psum289o2_216
  · exact le_trans (by norm_num) psum289o2_217
  · exact le_trans (by norm_num) psum289o2_218
  · exact le_trans (by norm_num) psum289o2_219
  · exact le_trans (by norm_num) psum289o2_220
  · exact le_trans (by norm_num) psum289o2_221
  · exact le_trans (by norm_num) psum289o2_222
  · exact le_trans (by norm_num) psum289o2_223
  · exact le_trans (by norm_num) psum289o2_224
  · exact le_trans (by norm_num) psum289o2_225
  · exact le_trans (by norm_num) psum289o2_226
  · exact le_trans (by norm_num) psum289o2_227
  · exact le_trans (by norm_num) psum289o2_228
  · exact le_trans (by norm_num) psum289o2_229
  · exact le_trans (by norm_num) psum289o2_230
  · exact le_trans (by norm_num) psum289o2_231
  · exact le_trans (by norm_num) psum289o2_232
  · exact le_trans (by norm_num) psum289o2_233
  · exact le_trans (by norm_num) psum289o2_234
  · exact le_trans (by norm_num) psum289o2_235
  · exact le_trans (by norm_num) psum289o2_236
  · exact le_trans (by norm_num) psum289o2_237
  · exact le_trans (by norm_num) psum289o2_238
  · exact le_trans (by norm_num) psum289o2_239
  · exact le_trans (by norm_num) psum289o2_240
  · exact le_trans (by norm_num) psum289o2_241
  · exact le_trans (by norm_num) psum289o2_242
  · exact le_trans (by norm_num) psum289o2_243
  · exact le_trans (by norm_num) psum289o2_244
  · exact le_trans (by norm_num) psum289o2_245
  · exact le_trans (by norm_num) psum289o2_246
  · exact le_trans (by norm_num) psum289o2_247
  · exact le_trans (by norm_num) psum289o2_248
  · exact le_trans (by norm_num) psum289o2_249
  · exact le_trans (by norm_num) psum289o2_250

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum289o2_floor
#print axioms CriticalLinePhasor.DVP.psum289o2_250
end AxiomAudit
