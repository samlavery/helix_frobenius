import RequestProject.DVPCos63Table

/-!
# The cosine partial-sum floor, `t = 63` (rung-63 of the channel)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 63` segment certificate. -/
def cos63c (n : ℕ) : ℝ := Real.cos (((63:ℕ):ℝ) * Real.log n)

theorem psum63_11 : ((240869/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos63c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/25000 : ℚ) : ℝ) ≤ cos63c 11 - ((240879/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_11).1
  push_cast at h ⊢
  linarith

theorem psum63_12 : ((1825983/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos63c k)
      = (∑ k ∈ Finset.Icc 11 11, cos63c k) + cos63c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_11
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 12 - ((862547/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_13 : ((325413/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos63c k)
      = (∑ k ∈ Finset.Icc 11 12, cos63c k) + cos63c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_12
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 13 - ((-99439/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_14 : ((656597/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos63c k)
      = (∑ k ∈ Finset.Icc 11 13, cos63c k) + cos63c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_13
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 14 - ((-242607/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_15 : ((1229127/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos63c k)
      = (∑ k ∈ Finset.Icc 11 14, cos63c k) + cos63c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_14
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 15 - ((57257/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_16 : ((307723/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos63c k)
      = (∑ k ∈ Finset.Icc 11 15, cos63c k) + cos63c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_15
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 16 - ((38691/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_17 : ((175301/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos63c k)
      = (∑ k ∈ Finset.Icc 11 16, cos63c k) + cos63c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_16
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 17 - ((-837371/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_18 : ((1694097/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos63c k)
      = (∑ k ∈ Finset.Icc 11 17, cos63c k) + cos63c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_17
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 18 - ((992933/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_19 : ((704651/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos63c k)
      = (∑ k ∈ Finset.Icc 11 18, cos63c k) + cos63c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_18
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 19 - ((-494703/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_20 : ((26203/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos63c k)
      = (∑ k ∈ Finset.Icc 11 19, cos63c k) + cos63c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_19
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 20 - ((972381/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_21 : ((690991/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos63c k)
      = (∑ k ∈ Finset.Icc 11 20, cos63c k) + cos63c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_20
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 21 - ((-985961/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_22 : ((211253/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos63c k)
      = (∑ k ∈ Finset.Icc 11 21, cos63c k) + cos63c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_21
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 22 - ((999073/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_23 : ((381443/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos63c k)
      = (∑ k ∈ Finset.Icc 11 22, cos63c k) + cos63c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_22
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 23 - ((-463549/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_24 : ((713461/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos63c k)
      = (∑ k ∈ Finset.Icc 11 23, cos63c k) + cos63c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_23
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 24 - ((166019/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_25 : ((1271069/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos63c k)
      = (∑ k ∈ Finset.Icc 11 24, cos63c k) + cos63c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_24
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 25 - ((-155813/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_26 : ((389579/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos63c k)
      = (∑ k ∈ Finset.Icc 11 25, cos63c k) + cos63c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_25
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 26 - ((-491871/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_27 : ((1736613/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos63c k)
      = (∑ k ∈ Finset.Icc 11 26, cos63c k) + cos63c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_26
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 27 - ((191499/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_28 : ((222041/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos63c k)
      = (∑ k ∈ Finset.Icc 11 27, cos63c k) + cos63c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_27
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 28 - ((-848409/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_29 : ((194033/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos63c k)
      = (∑ k ∈ Finset.Icc 11 28, cos63c k) + cos63c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_28
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 29 - ((82041/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_30 : ((88397/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos63c k)
      = (∑ k ∈ Finset.Icc 11 29, cos63c k) + cos63c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_29
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 30 - ((159563/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_31 : ((858393/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos63c k)
      = (∑ k ∈ Finset.Icc 11 30, cos63c k) + cos63c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_30
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 31 - ((-909507/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_32 : ((34361/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos63c k)
      = (∑ k ∈ Finset.Icc 11 31, cos63c k) + cos63c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_31
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 32 - ((21/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_33 : ((1791857/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos63c k)
      = (∑ k ∈ Finset.Icc 11 32, cos63c k) + cos63c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_32
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 33 - ((116609/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_34 : ((232849/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos63c k)
      = (∑ k ∈ Finset.Icc 11 33, cos63c k) + cos63c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_33
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 34 - ((-156893/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_35 : ((569461/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos63c k)
      = (∑ k ∈ Finset.Icc 11 34, cos63c k) + cos63c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_34
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 35 - ((-74343/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_36 : ((1477141/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos63c k)
      = (∑ k ∈ Finset.Icc 11 35, cos63c k) + cos63c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_35
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 36 - ((22693/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_37 : ((1751187/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos63c k)
      = (∑ k ∈ Finset.Icc 11 36, cos63c k) + cos63c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_36
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 37 - ((137043/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_38 : ((382641/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos63c k)
      = (∑ k ∈ Finset.Icc 11 37, cos63c k) + cos63c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_37
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 38 - ((-197173/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_39 : ((331373/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos63c k)
      = (∑ k ∈ Finset.Icc 11 38, cos63c k) + cos63c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_38
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 39 - ((-3203/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_40 : ((165963/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos63c k)
      = (∑ k ∈ Finset.Icc 11 39, cos63c k) + cos63c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_39
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 40 - ((249231/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_41 : ((876533/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos63c k)
      = (∑ k ∈ Finset.Icc 11 40, cos63c k) + cos63c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_40
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 41 - ((23369/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_42 : ((763703/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos63c k)
      = (∑ k ∈ Finset.Icc 11 41, cos63c k) + cos63c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_41
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 42 - ((-989323/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_43 : ((132793/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos63c k)
      = (∑ k ∈ Finset.Icc 11 42, cos63c k) + cos63c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_42
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 43 - ((-232491/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_44 : ((91753/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos63c k)
      = (∑ k ∈ Finset.Icc 11 43, cos63c k) + cos63c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_43
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 44 - ((234229/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_45 : ((979009/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos63c k)
      = (∑ k ∈ Finset.Icc 11 44, cos63c k) + cos63c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_44
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 45 - ((49001/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_46 : ((238399/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos63c k)
      = (∑ k ∈ Finset.Icc 11 45, cos63c k) + cos63c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_45
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 46 - ((-765983/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_47 : ((199961/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos63c k)
      = (∑ k ∈ Finset.Icc 11 46, cos63c k) + cos63c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_46
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 47 - ((-792033/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_48 : ((400269/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos63c k)
      = (∑ k ∈ Finset.Icc 11 47, cos63c k) + cos63c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_47
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 48 - ((25041/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_49 : ((1790651/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos63c k)
      = (∑ k ∈ Finset.Icc 11 48, cos63c k) + cos63c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_48
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 49 - ((990153/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_50 : ((973767/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos63c k)
      = (∑ k ∈ Finset.Icc 11 49, cos63c k) + cos63c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_49
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 50 - ((156923/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_51 : ((1060871/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos63c k)
      = (∑ k ∈ Finset.Icc 11 50, cos63c k) + cos63c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_50
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 51 - ((-886623/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_52 : ((162037/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos63c k)
      = (∑ k ∈ Finset.Icc 11 51, cos63c k) + cos63c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_51
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 52 - ((-736757/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_53 : ((687303/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos63c k)
      = (∑ k ∈ Finset.Icc 11 52, cos63c k) + cos63c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_52
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 53 - ((363269/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_54 : ((843517/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos63c k)
      = (∑ k ∈ Finset.Icc 11 53, cos63c k) + cos63c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_53
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 54 - ((999771/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_55 : ((2109509/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos63c k)
      = (∑ k ∈ Finset.Icc 11 54, cos63c k) + cos63c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_54
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 55 - ((84503/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_56 : ((1466057/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos63c k)
      = (∑ k ∈ Finset.Icc 11 55, cos63c k) + cos63c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_55
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 56 - ((-160853/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_57 : ((495451/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos63c k)
      = (∑ k ∈ Finset.Icc 11 56, cos63c k) + cos63c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_56
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 57 - ((-485283/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_58 : ((33199/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos63c k)
      = (∑ k ∈ Finset.Icc 11 57, cos63c k) + cos63c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_57
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 58 - ((-229819/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_59 : ((1013561/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos63c k)
      = (∑ k ∈ Finset.Icc 11 58, cos63c k) + cos63c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_58
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 59 - ((748009/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_60 : ((1958551/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos63c k)
      = (∑ k ∈ Finset.Icc 11 59, cos63c k) + cos63c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_59
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 60 - ((94503/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_61 : ((2153593/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos63c k)
      = (∑ k ∈ Finset.Icc 11 60, cos63c k) + cos63c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_60
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 61 - ((97541/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_62 : ((354231/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos63c k)
      = (∑ k ∈ Finset.Icc 11 61, cos63c k) + cos63c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_61
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 62 - ((-736629/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_63 : ((451869/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos63c k)
      = (∑ k ∈ Finset.Icc 11 62, cos63c k) + cos63c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_62
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 63 - ((-193003/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_64 : ((143579/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos63c k)
      = (∑ k ∈ Finset.Icc 11 63, cos63c k) + cos63c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_63
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 64 - ((-1233/4000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_65 : ((759347/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos63c k)
      = (∑ k ∈ Finset.Icc 11 64, cos63c k) + cos63c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_64
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 65 - ((9622/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_66 : ((27466/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos63c k)
      = (∑ k ∈ Finset.Icc 11 65, cos63c k) + cos63c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_65
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 66 - ((998517/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_67 : ((2296527/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos63c k)
      = (∑ k ∈ Finset.Icc 11 66, cos63c k) + cos63c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_66
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 67 - ((538743/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_68 : ((1940093/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos63c k)
      = (∑ k ∈ Finset.Icc 11 67, cos63c k) + cos63c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_67
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 68 - ((-178197/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_69 : ((980861/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos63c k)
      = (∑ k ∈ Finset.Icc 11 68, cos63c k) + cos63c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_68
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 69 - ((-119899/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_70 : ((166841/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos63c k)
      = (∑ k ∈ Finset.Icc 11 69, cos63c k) + cos63c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_69
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 70 - ((-40699/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_71 : ((109493/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos63c k)
      = (∑ k ∈ Finset.Icc 11 70, cos63c k) + cos63c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_70
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 71 - ((-14327/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_72 : ((421591/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos63c k)
      = (∑ k ∈ Finset.Icc 11 71, cos63c k) + cos63c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_71
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 72 - ((733729/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_73 : ((28683/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos63c k)
      = (∑ k ∈ Finset.Icc 11 72, cos63c k) + cos63c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_72
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 73 - ((99257/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_74 : ((478683/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos63c k)
      = (∑ k ∈ Finset.Icc 11 73, cos63c k) + cos63c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_73
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 74 - ((557743/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_75 : ((214211/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos63c k)
      = (∑ k ∈ Finset.Icc 11 74, cos63c k) + cos63c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_74
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 75 - ((-50253/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_76 : ((157021/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos63c k)
      = (∑ k ∈ Finset.Icc 11 75, cos63c k) + cos63c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_75
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 76 - ((-442951/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_77 : ((39221/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos63c k)
      = (∑ k ∈ Finset.Icc 11 76, cos63c k) + cos63c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_76
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 77 - ((-23559/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_78 : ((-45509/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos63c k)
      = (∑ k ∈ Finset.Icc 11 77, cos63c k) + cos63c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_77
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 78 - ((-202373/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_79 : ((57059/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos63c k)
      = (∑ k ∈ Finset.Icc 11 78, cos63c k) + cos63c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_78
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 79 - ((376353/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_80 : ((60461/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos63c k)
      = (∑ k ∈ Finset.Icc 11 79, cos63c k) + cos63c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_79
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 80 - ((184793/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_81 : ((426807/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos63c k)
      = (∑ k ∈ Finset.Icc 11 80, cos63c k) + cos63c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_80
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 81 - ((184971/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_82 : ((2530437/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos63c k)
      = (∑ k ∈ Finset.Icc 11 81, cos63c k) + cos63c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_81
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 82 - ((198221/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_83 : ((1090931/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos63c k)
      = (∑ k ∈ Finset.Icc 11 82, cos63c k) + cos63c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_82
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 83 - ((-69707/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_84 : ((1285897/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos63c k)
      = (∑ k ∈ Finset.Icc 11 83, cos63c k) + cos63c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_83
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 84 - ((-35837/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_85 : ((13051/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos63c k)
      = (∑ k ∈ Finset.Icc 11 84, cos63c k) + cos63c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_84
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 85 - ((-479791/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_86 : ((-12207/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos63c k)
      = (∑ k ∈ Finset.Icc 11 85, cos63c k) + cos63c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_85
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 86 - ((-521547/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_87 : ((-2081/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos63c k)
      = (∑ k ∈ Finset.Icc 11 86, cos63c k) + cos63c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_86
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 87 - ((11169/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_88 : ((383219/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos63c k)
      = (∑ k ∈ Finset.Icc 11 87, cos63c k) + cos63c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_87
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 88 - ((391563/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_89 : ((27587/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos63c k)
      = (∑ k ∈ Finset.Icc 11 88, cos63c k) + cos63c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_88
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 89 - ((99917/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_90 : ((2500839/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos63c k)
      = (∑ k ∈ Finset.Icc 11 89, cos63c k) + cos63c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_89
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 90 - ((735311/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_91 : ((131521/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos63c k)
      = (∑ k ∈ Finset.Icc 11 90, cos63c k) + cos63c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_90
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 91 - ((129621/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_92 : ((2100427/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos63c k)
      = (∑ k ∈ Finset.Icc 11 91, cos63c k) + cos63c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_91
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 92 - ((-529953/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_93 : ((577361/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos63c k)
      = (∑ k ∈ Finset.Icc 11 92, cos63c k) + cos63c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_92
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 93 - ((-189133/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_94 : ((212811/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos63c k)
      = (∑ k ∈ Finset.Icc 11 93, cos63c k) + cos63c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_93
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 94 - ((-941871/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_95 : ((-39959/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos63c k)
      = (∑ k ∈ Finset.Icc 11 94, cos63c k) + cos63c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_94
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 95 - ((-532443/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_96 : ((-110831/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos63c k)
      = (∑ k ∈ Finset.Icc 11 95, cos63c k) + cos63c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_95
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 96 - ((1961/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_97 : ((92143/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos63c k)
      = (∑ k ∈ Finset.Icc 11 96, cos63c k) + cos63c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_96
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 97 - ((682417/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_98 : ((1445649/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos63c k)
      = (∑ k ∈ Finset.Icc 11 97, cos63c k) + cos63c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_97
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 98 - ((492487/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_99 : ((233897/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos63c k)
      = (∑ k ∈ Finset.Icc 11 98, cos63c k) + cos63c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_98
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 99 - ((893361/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum63_100 : ((2793241/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos63c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos63c k)
      = (∑ k ∈ Finset.Icc 11 99, cos63c k) + cos63c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos63c
    simpa using h
  have hprev := psum63_99
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos63c 100 - ((454311/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos63_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

/-- **The Abel floor at `t = 63`.** -/
theorem psum63_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 100 →
    ((-39959/125000 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos63c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum63_11
  · exact le_trans (by norm_num) psum63_12
  · exact le_trans (by norm_num) psum63_13
  · exact le_trans (by norm_num) psum63_14
  · exact le_trans (by norm_num) psum63_15
  · exact le_trans (by norm_num) psum63_16
  · exact le_trans (by norm_num) psum63_17
  · exact le_trans (by norm_num) psum63_18
  · exact le_trans (by norm_num) psum63_19
  · exact le_trans (by norm_num) psum63_20
  · exact le_trans (by norm_num) psum63_21
  · exact le_trans (by norm_num) psum63_22
  · exact le_trans (by norm_num) psum63_23
  · exact le_trans (by norm_num) psum63_24
  · exact le_trans (by norm_num) psum63_25
  · exact le_trans (by norm_num) psum63_26
  · exact le_trans (by norm_num) psum63_27
  · exact le_trans (by norm_num) psum63_28
  · exact le_trans (by norm_num) psum63_29
  · exact le_trans (by norm_num) psum63_30
  · exact le_trans (by norm_num) psum63_31
  · exact le_trans (by norm_num) psum63_32
  · exact le_trans (by norm_num) psum63_33
  · exact le_trans (by norm_num) psum63_34
  · exact le_trans (by norm_num) psum63_35
  · exact le_trans (by norm_num) psum63_36
  · exact le_trans (by norm_num) psum63_37
  · exact le_trans (by norm_num) psum63_38
  · exact le_trans (by norm_num) psum63_39
  · exact le_trans (by norm_num) psum63_40
  · exact le_trans (by norm_num) psum63_41
  · exact le_trans (by norm_num) psum63_42
  · exact le_trans (by norm_num) psum63_43
  · exact le_trans (by norm_num) psum63_44
  · exact le_trans (by norm_num) psum63_45
  · exact le_trans (by norm_num) psum63_46
  · exact le_trans (by norm_num) psum63_47
  · exact le_trans (by norm_num) psum63_48
  · exact le_trans (by norm_num) psum63_49
  · exact le_trans (by norm_num) psum63_50
  · exact le_trans (by norm_num) psum63_51
  · exact le_trans (by norm_num) psum63_52
  · exact le_trans (by norm_num) psum63_53
  · exact le_trans (by norm_num) psum63_54
  · exact le_trans (by norm_num) psum63_55
  · exact le_trans (by norm_num) psum63_56
  · exact le_trans (by norm_num) psum63_57
  · exact le_trans (by norm_num) psum63_58
  · exact le_trans (by norm_num) psum63_59
  · exact le_trans (by norm_num) psum63_60
  · exact le_trans (by norm_num) psum63_61
  · exact le_trans (by norm_num) psum63_62
  · exact le_trans (by norm_num) psum63_63
  · exact le_trans (by norm_num) psum63_64
  · exact le_trans (by norm_num) psum63_65
  · exact le_trans (by norm_num) psum63_66
  · exact le_trans (by norm_num) psum63_67
  · exact le_trans (by norm_num) psum63_68
  · exact le_trans (by norm_num) psum63_69
  · exact le_trans (by norm_num) psum63_70
  · exact le_trans (by norm_num) psum63_71
  · exact le_trans (by norm_num) psum63_72
  · exact le_trans (by norm_num) psum63_73
  · exact le_trans (by norm_num) psum63_74
  · exact le_trans (by norm_num) psum63_75
  · exact le_trans (by norm_num) psum63_76
  · exact le_trans (by norm_num) psum63_77
  · exact le_trans (by norm_num) psum63_78
  · exact le_trans (by norm_num) psum63_79
  · exact le_trans (by norm_num) psum63_80
  · exact le_trans (by norm_num) psum63_81
  · exact le_trans (by norm_num) psum63_82
  · exact le_trans (by norm_num) psum63_83
  · exact le_trans (by norm_num) psum63_84
  · exact le_trans (by norm_num) psum63_85
  · exact le_trans (by norm_num) psum63_86
  · exact le_trans (by norm_num) psum63_87
  · exact le_trans (by norm_num) psum63_88
  · exact le_trans (by norm_num) psum63_89
  · exact le_trans (by norm_num) psum63_90
  · exact le_trans (by norm_num) psum63_91
  · exact le_trans (by norm_num) psum63_92
  · exact le_trans (by norm_num) psum63_93
  · exact le_trans (by norm_num) psum63_94
  · exact le_trans (by norm_num) psum63_95
  · exact le_trans (by norm_num) psum63_96
  · exact le_trans (by norm_num) psum63_97
  · exact le_trans (by norm_num) psum63_98
  · exact le_trans (by norm_num) psum63_99
  · exact le_trans (by norm_num) psum63_100

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum63_floor
#print axioms CriticalLinePhasor.DVP.psum63_100
end AxiomAudit
