import RequestProject.DVPCos1053o2Table

/-!
# The cosine partial-sum floor, `t = 1053/2` (N = 1000)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 1053/2` segment certificate. -/
def cos1053o2c (n : ℕ) : ℝ := Real.cos (((1053:ℕ):ℝ) * (Real.log n / 2))

theorem psum1053o2_11 : ((4547663/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos1053o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 11 - ((4548163/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum1053o2_12 : ((10786041/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos1053o2c k) + cos1053o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_11
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 12 - ((338343/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_13 : ((19836777/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos1053o2c k) + cos1053o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_12
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 13 - ((1131467/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_14 : ((13104639/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos1053o2c k) + cos1053o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_13
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 14 - ((6373501/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_15 : ((17504913/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos1053o2c k) + cos1053o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_14
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 15 - ((2200387/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_16 : ((30230469/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos1053o2c k) + cos1053o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_15
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 16 - ((-4778357/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_17 : ((10904371/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos1053o2c k) + cos1053o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_16
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 17 - ((-8420727/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_18 : ((4992417/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos1053o2c k) + cos1053o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_17
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 18 - ((3154343/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_19 : ((947039/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos1053o2c k) + cos1053o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_18
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 19 - ((-128511/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_20 : ((33524811/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos1053o2c k) + cos1053o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_19
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 20 - ((2462459/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_21 : ((20491721/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos1053o2c k) + cos1053o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_20
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 21 - ((7459631/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_22 : ((3183937/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos1053o2c k) + cos1053o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_21
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 22 - ((199211/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_23 : ((6281297/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos1053o2c k) + cos1053o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_22
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 23 - ((-21613/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_24 : ((1463941/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos1053o2c k) + cos1053o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_23
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 24 - ((-26588/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_25 : ((45339839/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos1053o2c k) + cos1053o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_24
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 25 - ((-1505273/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_26 : ((55308243/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos1053o2c k) + cos1053o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_25
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 26 - ((2492351/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_27 : ((59852499/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos1053o2c k) + cos1053o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_26
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 27 - ((568157/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_28 : ((61580777/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos1053o2c k) + cos1053o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_27
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 28 - ((864639/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_29 : ((33393889/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos1053o2c k) + cos1053o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_28
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 29 - ((5208001/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_30 : ((38392113/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos1053o2c k) + cos1053o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_29
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 30 - ((1249681/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_31 : ((614883/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos1053o2c k) + cos1053o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_30
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 31 - ((77149/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_32 : ((68362237/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos1053o2c k) + cos1053o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_31
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 32 - ((-4248569/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_33 : ((3917099/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos1053o2c k) + cos1053o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_32
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 33 - ((9980743/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_34 : ((68354721/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos1053o2c k) + cos1053o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_33
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 34 - ((-9986259/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_35 : ((9642107/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos1053o2c k) + cos1053o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_34
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 35 - ((1756627/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_36 : ((75185059/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos1053o2c k) + cos1053o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_35
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 36 - ((-1950797/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_37 : ((33168061/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos1053o2c k) + cos1053o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_36
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 37 - ((-8847937/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_38 : ((7012207/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos1053o2c k) + cos1053o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_37
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 38 - ((946737/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_39 : ((80094669/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos1053o2c k) + cos1053o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_38
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 39 - ((9973599/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_40 : ((43900611/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos1053o2c k) + cos1053o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_39
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 40 - ((7707553/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_41 : ((46055751/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos1053o2c k) + cos1053o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_40
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 41 - ((53891/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_42 : ((95301/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos1053o2c k) + cos1053o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_41
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 42 - ((1595249/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_43 : ((25028583/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos1053o2c k) + cos1053o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_42
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 43 - ((1203583/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_44 : ((27083011/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos1053o2c k) + cos1053o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_43
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 44 - ((1027339/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_45 : ((11824881/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos1053o2c k) + cos1053o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_44
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 45 - ((4958883/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_46 : ((122579299/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos1053o2c k) + cos1053o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_45
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 46 - ((4331489/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_47 : ((115437421/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos1053o2c k) + cos1053o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_46
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 47 - ((-3570439/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_48 : ((53914301/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos1053o2c k) + cos1053o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_47
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 48 - ((-7607819/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_49 : ((57656459/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos1053o2c k) + cos1053o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_48
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 49 - ((1871329/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_50 : ((29723041/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos1053o2c k) + cos1053o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_49
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 50 - ((1790123/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_51 : ((109097217/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos1053o2c k) + cos1053o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_50
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 51 - ((-9793947/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_52 : ((117374911/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos1053o2c k) + cos1053o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_51
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 52 - ((4139347/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_53 : ((56873289/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos1053o2c k) + cos1053o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_52
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 53 - ((-3627333/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_54 : ((283229/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos1053o2c k) + cos1053o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_53
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 54 - ((-226989/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_55 : ((2901699/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos1053o2c k) + cos1053o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_54
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 55 - ((34717/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_56 : ((22540013/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos1053o2c k) + cos1053o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_55
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 56 - ((-673379/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_57 : ((23010283/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos1053o2c k) + cos1053o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_56
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 57 - ((47047/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_58 : ((115355717/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos1053o2c k) + cos1053o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_57
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 58 - ((152651/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_59 : ((55479547/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos1053o2c k) + cos1053o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_58
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 59 - ((-4395623/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_60 : ((119535977/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos1053o2c k) + cos1053o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_59
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 60 - ((8577883/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_61 : ((21940121/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos1053o2c k) + cos1053o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_60
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 61 - ((-2458593/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_62 : ((57355501/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos1053o2c k) + cos1053o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_61
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 62 - ((5011397/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_63 : ((3727787/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos1053o2c k) + cos1053o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_62
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 63 - ((2289591/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_64 : ((54647731/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos1053o2c k) + cos1053o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_63
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 64 - ((-4996361/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_65 : ((22393947/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos1053o2c k) + cos1053o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_64
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 65 - ((2675273/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_66 : ((120950541/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos1053o2c k) + cos1053o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_65
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 66 - ((4490903/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_67 : ((11599241/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos1053o2c k) + cos1053o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_66
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 67 - ((-4957131/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_68 : ((107052407/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos1053o2c k) + cos1053o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_67
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 68 - ((-8939003/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_69 : ((27494749/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos1053o2c k) + cos1053o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_68
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 69 - ((2927589/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_70 : ((119976233/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos1053o2c k) + cos1053o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_69
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 70 - ((9998237/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_71 : ((61781747/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos1053o2c k) + cos1053o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_70
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 71 - ((3588261/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_72 : ((117016961/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos1053o2c k) + cos1053o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_71
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 72 - ((-6545533/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_73 : ((13386253/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos1053o2c k) + cos1053o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_72
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 73 - ((-9925937/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_74 : ((101702383/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos1053o2c k) + cos1053o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_73
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 74 - ((-5386641/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_75 : ((51918533/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos1053o2c k) + cos1053o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_74
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 75 - ((2135683/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_76 : ((111704261/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos1053o2c k) + cos1053o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_75
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 76 - ((1573639/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_77 : ((60840783/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos1053o2c k) + cos1053o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_76
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 77 - ((1995661/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_78 : ((4084641/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos1053o2c k) + cos1053o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_77
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 78 - ((4513973/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_79 : ((6858373/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos1053o2c k) + cos1053o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_78
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 79 - ((1614987/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_80 : ((7035757/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos1053o2c k) + cos1053o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_79
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 80 - ((88717/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_81 : ((70883651/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos1053o2c k) + cos1053o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_80
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 81 - ((526581/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_82 : ((141051807/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos1053o2c k) + cos1053o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_81
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 82 - ((-142899/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_83 : ((34839149/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos1053o2c k) + cos1053o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_82
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 83 - ((-1694211/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_84 : ((4295077/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos1053o2c k) + cos1053o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_83
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 84 - ((-478283/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_85 : ((136044523/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos1053o2c k) + cos1053o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_84
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 85 - ((-1396941/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_86 : ((8493401/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos1053o2c k) + cos1053o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_85
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 86 - ((-149107/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_87 : ((34424519/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos1053o2c k) + cos1053o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_86
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 87 - ((90233/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_88 : ((142023621/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos1053o2c k) + cos1053o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_87
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 88 - ((865309/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_89 : ((149065599/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos1053o2c k) + cos1053o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_88
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 89 - ((3521489/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_90 : ((158317791/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos1053o2c k) + cos1053o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_89
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 90 - ((1156649/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_91 : ((168287529/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos1053o2c k) + cos1053o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_90
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 91 - ((4985369/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_92 : ((35301673/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos1053o2c k) + cos1053o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_91
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 92 - ((2055459/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_93 : ((18016069/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos1053o2c k) + cos1053o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_92
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 93 - ((146133/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_94 : ((2772097/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos1053o2c k) + cos1053o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_93
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 94 - ((-1372741/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_95 : ((42263471/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos1053o2c k) + cos1053o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_94
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 95 - ((-2089831/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_96 : ((79615553/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos1053o2c k) + cos1053o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_95
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 96 - ((-4910889/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_97 : ((15396453/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos1053o2c k) + cos1053o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_96
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 97 - ((-658197/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_98 : ((31438127/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos1053o2c k) + cos1053o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_97
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 98 - ((645421/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_99 : ((166730331/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos1053o2c k) + cos1053o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_98
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 99 - ((1192587/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_100 : ((10903627/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos1053o2c k) + cos1053o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_99
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 100 - ((7728701/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_101 : ((43213623/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos1053o2c k) + cos1053o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_100
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 101 - ((-80127/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_102 : ((163342123/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos1053o2c k) + cos1053o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_101
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 102 - ((-9511369/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_103 : ((19576539/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos1053o2c k) + cos1053o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_102
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 103 - ((-6728811/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_104 : ((32206749/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos1053o2c k) + cos1053o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_103
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 104 - ((4422433/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_105 : ((4273639/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos1053o2c k) + cos1053o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_104
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 105 - ((1982563/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_106 : ((172399389/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos1053o2c k) + cos1053o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_105
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 106 - ((1454829/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_107 : ((40775479/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos1053o2c k) + cos1053o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_106
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 107 - ((-9296473/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_108 : ((78883241/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos1053o2c k) + cos1053o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_107
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 108 - ((-2667217/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_109 : ((41348931/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos1053o2c k) + cos1053o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_108
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 109 - ((3815121/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_110 : ((172559149/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos1053o2c k) + cos1053o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_109
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 110 - ((286577/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_111 : ((82983191/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos1053o2c k) + cos1053o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_110
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 111 - ((-6591767/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_112 : ((31676541/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos1053o2c k) + cos1053o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_111
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 112 - ((-7582677/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_113 : ((4128571/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos1053o2c k) + cos1053o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_112
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 113 - ((1352227/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_114 : ((85996319/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos1053o2c k) + cos1053o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_113
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 114 - ((3425399/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_115 : ((163974369/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos1053o2c k) + cos1053o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_114
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 115 - ((-8017269/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_116 : ((159296559/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos1053o2c k) + cos1053o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_115
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 116 - ((-467681/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_117 : ((33773501/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos1053o2c k) + cos1053o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_116
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 117 - ((4785973/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_118 : ((84743761/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos1053o2c k) + cos1053o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_117
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 118 - ((621017/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_119 : ((79850227/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos1053o2c k) + cos1053o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_118
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 119 - ((-2446517/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_120 : ((41153367/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos1053o2c k) + cos1053o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_119
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 120 - ((2457007/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_121 : ((34232259/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos1053o2c k) + cos1053o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_120
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 121 - ((6548827/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_122 : ((161716181/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos1053o2c k) + cos1053o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_121
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 122 - ((-4722057/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_123 : ((32501699/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos1053o2c k) + cos1053o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_122
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 123 - ((396657/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_124 : ((171142493/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos1053o2c k) + cos1053o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_123
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 124 - ((4317499/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_125 : ((162662217/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos1053o2c k) + cos1053o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_124
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 125 - ((-2119819/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_126 : ((162245327/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos1053o2c k) + cos1053o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_125
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 126 - ((-41589/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_127 : ((170977853/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos1053o2c k) + cos1053o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_126
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 127 - ((4366763/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_128 : ((40525687/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos1053o2c k) + cos1053o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_127
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 128 - ((-1774821/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_129 : ((163457177/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos1053o2c k) + cos1053o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_128
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 129 - ((1355429/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_130 : ((6821847/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos1053o2c k) + cos1053o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_129
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 130 - ((3544999/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_131 : ((160605841/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos1053o2c k) + cos1053o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_130
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 131 - ((-4969667/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_132 : ((6649509/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos1053o2c k) + cos1053o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_131
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 132 - ((1408221/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_133 : ((168552003/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos1053o2c k) + cos1053o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_132
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 133 - ((1157639/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_134 : ((79973939/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos1053o2c k) + cos1053o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_133
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 134 - ((-2753/3200 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_135 : ((33933001/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos1053o2c k) + cos1053o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_134
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 135 - ((9718127/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_136 : ((32822121/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos1053o2c k) + cos1053o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_135
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 136 - ((-27767/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_137 : ((16284473/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos1053o2c k) + cos1053o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_136
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 137 - ((-10119/80000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_138 : ((8505813/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos1053o2c k) + cos1053o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_137
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 138 - ((727253/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_139 : ((10010117/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos1053o2c k) + cos1053o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_138
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 139 - ((-2488347/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_140 : ((10547393/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos1053o2c k) + cos1053o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_139
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 140 - ((1074677/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_141 : ((164597261/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos1053o2c k) + cos1053o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_140
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 141 - ((-4160027/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_142 : ((163099477/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos1053o2c k) + cos1053o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_141
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 142 - ((-93549/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_143 : ((169566749/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos1053o2c k) + cos1053o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_142
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 143 - ((404267/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_144 : ((160138217/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos1053o2c k) + cos1053o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_143
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 144 - ((-2356883/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_145 : ((170006209/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos1053o2c k) + cos1053o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_144
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 145 - ((154203/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_146 : ((32395699/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos1053o2c k) + cos1053o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_145
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 146 - ((-4013357/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_147 : ((41647751/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos1053o2c k) + cos1053o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_146
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 147 - ((4613509/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_148 : ((33214851/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos1053o2c k) + cos1053o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_147
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 148 - ((-515749/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_149 : ((40655639/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos1053o2c k) + cos1053o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_148
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 149 - ((-3450699/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_150 : ((84654157/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos1053o2c k) + cos1053o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_149
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 150 - ((3343379/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_151 : ((6417787/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos1053o2c k) + cos1053o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_150
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 151 - ((-8862639/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_152 : ((34066899/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos1053o2c k) + cos1053o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_151
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 152 - ((494541/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_153 : ((160466003/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos1053o2c k) + cos1053o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_152
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 153 - ((-2466873/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_154 : ((10591469/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos1053o2c k) + cos1053o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_153
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 154 - ((8998501/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_155 : ((161928309/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos1053o2c k) + cos1053o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_154
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 155 - ((-1506839/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_156 : ((83823773/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos1053o2c k) + cos1053o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_155
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 156 - ((5720237/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_157 : ((40969649/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos1053o2c k) + cos1053o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_156
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 157 - ((-75359/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_158 : ((10357361/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos1053o2c k) + cos1053o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_157
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 158 - ((92009/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_159 : ((8283403/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos1053o2c k) + cos1053o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_158
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 159 - ((-12179/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_160 : ((32825679/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos1053o2c k) + cos1053o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_159
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 160 - ((-307733/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_161 : ((41754501/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos1053o2c k) + cos1053o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_160
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 161 - ((2890609/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_162 : ((163014949/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos1053o2c k) + cos1053o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_161
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 162 - ((-800411/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_163 : ((10493579/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos1053o2c k) + cos1053o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_162
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 163 - ((976663/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_164 : ((162342933/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos1053o2c k) + cos1053o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_163
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 164 - ((-5553331/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_165 : ((10523499/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos1053o2c k) + cos1053o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_164
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 165 - ((6034051/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_166 : ((162029357/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos1053o2c k) + cos1053o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_165
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 166 - ((-6345627/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_167 : ((84265991/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos1053o2c k) + cos1053o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_166
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 167 - ((52029/80000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_168 : ((81007359/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos1053o2c k) + cos1053o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_167
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 168 - ((-814533/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_169 : ((168400707/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos1053o2c k) + cos1053o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_168
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 169 - ((6386989/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_170 : ((32457811/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos1053o2c k) + cos1053o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_169
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 170 - ((-1527663/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_171 : ((167965703/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos1053o2c k) + cos1053o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_170
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 171 - ((354853/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_172 : ((162890709/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos1053o2c k) + cos1053o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_171
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 172 - ((-2536997/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_173 : ((1044837/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos1053o2c k) + cos1053o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_172
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 173 - ((4284211/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_174 : ((163878239/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos1053o2c k) + cos1053o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_173
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 174 - ((-3294681/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_175 : ((165975147/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos1053o2c k) + cos1053o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_174
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 175 - ((524477/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_176 : ((165277059/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos1053o2c k) + cos1053o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_175
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 176 - ((-5446/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_177 : ((164389389/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos1053o2c k) + cos1053o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_176
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 177 - ((-88667/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_178 : ((166999573/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos1053o2c k) + cos1053o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_177
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 178 - ((163199/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_179 : ((162593513/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos1053o2c k) + cos1053o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_178
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 179 - ((-220253/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_180 : ((8438007/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos1053o2c k) + cos1053o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_179
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 180 - ((6167627/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_181 : ((6439713/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos1053o2c k) + cos1053o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_180
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 181 - ((-1553263/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_182 : ((170036327/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos1053o2c k) + cos1053o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_181
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 182 - ((4522251/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_183 : ((160204261/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos1053o2c k) + cos1053o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_182
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 183 - ((-4915533/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_184 : ((21270537/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos1053o2c k) + cos1053o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_183
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 184 - ((1992207/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_185 : ((40215671/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos1053o2c k) + cos1053o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_184
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 185 - ((-2325153/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_186 : ((168640219/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos1053o2c k) + cos1053o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_185
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 186 - ((1555707/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_187 : ((163219823/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos1053o2c k) + cos1053o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_186
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 187 - ((-1354849/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_188 : ((41396857/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos1053o2c k) + cos1053o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_187
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 188 - ((473721/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_189 : ((33335499/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos1053o2c k) + cos1053o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_188
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 189 - ((1091067/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_190 : ((40531169/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos1053o2c k) + cos1053o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_189
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 190 - ((-4551819/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_191 : ((21204857/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos1053o2c k) + cos1053o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_190
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 191 - ((375759/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_192 : ((160171531/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos1053o2c k) + cos1053o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_191
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 192 - ((-378653/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_193 : ((21267481/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos1053o2c k) + cos1053o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_192
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 193 - ((9969317/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_194 : ((161358219/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos1053o2c k) + cos1053o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_193
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 194 - ((-8780629/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_195 : ((167306319/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos1053o2c k) + cos1053o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_194
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 195 - ((59491/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_196 : ((4135747/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos1053o2c k) + cos1053o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_195
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 196 - ((-1875439/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_197 : ((81363827/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos1053o2c k) + cos1053o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_196
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 197 - ((-1350613/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_198 : ((42384453/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos1053o2c k) + cos1053o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_197
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 198 - ((3405579/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_199 : ((160083931/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos1053o2c k) + cos1053o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_198
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 199 - ((-9452881/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_200 : ((84969227/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos1053o2c k) + cos1053o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_199
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 200 - ((9855523/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_201 : ((162198409/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos1053o2c k) + cos1053o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_200
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 201 - ((-1547809/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_202 : ((165685053/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos1053o2c k) + cos1053o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_201
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 202 - ((871911/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_203 : ((41881679/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos1053o2c k) + cos1053o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_202
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 203 - ((1842663/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_204 : ((6431403/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos1053o2c k) + cos1053o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_203
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 204 - ((-6740641/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_205 : ((1363499/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos1053o2c k) + cos1053o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_204
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 205 - ((96533/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_206 : ((40232449/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos1053o2c k) + cos1053o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_205
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 206 - ((-9506579/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_207 : ((83543339/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos1053o2c k) + cos1053o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_206
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 207 - ((3078941/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_208 : ((41623619/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos1053o2c k) + cos1053o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_207
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 208 - ((-295601/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_209 : ((16120503/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos1053o2c k) + cos1053o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_208
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 209 - ((-2644223/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_210 : ((170471611/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos1053o2c k) + cos1053o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_209
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 210 - ((9267581/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_211 : ((160794721/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos1053o2c k) + cos1053o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_210
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 211 - ((-967589/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_212 : ((41737641/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos1053o2c k) + cos1053o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_211
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 212 - ((6156843/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_213 : ((166956387/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos1053o2c k) + cos1053o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_212
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 213 - ((6823/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_214 : ((160697037/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos1053o2c k) + cos1053o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_213
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 214 - ((-125167/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_215 : ((85240717/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos1053o2c k) + cos1053o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_214
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 215 - ((9785397/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_216 : ((40415309/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos1053o2c k) + cos1053o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_215
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 216 - ((-4409599/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_217 : ((82639023/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos1053o2c k) + cos1053o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_216
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 217 - ((361781/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_218 : ((168712843/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos1053o2c k) + cos1053o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_217
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 218 - ((3435797/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_219 : ((39969909/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos1053o2c k) + cos1053o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_218
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 219 - ((-8832207/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_220 : ((84777819/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos1053o2c k) + cos1053o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_219
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 220 - ((4838501/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_221 : ((164224719/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos1053o2c k) + cos1053o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_220
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 221 - ((-5329919/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_222 : ((32442461/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos1053o2c k) + cos1053o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_221
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 222 - ((-1005707/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_223 : ((170504083/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos1053o2c k) + cos1053o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_222
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 223 - ((4146389/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_224 : ((160688543/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos1053o2c k) + cos1053o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_223
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 224 - ((-490727/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_225 : ((166180773/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos1053o2c k) + cos1053o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_224
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 225 - ((549323/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_226 : ((168413257/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos1053o2c k) + cos1053o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_225
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 226 - ((558371/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_227 : ((39944127/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos1053o2c k) + cos1053o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_226
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 227 - ((-8635749/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_228 : ((42333081/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos1053o2c k) + cos1053o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_227
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 228 - ((597301/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_229 : ((165121317/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos1053o2c k) + cos1053o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_228
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 229 - ((-4210007/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_230 : ((80553703/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos1053o2c k) + cos1053o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_229
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 230 - ((-4012911/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_231 : ((85329227/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos1053o2c k) + cos1053o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_230
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 231 - ((597003/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_232 : ((81110819/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos1053o2c k) + cos1053o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_231
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 232 - ((-1054477/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_233 : ((163485787/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos1053o2c k) + cos1053o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_232
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 233 - ((1265149/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_234 : ((170373249/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos1053o2c k) + cos1053o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_233
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 234 - ((3444231/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_235 : ((80204383/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos1053o2c k) + cos1053o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_234
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 235 - ((-9963483/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_236 : ((165882941/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos1053o2c k) + cos1053o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_235
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 236 - ((219007/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_237 : ((169179057/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos1053o2c k) + cos1053o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_236
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 237 - ((824279/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_238 : ((6386193/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos1053o2c k) + cos1053o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_237
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 238 - ((-297601/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_239 : ((167769321/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos1053o2c k) + cos1053o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_238
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 239 - ((1014437/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_240 : ((167732773/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos1053o2c k) + cos1053o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_239
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 240 - ((-8887/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_241 : ((39901077/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos1053o2c k) + cos1053o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_240
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 241 - ((-1625493/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_242 : ((42258117/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos1053o2c k) + cos1053o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_241
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 242 - ((235729/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_243 : ((8322639/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos1053o2c k) + cos1053o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_242
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 243 - ((-20146/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_244 : ((79934433/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos1053o2c k) + cos1053o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_243
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 244 - ((-3291457/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_245 : ((3395511/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos1053o2c k) + cos1053o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_244
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 245 - ((2476921/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_246 : ((6621389/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos1053o2c k) + cos1053o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_245
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 246 - ((-169593/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_247 : ((40038881/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos1053o2c k) + cos1053o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_246
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 247 - ((-5378201/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_248 : ((170153877/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos1053o2c k) + cos1053o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_247
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 248 - ((9999353/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_249 : ((8252071/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos1053o2c k) + cos1053o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_248
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 249 - ((-5111457/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_250 : ((160291769/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos1053o2c k) + cos1053o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_249
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 250 - ((-4748651/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_251 : ((2660691/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 251, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 251, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 250, cos1053o2c k) + cos1053o2c 251 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 250) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_250
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 251 - ((1998691/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_251).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_252 : ((82490761/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 252, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 252, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 251, cos1053o2c k) + cos1053o2c 252 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 251) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_251
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 252 - ((-2650851/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_252).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_253 : ((20025873/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 253, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 253, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 252, cos1053o2c k) + cos1053o2c 253 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 252) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_252
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 253 - ((-2386769/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_253).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_254 : ((170205623/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 254, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 254, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 253, cos1053o2c k) + cos1053o2c 254 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 253) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_253
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 254 - ((9999639/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_254).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_255 : ((165353599/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 255, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 255, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 254, cos1053o2c k) + cos1053o2c 255 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 254) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_254
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 255 - ((-303189/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_255).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_256 : ((159918917/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 256, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 256, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 255, cos1053o2c k) + cos1053o2c 256 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 255) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_255
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 256 - ((-2716841/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_256).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_257 : ((21234381/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 257, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 257, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 256, cos1053o2c k) + cos1053o2c 257 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 256) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_256
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 257 - ((9957131/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_257).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_258 : ((166153341/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 258, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 258, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 257, cos1053o2c k) + cos1053o2c 258 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 257) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_257
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 258 - ((-3720707/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_258).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_259 : ((79765779/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 259, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 259, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 258, cos1053o2c k) + cos1053o2c 259 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 258) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_258
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 259 - ((-6620783/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_259).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_260 : ((84590133/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 260, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 260, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 259, cos1053o2c k) + cos1053o2c 260 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 259) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_259
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 260 - ((2412427/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_260).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_261 : ((10458819/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 261, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 261, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 260, cos1053o2c k) + cos1053o2c 261 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 260) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_260
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 261 - ((-919081/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_261).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_262 : ((159244889/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 262, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 262, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 261, cos1053o2c k) + cos1053o2c 262 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 261) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_261
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 262 - ((-1619043/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_262).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_263 : ((83989491/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 263, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 263, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 262, cos1053o2c k) + cos1053o2c 263 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 262) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_262
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 263 - ((8735093/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_263).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_264 : ((84394083/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 264, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 264, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 263, cos1053o2c k) + cos1053o2c 264 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 263) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_263
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 264 - ((101273/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_264).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_265 : ((39838769/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 265, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 265, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 264, cos1053o2c k) + cos1053o2c 265 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 264) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_264
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 265 - ((-943209/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_265).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_266 : ((41544263/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 266, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 266, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 265, cos1053o2c k) + cos1053o2c 266 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 265) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_265
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 266 - ((106609/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_266).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_267 : ((4255223/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 267, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 267, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 266, cos1053o2c k) + cos1053o2c 267 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 266) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_266
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 267 - ((1008217/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_267).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_268 : ((40052371/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 268, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 268, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 267, cos1053o2c k) + cos1053o2c 268 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 267) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_267
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 268 - ((-2499609/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_268).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_269 : ((1310777/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 269, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 269, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 268, cos1053o2c k) + cos1053o2c 269 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 268) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_268
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 269 - ((3638641/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_269).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_270 : ((171127143/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 270, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 270, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 269, cos1053o2c k) + cos1053o2c 270 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 269) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_269
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 270 - ((3640509/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_270).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_271 : ((40519579/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 271, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 271, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 270, cos1053o2c k) + cos1053o2c 271 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 270) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_270
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 271 - ((-9047827/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_271).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_272 : ((80681369/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 272, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 272, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 271, cos1053o2c k) + cos1053o2c 272 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 271) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_271
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 272 - ((-357289/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_272).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_273 : ((213681/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 273, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 273, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 272, cos1053o2c k) + cos1053o2c 273 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 272) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_272
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 273 - ((4791531/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_273).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_274 : ((5154349/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 274, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 274, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 273, cos1053o2c k) + cos1053o2c 274 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 273) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_273
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 274 - ((-750579/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_274).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_275 : ((79730949/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 275, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 275, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 274, cos1053o2c k) + cos1053o2c 275 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 274) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_274
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 275 - ((-547627/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_275).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_276 : ((1691761/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 276, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 276, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 275, cos1053o2c k) + cos1053o2c 276 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 275) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_275
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 276 - ((4857601/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_276).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_277 : ((3364697/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 277, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 277, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 276, cos1053o2c k) + cos1053o2c 277 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 276) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_276
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 277 - ((-3761/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_277).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_278 : ((159105667/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 278, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 278, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 277, cos1053o2c k) + cos1053o2c 278 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 277) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_277
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 278 - ((-9128183/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_278).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_279 : ((41462473/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 279, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 279, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 278, cos1053o2c k) + cos1053o2c 279 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 278) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_278
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 279 - ((269809/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_279).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_280 : ((6831843/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 280, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 280, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 279, cos1053o2c k) + cos1053o2c 280 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 279) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_279
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 280 - ((4947183/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_280).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_281 : ((40254389/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 281, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 281, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 280, cos1053o2c k) + cos1053o2c 281 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 280) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_280
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 281 - ((-9777519/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_281).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_282 : ((161897491/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 282, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 282, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 281, cos1053o2c k) + cos1053o2c 282 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 281) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_281
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 282 - ((176187/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_282).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_283 : ((171178991/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 283, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 283, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 282, cos1053o2c k) + cos1053o2c 283 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 282) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_282
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 283 - ((3713/4000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_283).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_284 : ((82493889/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 284, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 284, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 283, cos1053o2c k) + cos1053o2c 284 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 283) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_283
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 284 - ((-6190213/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_284).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_285 : ((79573981/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 285, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 285, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 284, cos1053o2c k) + cos1053o2c 285 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 284) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_284
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 285 - ((-182463/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_285).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_286 : ((33708051/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 286, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 286, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 285, cos1053o2c k) + cos1053o2c 286 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 285) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_285
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 286 - ((9393293/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_286).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_287 : ((169370567/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 287, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 287, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 286, cos1053o2c k) + cos1053o2c 287 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 286) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_286
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 287 - ((51957/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_287).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_288 : ((79763121/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 288, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 288, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 287, cos1053o2c k) + cos1053o2c 288 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 287) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_287
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 288 - ((-393733/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_288).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_289 : ((40926683/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 289, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 289, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 288, cos1053o2c k) + cos1053o2c 289 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 288) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_288
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 289 - ((418149/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_289).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_290 : ((171485863/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 290, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 290, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 289, cos1053o2c k) + cos1053o2c 290 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 289) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_289
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 290 - ((7780131/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_290).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_291 : ((40880889/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 291, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 291, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 290, cos1053o2c k) + cos1053o2c 291 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 290) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_290
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 291 - ((-7961307/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_291).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_292 : ((159495161/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 292, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 292, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 291, cos1053o2c k) + cos1053o2c 292 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 291) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_291
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 292 - ((-805479/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_292).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_293 : ((2116537/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 293, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 293, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 292, cos1053o2c k) + cos1053o2c 293 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 292) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_292
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 293 - ((9828799/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_293).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_294 : ((168944691/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 294, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 294, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 293, cos1053o2c k) + cos1053o2c 294 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 293) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_293
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 294 - ((-377269/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_294).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_295 : ((159266359/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 295, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 295, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 294, cos1053o2c k) + cos1053o2c 295 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 294) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_294
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 295 - ((-2419333/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_295).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_296 : ((163755443/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 296, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 296, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 295, cos1053o2c k) + cos1053o2c 296 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 295) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_295
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 296 - ((1122521/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_296).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_297 : ((171589023/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 297, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 297, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 296, cos1053o2c k) + cos1053o2c 297 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 296) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_296
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 297 - ((391729/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_297).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_298 : ((163947871/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 298, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 298, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 297, cos1053o2c k) + cos1053o2c 298 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 297) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_297
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 298 - ((-955019/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_298).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_299 : ((159080367/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 299, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 299, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 298, cos1053o2c k) + cos1053o2c 299 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 298) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_298
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 299 - ((-608313/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_299).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_300 : ((84284101/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 300, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 300, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 299, cos1053o2c k) + cos1053o2c 300 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 299) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_299
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 300 - ((1897767/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_300).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_301 : ((33992183/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 301, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 301, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 300, cos1053o2c k) + cos1053o2c 301 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 300) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_300
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 301 - ((1393713/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_301).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_302 : ((159966277/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 302, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 302, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 301, cos1053o2c k) + cos1053o2c 302 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 301) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_301
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 302 - ((-4996819/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_302).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_303 : ((81002333/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 303, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 303, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 302, cos1053o2c k) + cos1053o2c 303 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 302) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_302
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 303 - ((2039389/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_303).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_304 : ((85664647/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 304, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 304, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 303, cos1053o2c k) + cos1053o2c 304 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 303) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_303
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 304 - ((2331407/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_304).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_305 : ((166293873/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 305, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 305, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 304, cos1053o2c k) + cos1053o2c 305 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 304) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_304
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 305 - ((-5034421/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_305).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_306 : ((158518571/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 306, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 306, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 305, cos1053o2c k) + cos1053o2c 306 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 305) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_305
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 306 - ((-3887151/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_306).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_307 : ((82938943/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 307, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 307, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 306, cos1053o2c k) + cos1053o2c 307 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 306) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_306
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 307 - ((1472063/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_307).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_308 : ((5360677/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 308, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 308, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 307, cos1053o2c k) + cos1053o2c 308 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 307) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_307
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 308 - ((2832389/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_308).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_309 : ((162608609/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 309, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 309, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 308, cos1053o2c k) + cos1053o2c 309 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 308) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_308
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 309 - ((-1786411/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_309).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_310 : ((159310033/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 310, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 310, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 309, cos1053o2c k) + cos1053o2c 310 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 309) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_309
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 310 - ((-412197/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_310).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_311 : ((3381739/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 311, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 311, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 310, cos1053o2c k) + cos1053o2c 311 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 310) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_310
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 311 - ((9777917/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_311).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_312 : ((2656287/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 312, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 312, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 311, cos1053o2c k) + cos1053o2c 312 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 311) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_311
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 312 - ((458209/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_312).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_313 : ((160003839/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 313, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 313, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 312, cos1053o2c k) + cos1053o2c 313 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 312) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_312
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 313 - ((-9997529/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_313).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_314 : ((161307771/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 314, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 314, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 313, cos1053o2c k) + cos1053o2c 314 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 313) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_313
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 314 - ((326233/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_314).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_315 : ((34206763/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 315, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 315, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 314, cos1053o2c k) + cos1053o2c 315 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 314) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_314
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 315 - ((2431761/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_315).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_316 : ((167771767/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 316, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 316, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 315, cos1053o2c k) + cos1053o2c 316 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 315) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_315
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 316 - ((-407631/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_316).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_317 : ((31731961/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 317, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 317, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 316, cos1053o2c k) + cos1053o2c 317 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 316) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_316
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 317 - ((-4555481/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_317).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_318 : ((20445111/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 318, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 318, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 317, cos1053o2c k) + cos1053o2c 318 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 317) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_317
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 318 - ((4902083/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_318).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_319 : ((85921703/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 319, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 319, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 318, cos1053o2c k) + cos1053o2c 319 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 318) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_318
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 319 - ((4141759/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_319).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_320 : ((165619383/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 320, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 320, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 319, cos1053o2c k) + cos1053o2c 320 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 319) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_319
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 320 - ((-6223023/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_320).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_321 : ((15825849/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 321, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 321, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 320, cos1053o2c k) + cos1053o2c 321 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 320) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_320
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 321 - ((-7359893/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_321).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_322 : ((827519/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 322, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 322, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 321, cos1053o2c k) + cos1053o2c 322 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 321) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_321
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 322 - ((724631/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_322).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_323 : ((171933671/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 323, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 323, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 322, cos1053o2c k) + cos1053o2c 323 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 322) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_322
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 323 - ((6430871/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_323).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_324 : ((163922489/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 324, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 324, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 323, cos1053o2c k) + cos1053o2c 324 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 323) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_323
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 324 - ((-4005091/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_324).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_325 : ((158356747/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 325, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 325, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 324, cos1053o2c k) + cos1053o2c 325 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 324) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_324
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 325 - ((-2782371/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_325).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_326 : ((41728801/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 326, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 326, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 325, cos1053o2c k) + cos1053o2c 326 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 325) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_325
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 326 - ((8559457/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_326).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_327 : ((34344589/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 327, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 327, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 326, cos1053o2c k) + cos1053o2c 327 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 326) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_326
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 327 - ((4808741/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_327).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_328 : ((162782743/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 328, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 328, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 327, cos1053o2c k) + cos1053o2c 328 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 327) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_327
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 328 - ((-4469601/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_328).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_329 : ((158587077/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 329, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 329, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 328, cos1053o2c k) + cos1053o2c 329 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 328) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_328
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 329 - ((-2097333/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_329).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_330 : ((41943507/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 330, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 330, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 329, cos1053o2c k) + cos1053o2c 330 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 329) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_329
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 330 - ((9187951/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_330).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_331 : ((42878781/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 331, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 331, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 330, cos1053o2c k) + cos1053o2c 331 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 330) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_330
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 331 - ((233881/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_331).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_332 : ((162176821/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 332, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 332, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 331, cos1053o2c k) + cos1053o2c 332 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 331) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_331
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 332 - ((-9337303/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_332).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_333 : ((15871447/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 333, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 333, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 332, cos1053o2c k) + cos1053o2c 333 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 332) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_332
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 333 - ((-3461351/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_333).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_334 : ((10507651/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 334, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 334, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 333, cos1053o2c k) + cos1053o2c 334 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 333) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_333
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 334 - ((4704473/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_334).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_335 : ((171478021/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 335, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 335, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 334, cos1053o2c k) + cos1053o2c 335 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 334) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_334
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 335 - ((671321/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_335).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_336 : ((162062271/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 336, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 336, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 335, cos1053o2c k) + cos1053o2c 336 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 335) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_335
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 336 - ((-37659/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_336).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_337 : ((31726533/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 337, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 337, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 336, cos1053o2c k) + cos1053o2c 337 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 336) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_336
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 337 - ((-1714303/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_337).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_338 : ((20998481/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 338, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 338, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 337, cos1053o2c k) + cos1053o2c 338 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 337) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_337
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 338 - ((9356183/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_338).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_339 : ((85830123/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 339, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 339, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 338, cos1053o2c k) + cos1053o2c 339 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 338) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_338
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 339 - ((1836699/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_339).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_340 : ((32486733/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 340, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 340, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 339, cos1053o2c k) + cos1053o2c 340 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 339) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_339
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 340 - ((-9225581/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_340).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_341 : ((39587147/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 341, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 341, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 340, cos1053o2c k) + cos1053o2c 341 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 340) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_340
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 341 - ((-4084077/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_341).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_342 : ((167353123/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 342, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 342, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 341, cos1053o2c k) + cos1053o2c 342 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 341) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_341
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 342 - ((1801107/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_342).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_343 : ((171999423/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 343, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 343, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 342, cos1053o2c k) + cos1053o2c 343 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 342) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_342
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 343 - ((46473/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_343).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_344 : ((40831773/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 344, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 344, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 343, cos1053o2c k) + cos1053o2c 344 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 343) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_343
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 344 - ((-8671331/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_344).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_345 : ((157981639/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 345, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 345, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 344, cos1053o2c k) + cos1053o2c 345 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 344) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_344
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 345 - ((-5344453/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_345).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_346 : ((166172541/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 346, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 346, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 345, cos1053o2c k) + cos1053o2c 346 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 345) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_345
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 346 - ((4095951/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_346).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_347 : ((43079853/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 347, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 347, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 346, cos1053o2c k) + cos1053o2c 347 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 346) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_346
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 347 - ((6147871/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_347).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_348 : ((5149559/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 348, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 348, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 347, cos1053o2c k) + cos1053o2c 348 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 347) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_347
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 348 - ((-1883131/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_348).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_349 : ((31553539/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 349, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 349, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 348, cos1053o2c k) + cos1053o2c 349 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 348) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_348
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 349 - ((-7017193/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_349).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_350 : ((164425057/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 350, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 350, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 349, cos1053o2c k) + cos1053o2c 350 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 349) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_349
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 350 - ((3329181/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_350).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_351 : ((86162067/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 351, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 351, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 350, cos1053o2c k) + cos1053o2c 351 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 350) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_350
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 351 - ((7900077/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_351).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_352 : ((6671373/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 352, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 352, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 351, cos1053o2c k) + cos1053o2c 352 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 351) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_351
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 352 - ((-5538809/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_352).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_353 : ((158055147/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 353, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 353, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 352, cos1053o2c k) + cos1053o2c 353 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 352) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_352
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 353 - ((-4364089/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_353).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_354 : ((162208937/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 354, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 354, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 353, cos1053o2c k) + cos1053o2c 354 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 353) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_353
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 354 - ((415479/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_354).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_355 : ((42906507/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 355, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 355, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 354, cos1053o2c k) + cos1053o2c 355 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 354) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_354
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 355 - ((9418091/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_355).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_356 : ((169121231/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 356, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 356, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 355, cos1053o2c k) + cos1053o2c 356 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 355) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_355
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 356 - ((-2503797/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_356).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_357 : ((79623271/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 357, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 357, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 356, cos1053o2c k) + cos1053o2c 357 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 356) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_356
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 357 - ((-9873689/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_357).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_358 : ((19981943/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 358, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 358, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 357, cos1053o2c k) + cos1053o2c 358 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 357) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_357
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 358 - ((305001/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_358).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_359 : ((169846083/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 359, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 359, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 358, cos1053o2c k) + cos1053o2c 359 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 358) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_358
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 359 - ((9991539/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_359).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_360 : ((171313459/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 360, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 360, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 359, cos1053o2c k) + cos1053o2c 360 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 359) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_359
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 360 - ((183547/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_360).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_361 : ((161642693/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 361, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 361, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 360, cos1053o2c k) + cos1053o2c 361 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 360) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_360
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 361 - ((-4834883/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_361).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_362 : ((79003227/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 362, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 362, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 361, cos1053o2c k) + cos1053o2c 362 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 361) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_361
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 362 - ((-3635239/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_362).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_363 : ((33365341/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 363, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 363, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 362, cos1053o2c k) + cos1053o2c 363 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 362) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_362
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 363 - ((8821251/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_363).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_364 : ((86288801/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 364, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 364, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 363, cos1053o2c k) + cos1053o2c 364 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 363) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_363
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 364 - ((5751897/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_364).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_365 : ((165186387/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 365, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 365, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 364, cos1053o2c k) + cos1053o2c 365 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 364) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_364
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 365 - ((-1478043/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_365).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_366 : ((4923297/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 366, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 366, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 365, cos1053o2c k) + cos1053o2c 366 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 365) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_365
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 366 - ((-7639883/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_366).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_367 : ((81458123/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 367, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 367, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 366, cos1053o2c k) + cos1053o2c 367 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 366) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_366
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 367 - ((2685871/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_367).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_368 : ((43002323/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 368, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 368, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 367, cos1053o2c k) + cos1053o2c 368 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 367) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_367
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 368 - ((4547023/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_368).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_369 : ((84589183/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 369, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 369, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 368, cos1053o2c k) + cos1053o2c 369 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 368) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_368
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 369 - ((-1414963/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_369).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_370 : ((159276657/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 370, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 370, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 369, cos1053o2c k) + cos1053o2c 370 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 369) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_369
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 370 - ((-9900709/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_370).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_371 : ((159188291/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 371, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 371, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 370, cos1053o2c k) + cos1053o2c 371 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 370) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_370
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 371 - ((-43683/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_371).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_372 : ((169055873/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 372, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 372, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 371, cos1053o2c k) + cos1053o2c 372 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 371) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_371
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 372 - ((4934291/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_372).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_373 : ((172197261/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 373, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 373, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 372, cos1053o2c k) + cos1053o2c 373 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 372) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_372
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 373 - ((785597/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_373).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_374 : ((40832563/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 374, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 374, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 373, cos1053o2c k) + cos1053o2c 374 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 373) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_373
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 374 - ((-8866009/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_374).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_375 : ((39327847/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 375, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 375, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 374, cos1053o2c k) + cos1053o2c 375 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 374) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_374
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 375 - ((-752233/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_375).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_376 : ((164173363/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 376, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 376, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 375, cos1053o2c k) + cos1053o2c 376 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 375) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_375
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 376 - ((274519/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_376).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_377 : ((86257573/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 377, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 377, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 376, cos1053o2c k) + cos1053o2c 377 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 376) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_376
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 377 - ((8342783/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_377).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_378 : ((168547541/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 378, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 378, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 377, cos1053o2c k) + cos1053o2c 378 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 377) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_377
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 378 - ((-793321/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_378).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_379 : ((31761133/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 379, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 379, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 378, cos1053o2c k) + cos1053o2c 379 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 378) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_378
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 379 - ((-2435219/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_379).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_380 : ((159251281/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 380, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 380, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 379, cos1053o2c k) + cos1053o2c 380 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 379) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_379
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 380 - ((55827/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_380).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_381 : ((42287257/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 381, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 381, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 380, cos1053o2c k) + cos1053o2c 381 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 380) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_380
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 381 - ((9898747/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_381).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_382 : ((172417837/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 382, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 382, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 381, cos1053o2c k) + cos1053o2c 382 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 381) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_381
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 382 - ((3269809/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_382).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_383 : ((81888013/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 383, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 383, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 382, cos1053o2c k) + cos1053o2c 383 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 382) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_382
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 383 - ((-8640811/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_383).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_384 : ((157140907/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 384, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 384, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 383, cos1053o2c k) + cos1053o2c 384 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 383) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_383
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 384 - ((-6634119/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_384).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_385 : ((20392939/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 385, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 385, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 384, cos1053o2c k) + cos1053o2c 385 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 384) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_384
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 385 - ((1200721/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_385).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_386 : ((172194723/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 386, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 386, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 385, cos1053o2c k) + cos1053o2c 386 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 385) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_385
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 386 - ((9052211/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_386).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_387 : ((84955447/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 387, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 387, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 386, cos1053o2c k) + cos1053o2c 387 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 386) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_386
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 387 - ((-2282829/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_387).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_388 : ((3997789/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 388, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 388, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 387, cos1053o2c k) + cos1053o2c 388 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 387) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_387
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 388 - ((-4999167/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_388).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_389 : ((157950047/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 389, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 389, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 388, cos1053o2c k) + cos1053o2c 389 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 388) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_388
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 389 - ((-1960513/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_389).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_390 : ((83547299/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 390, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 390, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 389, cos1053o2c k) + cos1053o2c 390 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 389) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_389
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 390 - ((9145551/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_390).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_391 : ((6922277/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 391, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 391, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 390, cos1053o2c k) + cos1053o2c 391 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 390) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_390
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 391 - ((5963327/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_391).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_392 : ((166568627/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 392, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 392, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 391, cos1053o2c k) + cos1053o2c 392 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 391) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_391
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 392 - ((-3243649/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_392).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_393 : ((2463777/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 393, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 393, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 392, cos1053o2c k) + cos1053o2c 393 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 392) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_392
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 393 - ((-8885899/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_393).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_394 : ((80046997/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 394, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 394, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 393, cos1053o2c k) + cos1053o2c 394 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 393) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_393
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 394 - ((1206633/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_394).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_395 : ((21261589/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 395, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 395, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 394, cos1053o2c k) + cos1053o2c 395 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 394) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_394
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 395 - ((4999859/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_395).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_396 : ((172391273/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 396, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 396, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 395, cos1053o2c k) + cos1053o2c 396 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 395) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_395
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 396 - ((2299561/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_396).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_397 : ((163497327/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 397, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 397, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 396, cos1053o2c k) + cos1053o2c 397 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 396) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_396
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 397 - ((-4446473/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_397).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_398 : ((78446643/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 398, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 398, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 397, cos1053o2c k) + cos1053o2c 398 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 397) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_397
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 398 - ((-6603041/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_398).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_399 : ((162538509/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 399, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 399, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 398, cos1053o2c k) + cos1053o2c 399 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 398) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_398
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 399 - ((5646223/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_399).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_400 : ((21492659/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 400, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 400, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 399, cos1053o2c k) + cos1053o2c 400 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 399) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_399
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 400 - ((9403763/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_400).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_401 : ((171032693/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 401, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 401, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 400, cos1053o2c k) + cos1053o2c 401 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 400) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_400
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 401 - ((-907579/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_401).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_402 : ((161173507/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 402, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 402, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 401, cos1053o2c k) + cos1053o2c 402 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 401) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_401
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 402 - ((-4929093/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_402).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_403 : ((2452997/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 403, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 403, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 402, cos1053o2c k) + cos1053o2c 403 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 402) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_402
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 403 - ((-4180699/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_403).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_404 : ((82328327/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 404, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 404, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 403, cos1053o2c k) + cos1053o2c 404 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 403) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_403
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 404 - ((3832923/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_404).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_405 : ((172884527/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 405, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 405, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 404, cos1053o2c k) + cos1053o2c 405 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 404) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_404
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 405 - ((8228873/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_405).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_406 : ((169624867/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 406, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 406, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 405, cos1053o2c k) + cos1053o2c 406 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 405) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_405
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 406 - ((-162933/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_406).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_407 : ((159639723/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 407, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 407, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 406, cos1053o2c k) + cos1053o2c 407 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 406) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_406
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 407 - ((-624009/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_407).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_408 : ((78716291/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 408, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 408, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 407, cos1053o2c k) + cos1053o2c 408 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 407) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_407
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 408 - ((-2206141/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_408).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_409 : ((166186381/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 409, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 409, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 408, cos1053o2c k) + cos1053o2c 409 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 408) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_408
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 409 - ((8754799/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_409).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_410 : ((173285053/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 410, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 410, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 409, cos1053o2c k) + cos1053o2c 410 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 409) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_409
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 410 - ((887459/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_410).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_411 : ((8427499/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 411, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 411, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 410, cos1053o2c k) + cos1053o2c 411 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 410) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_410
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 411 - ((-4734073/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_411).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_412 : ((158751919/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 412, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 412, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 411, cos1053o2c k) + cos1053o2c 412 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 411) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_411
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 412 - ((-9797061/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_412).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_413 : ((157825757/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 413, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 413, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 412, cos1053o2c k) + cos1053o2c 413 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 412) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_412
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 413 - ((-462581/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_413).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_414 : ((167073249/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 414, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 414, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 413, cos1053o2c k) + cos1053o2c 414 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 413) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_413
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 414 - ((2312123/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_414).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_415 : ((173443171/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 415, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 415, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 414, cos1053o2c k) + cos1053o2c 415 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 414) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_414
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 415 - ((3185461/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_415).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_416 : ((33598403/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 416, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 416, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 415, cos1053o2c k) + cos1053o2c 416 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 415) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_415
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 416 - ((-1362539/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_416).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_417 : ((158352607/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 417, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 417, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 416, cos1053o2c k) + cos1053o2c 417 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 416) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_416
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 417 - ((-1204801/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_417).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_418 : ((157951857/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 418, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 418, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 417, cos1053o2c k) + cos1053o2c 418 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 417) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_417
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 418 - ((-1599/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_418).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_419 : ((20916907/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 419, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 419, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 418, cos1053o2c k) + cos1053o2c 419 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 418) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_418
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 419 - ((9384399/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_419).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_420 : ((21691481/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 420, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 420, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 419, cos1053o2c k) + cos1053o2c 420 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 419) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_419
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 420 - ((774699/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_420).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_421 : ((672081/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 421, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 421, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 420, cos1053o2c k) + cos1053o2c 421 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 420) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_420
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 421 - ((-2755299/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_421).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_422 : ((39590101/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 422, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 422, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 421, cos1053o2c k) + cos1053o2c 422 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 421) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_421
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 422 - ((-4829423/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_422).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_423 : ((157732641/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 423, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 423, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 422, cos1053o2c k) + cos1053o2c 423 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 422) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_422
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 423 - ((-626763/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_423).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_424 : ((166979631/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 424, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 424, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 423, cos1053o2c k) + cos1053o2c 424 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 423) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_423
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 424 - ((924799/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_424).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_425 : ((86789281/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 425, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 425, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 424, cos1053o2c k) + cos1053o2c 425 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 424) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_424
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 425 - ((6599931/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_425).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_426 : ((3372771/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 426, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 426, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 425, cos1053o2c k) + cos1053o2c 426 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 425) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_425
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 426 - ((-1234753/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_426).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_427 : ((158799577/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 427, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 427, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 426, cos1053o2c k) + cos1053o2c 427 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 426) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_426
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 427 - ((-9837973/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_427).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_428 : ((19651907/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 428, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 428, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 427, cos1053o2c k) + cos1053o2c 428 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 427) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_427
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 428 - ((-1583321/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_428).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_429 : ((82992517/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 429, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 429, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 428, cos1053o2c k) + cos1053o2c 429 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 428) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_428
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 429 - ((4385389/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_429).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_430 : ((173470367/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 430, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 430, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 429, cos1053o2c k) + cos1053o2c 430 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 429) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_429
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 430 - ((7486333/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_430).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_431 : ((5305889/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 431, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 431, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 430, cos1053o2c k) + cos1053o2c 431 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 430) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_430
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 431 - ((-3680919/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_431).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_432 : ((2496733/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 432, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 432, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 431, cos1053o2c k) + cos1053o2c 432 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 431) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_431
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 432 - ((-1249567/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_432).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_433 : ((78288467/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 433, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 433, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 432, cos1053o2c k) + cos1053o2c 433 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 432) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_432
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 433 - ((-1606489/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_433).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_434 : ((82165227/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 434, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 434, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 433, cos1053o2c k) + cos1053o2c 434 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 433) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_433
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 434 - ((193863/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_434).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_435 : ((172965733/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 435, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 435, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 434, cos1053o2c k) + cos1053o2c 435 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 434) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_434
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 435 - ((8636279/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_435).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_436 : ((171307149/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 436, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 436, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 435, cos1053o2c k) + cos1053o2c 436 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 435) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_435
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 436 - ((-103599/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_436).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_437 : ((161501747/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 437, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 437, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 436, cos1053o2c k) + cos1053o2c 437 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 436) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_436
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 437 - ((-4902201/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_437).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_438 : ((156142931/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 438, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 438, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 437, cos1053o2c k) + cos1053o2c 438 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 437) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_437
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 438 - ((-669727/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_438).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_439 : ((162075719/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 439, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 439, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 438, cos1053o2c k) + cos1053o2c 439 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 438) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_438
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 439 - ((1483447/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_439).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_440 : ((171732423/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 440, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 440, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 439, cos1053o2c k) + cos1053o2c 440 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 439) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_439
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 440 - ((1207213/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_440).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_441 : ((86430451/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 441, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 441, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 440, cos1053o2c k) + cos1053o2c 441 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 440) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_440
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 441 - ((1129479/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_441).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_442 : ((164043469/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 442, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 442, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 441, cos1053o2c k) + cos1053o2c 442 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 441) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_441
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 442 - ((-8816433/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_442).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_443 : ((156383583/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 443, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 443, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 442, cos1053o2c k) + cos1053o2c 443 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 442) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_442
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 443 - ((-3829443/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_443).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_444 : ((7973909/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 444, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 444, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 443, cos1053o2c k) + cos1053o2c 444 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 443) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_443
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 444 - ((3095597/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_444).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_445 : ((169451559/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 445, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 445, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 444, cos1053o2c k) + cos1053o2c 445 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 444) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_444
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 445 - ((9974379/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_445).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_446 : ((173895067/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 446, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 446, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 445, cos1053o2c k) + cos1053o2c 446 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 445) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_445
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 446 - ((1111127/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_446).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_447 : ((4182771/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 447, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 447, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 446, cos1053o2c k) + cos1053o2c 447 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 446) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_446
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 447 - ((-6583227/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_447).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_448 : ((1233057/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 448, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 448, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 447, cos1053o2c k) + cos1053o2c 448 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 447) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_447
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 448 - ((-592409/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_448).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_449 : ((39276357/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 449, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 449, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 448, cos1053o2c k) + cos1053o2c 449 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 448) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_448
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 449 - ((-181217/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_449).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_450 : ((166010843/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 450, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 450, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 449, cos1053o2c k) + cos1053o2c 450 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 449) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_449
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 450 - ((1781283/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_450).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_451 : ((34735919/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 451, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 451, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 450, cos1053o2c k) + cos1053o2c 451 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 450) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_450
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 451 - ((958719/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_451).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_452 : ((170800121/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 452, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 452, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 451, cos1053o2c k) + cos1053o2c 452 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 451) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_451
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 452 - ((-1439237/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_452).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_453 : ((20108183/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 453, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 453, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 452, cos1053o2c k) + cos1053o2c 453 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 452) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_452
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 453 - ((-9933657/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_453).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_454 : ((155851323/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 454, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 454, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 453, cos1053o2c k) + cos1053o2c 454 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 453) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_453
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 454 - ((-5013141/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_454).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_455 : ((32353747/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 455, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 455, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 454, cos1053o2c k) + cos1053o2c 455 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 454) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_454
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 455 - ((1479603/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_455).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_456 : ((171530139/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 456, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 456, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 455, cos1053o2c k) + cos1053o2c 456 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 455) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_455
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 456 - ((2440601/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_456).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_457 : ((173506767/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 457, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 457, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 456, cos1053o2c k) + cos1053o2c 457 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 456) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_456
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 457 - ((494407/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_457).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_458 : ((165361453/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 458, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 458, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 457, cos1053o2c k) + cos1053o2c 458 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 457) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_457
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 458 - ((-4072157/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_458).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_459 : ((156728853/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 459, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 459, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 458, cos1053o2c k) + cos1053o2c 459 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 458) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_458
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 459 - ((-21579/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_459).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_460 : ((39442177/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 460, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 460, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 459, cos1053o2c k) + cos1053o2c 460 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 459) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_459
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 460 - ((208171/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_460).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_461 : ((41812507/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 461, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 461, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 460, cos1053o2c k) + cos1053o2c 461 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 460) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_460
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 461 - ((118529/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_461).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_462 : ((34817687/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 462, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 462, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 461, cos1053o2c k) + cos1053o2c 462 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 461) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_461
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 462 - ((6839407/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_462).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_463 : ((170329549/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 463, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 463, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 462, cos1053o2c k) + cos1053o2c 463 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 462) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_462
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 463 - ((-1878943/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_463).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_464 : ((8017043/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 464, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 464, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 463, cos1053o2c k) + cos1053o2c 464 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 463) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_463
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 464 - ((-9987689/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_464).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_465 : ((38915201/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 465, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 465, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 464, cos1053o2c k) + cos1053o2c 465 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 464) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_464
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 465 - ((-292441/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_465).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_466 : ((161664657/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 466, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 466, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 465, cos1053o2c k) + cos1053o2c 466 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 465) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_465
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 466 - ((6004853/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_466).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_467 : ((10716281/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 467, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 467, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 466, cos1053o2c k) + cos1053o2c 467 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 466) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_466
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 467 - ((9796839/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_467).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_468 : ((1738627/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 468, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 468, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 467, cos1053o2c k) + cos1053o2c 468 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 467) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_467
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 468 - ((600801/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_468).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_469 : ((16614719/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 469, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 469, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 468, cos1053o2c k) + cos1053o2c 469 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 468) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_468
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 469 - ((-771451/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_469).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_470 : ((157063693/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 470, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 470, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 469, cos1053o2c k) + cos1053o2c 470 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 469) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_469
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 470 - ((-9082497/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_470).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_471 : ((78431059/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 471, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 471, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 470, cos1053o2c k) + cos1053o2c 471 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 470) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_470
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 471 - ((-8023/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_471).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_472 : ((33151539/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 472, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 472, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 471, cos1053o2c k) + cos1053o2c 472 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 471) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_471
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 472 - ((8896577/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_472).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_473 : ((34755431/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 473, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 473, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 472, cos1053o2c k) + cos1053o2c 473 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 472) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_472
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 473 - ((401023/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_473).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_474 : ((85986757/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 474, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 474, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 473, cos1053o2c k) + cos1053o2c 474 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 473) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_473
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 474 - ((-1802641/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_474).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_475 : ((162361801/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 475, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 475, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 474, cos1053o2c k) + cos1053o2c 475 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 474) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_474
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 475 - ((-9610713/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_475).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_476 : ((155592047/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 476, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 476, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 475, cos1053o2c k) + cos1053o2c 476 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 475) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_475
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 476 - ((-3384377/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_476).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_477 : ((159126921/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 477, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 477, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 476, cos1053o2c k) + cos1053o2c 477 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 476) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_476
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 477 - ((1767937/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_477).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_478 : ((42267251/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 478, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 478, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 477, cos1053o2c k) + cos1053o2c 478 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 477) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_477
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 478 - ((9943083/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_478).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_479 : ((43631327/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 479, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 479, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 478, cos1053o2c k) + cos1053o2c 479 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 478) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_478
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 479 - ((682163/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_479).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_480 : ((84774249/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 480, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 480, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 479, cos1053o2c k) + cos1053o2c 480 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 479) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_479
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 480 - ((-497581/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_480).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_481 : ((159557943/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 481, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 481, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 480, cos1053o2c k) + cos1053o2c 481 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 480) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_480
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 481 - ((-1997911/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_481).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_482 : ((155373717/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 482, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 482, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 481, cos1053o2c k) + cos1053o2c 482 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 481) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_481
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 482 - ((-2091613/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_482).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_483 : ((32300103/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 483, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 483, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 482, cos1053o2c k) + cos1053o2c 483 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 482) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_482
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 483 - ((3063899/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_483).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_484 : ((85670989/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 484, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 484, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 483, cos1053o2c k) + cos1053o2c 484 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 483) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_483
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 484 - ((9842463/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_484).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_485 : ((174357413/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 485, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 485, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 484, cos1053o2c k) + cos1053o2c 485 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 484) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_484
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 485 - ((603287/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_485).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_486 : ((167337361/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 486, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 486, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 485, cos1053o2c k) + cos1053o2c 486 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 485) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_485
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 486 - ((-1754763/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_486).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_487 : ((78876237/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 487, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 487, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 486, cos1053o2c k) + cos1053o2c 487 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 486) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_486
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 487 - ((-9583887/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_487).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_488 : ((155752103/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 488, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 488, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 487, cos1053o2c k) + cos1053o2c 488 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 487) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_487
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 488 - ((-1999371/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_488).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_489 : ((40858959/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 489, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 489, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 488, cos1053o2c k) + cos1053o2c 489 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 488) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_488
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 489 - ((7684733/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_489).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_490 : ((172716867/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 490, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 490, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 489, cos1053o2c k) + cos1053o2c 490 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 489) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_489
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 490 - ((9282031/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_490).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_491 : ((43468629/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 491, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 491, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 490, cos1053o2c k) + cos1053o2c 491 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 490) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_490
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 491 - ((1158649/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_491).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_492 : ((41427463/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 492, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 492, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 491, cos1053o2c k) + cos1053o2c 492 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 491) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_491
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 492 - ((-510229/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_492).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_493 : ((78359393/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 493, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 493, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 492, cos1053o2c k) + cos1053o2c 493 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 492) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_492
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 493 - ((-4495033/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_493).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_494 : ((156212039/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 494, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 494, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 493, cos1053o2c k) + cos1053o2c 494 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 493) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_493
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 494 - ((-505747/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_494).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_495 : ((3294021/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 495, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 495, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 494, cos1053o2c k) + cos1053o2c 495 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 494) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_494
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 495 - ((8490011/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_495).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_496 : ((21680943/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 496, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 496, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 495, cos1053o2c k) + cos1053o2c 496 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 495) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_495
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 496 - ((4373747/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_496).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_497 : ((173491491/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 497, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 497, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 496, cos1053o2c k) + cos1053o2c 497 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 496) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_496
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 497 - ((44947/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_497).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_498 : ((164797561/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 498, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 498, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 497, cos1053o2c k) + cos1053o2c 498 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 497) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_497
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 498 - ((-869293/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_498).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_499 : ((7810751/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 499, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 499, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 498, cos1053o2c k) + cos1053o2c 499 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 498) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_498
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 499 - ((-8581541/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_499).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_500 : ((156437897/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 500, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 500, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 499, cos1053o2c k) + cos1053o2c 500 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 499) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_499
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 500 - ((223877/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_500).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_501 : ((165229891/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 501, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 501, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 500, cos1053o2c k) + cos1053o2c 501 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 500) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_500
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 501 - ((4396497/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_501).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_502 : ((173736137/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 502, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 502, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 501, cos1053o2c k) + cos1053o2c 502 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 501) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_501
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 502 - ((4253623/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_502).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_503 : ((86715729/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 503, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 503, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 502, cos1053o2c k) + cos1053o2c 503 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 502) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_502
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 503 - ((-303679/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_503).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_504 : ((82314773/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 504, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 504, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 503, cos1053o2c k) + cos1053o2c 504 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 503) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_503
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 504 - ((-550057/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_504).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_505 : ((39024371/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 505, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 505, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 504, cos1053o2c k) + cos1053o2c 505 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 504) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_504
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 505 - ((-4265531/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_505).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_506 : ((156292593/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 506, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 506, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 505, cos1053o2c k) + cos1053o2c 506 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 505) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_505
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 506 - ((196109/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_506).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_507 : ((16501091/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 507, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 507, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 506, cos1053o2c k) + cos1053o2c 507 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 506) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_506
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 507 - ((8719317/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_507).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_508 : ((43414843/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 508, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 508, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 507, cos1053o2c k) + cos1053o2c 508 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 507) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_507
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 508 - ((4324731/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_508).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_509 : ((86877327/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 509, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 509, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 508, cos1053o2c k) + cos1053o2c 509 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 508) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_508
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 509 - ((48141/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_509).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_510 : ((33042619/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 510, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 510, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 509, cos1053o2c k) + cos1053o2c 510 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 509) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_509
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 510 - ((-8540559/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_510).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_511 : ((156361829/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 511, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 511, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 510, cos1053o2c k) + cos1053o2c 511 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 510) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_510
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 511 - ((-4425133/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_511).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_512 : ((15578923/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 512, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 512, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 511, cos1053o2c k) + cos1053o2c 512 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 511) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_511
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 512 - ((-571599/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_512).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_513 : ((164037741/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 513, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 513, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 512, cos1053o2c k) + cos1053o2c 513 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 512) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_512
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 513 - ((8249511/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_513).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_514 : ((1352724/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 514, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 514, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 513, cos1053o2c k) + cos1053o2c 514 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 513) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_513
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 514 - ((9111931/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_514).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_515 : ((34874543/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 515, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 515, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 514, cos1053o2c k) + cos1053o2c 515 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 514) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_514
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 515 - ((1225043/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_515).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_516 : ((166547829/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 516, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 516, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 515, cos1053o2c k) + cos1053o2c 516 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 515) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_515
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 516 - ((-3911943/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_516).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_517 : ((31428607/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 517, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 517, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 516, cos1053o2c k) + cos1053o2c 517 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 516) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_516
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 517 - ((-4701897/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_517).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_518 : ((15509329/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 518, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 518, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 517, cos1053o2c k) + cos1053o2c 518 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 517) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_517
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 518 - ((-409749/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_518).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_519 : ((162328763/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 519, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 519, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 518, cos1053o2c k) + cos1053o2c 519 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 518) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_518
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 519 - ((7236473/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_519).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_520 : ((172012447/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 520, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 520, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 519, cos1053o2c k) + cos1053o2c 520 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 519) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_519
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 520 - ((2421171/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_520).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_521 : ((175038177/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 521, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 521, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 520, cos1053o2c k) + cos1053o2c 521 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 520) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_520
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 521 - ((302673/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_521).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_522 : ((168579199/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 522, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 522, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 521, cos1053o2c k) + cos1053o2c 522 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 521) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_521
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 522 - ((-3228989/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_522).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_523 : ((31734913/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 523, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 523, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 522, cos1053o2c k) + cos1053o2c 523 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 522) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_522
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 523 - ((-4951817/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_523).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_524 : ((19317501/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 524, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 524, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 523, cos1053o2c k) + cos1053o2c 524 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 523) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_523
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 524 - ((-4133557/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_524).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_525 : ((159999899/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 525, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 525, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 524, cos1053o2c k) + cos1053o2c 525 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 524) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_524
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 525 - ((5460891/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_525).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_526 : ((16999851/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 526, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 526, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 525, cos1053o2c k) + cos1053o2c 526 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 525) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_525
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 526 - ((9999611/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_526).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_527 : ((175326247/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 527, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 527, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 526, cos1053o2c k) + cos1053o2c 527 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 526) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_526
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 527 - ((5328737/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_527).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_528 : ((171101233/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 528, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 528, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 527, cos1053o2c k) + cos1053o2c 528 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 527) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_527
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 528 - ((-2112007/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_528).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_529 : ((5037373/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 529, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 529, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 528, cos1053o2c k) + cos1053o2c 529 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 528) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_528
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 529 - ((-9904297/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_529).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_530 : ((154639453/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 530, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 530, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 529, cos1053o2c k) + cos1053o2c 530 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 529) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_529
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 530 - ((-6555483/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_530).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_531 : ((78689199/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 531, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 531, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 530, cos1053o2c k) + cos1053o2c 531 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 530) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_530
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 531 - ((547989/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_531).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_532 : ((166922763/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 532, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 532, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 531, cos1053o2c k) + cos1053o2c 532 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 531) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_531
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 532 - ((1909073/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_532).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_533 : ((5458099/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 533, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 533, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 532, cos1053o2c k) + cos1053o2c 533 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 532) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_532
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 533 - ((1547481/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_533).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_534 : ((21704809/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 534, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 534, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 533, cos1053o2c k) + cos1053o2c 534 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 533) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_533
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 534 - ((-63731/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_534).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_535 : ((164784299/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 535, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 535, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 534, cos1053o2c k) + cos1053o2c 535 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 534) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_534
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 535 - ((-8853173/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_535).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_536 : ((9750337/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 536, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 536, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 535, cos1053o2c k) + cos1053o2c 536 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 535) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_535
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 536 - ((-8777907/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_536).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_537 : ((15510673/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 537, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 537, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 536, cos1053o2c k) + cos1053o2c 537 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 536) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_536
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 537 - ((-448831/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_537).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_538 : ((32574869/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 538, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 538, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 537, cos1053o2c k) + cos1053o2c 538 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 537) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_537
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 538 - ((1553723/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_538).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_539 : ((4310919/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 539, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 539, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 538, cos1053o2c k) + cos1053o2c 539 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 538) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_538
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 539 - ((1912683/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_539).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_540 : ((43843669/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 540, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 540, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 539, cos1053o2c k) + cos1053o2c 540 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 539) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_539
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 540 - ((734729/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_540).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_541 : ((845593/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 541, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 541, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 540, cos1053o2c k) + cos1053o2c 541 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 540) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_540
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 541 - ((-1563769/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_541).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_542 : ((159147481/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 542, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 542, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 541, cos1053o2c k) + cos1053o2c 542 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 541) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_541
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 542 - ((-9970119/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_542).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_543 : ((154151901/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 543, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 543, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 542, cos1053o2c k) + cos1053o2c 543 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 542) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_542
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 543 - ((-249729/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_543).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_544 : ((79231053/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 544, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 544, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 543, cos1053o2c k) + cos1053o2c 544 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 543) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_543
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 544 - ((862241/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_544).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_545 : ((84168159/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 545, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 545, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 544, cos1053o2c k) + cos1053o2c 545 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 544) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_544
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 545 - ((2468803/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_545).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_546 : ((175251747/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 546, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 546, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 545, cos1053o2c k) + cos1053o2c 546 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 545) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_545
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 546 - ((6916429/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_546).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_547 : ((8663359/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 547, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 547, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 546, cos1053o2c k) + cos1053o2c 547 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 546) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_546
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 547 - ((-1983567/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_547).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_548 : ((164093043/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 548, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 548, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 547, cos1053o2c k) + cos1053o2c 548 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 547) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_547
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 548 - ((-9173137/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_548).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_549 : ((38892221/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 549, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 549, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 548, cos1053o2c k) + cos1053o2c 549 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 548) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_548
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 549 - ((-8523159/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_549).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_550 : ((154945561/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 550, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 550, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 549, cos1053o2c k) + cos1053o2c 550 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 549) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_549
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 550 - ((-622323/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_550).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_551 : ((162741441/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 551, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 551, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 550, cos1053o2c k) + cos1053o2c 551 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 550) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_550
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 551 - ((97461/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_551).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_552 : ((86178223/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 552, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 552, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 551, cos1053o2c k) + cos1053o2c 552 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 551) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_551
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 552 - ((1923201/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_552).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_553 : ((17568853/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 553, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 553, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 552, cos1053o2c k) + cos1053o2c 553 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 552) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_552
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 553 - ((833271/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_553).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_554 : ((84973839/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 554, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 554, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 553, cos1053o2c k) + cos1053o2c 554 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 553) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_553
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 554 - ((-1434963/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_554).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_555 : ((159947167/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 555, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 555, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 554, cos1053o2c k) + cos1053o2c 555 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 554) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_554
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 555 - ((-9999511/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_555).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_556 : ((77015523/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 556, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 556, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 555, cos1053o2c k) + cos1053o2c 556 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 555) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_555
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 556 - ((-5915121/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_556).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_557 : ((78555487/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 557, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 557, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 556, cos1053o2c k) + cos1053o2c 557 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 556) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_556
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 557 - ((96279/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_557).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_558 : ((8331171/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 558, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 558, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 557, cos1053o2c k) + cos1053o2c 558 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 557) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_557
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 558 - ((4756723/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_558).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_559 : ((174705801/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 559, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 559, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 558, cos1053o2c k) + cos1053o2c 559 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 558) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_558
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 559 - ((8083381/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_559).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_560 : ((174707903/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 560, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 560, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 559, cos1053o2c k) + cos1053o2c 560 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 559) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_559
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 560 - ((1551/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_560).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_561 : ((41659201/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 561, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 561, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 560, cos1053o2c k) + cos1053o2c 561 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 560) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_560
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 561 - ((-8070099/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_561).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_562 : ((157100097/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 562, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 562, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 561, cos1053o2c k) + cos1053o2c 562 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 561) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_561
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 562 - ((-9535707/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_562).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_563 : ((38467349/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 563, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 563, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 562, cos1053o2c k) + cos1053o2c 563 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 562) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_562
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 563 - ((-3229701/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_563).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_564 : ((159559807/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 564, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 564, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 563, cos1053o2c k) + cos1053o2c 564 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 563) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_563
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 564 - ((5691411/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_564).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_565 : ((4238837/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 565, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 565, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 564, cos1053o2c k) + cos1053o2c 565 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 564) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_564
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 565 - ((9994673/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_565).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_566 : ((87890673/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 566, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 566, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 565, cos1053o2c k) + cos1053o2c 566 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 565) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_565
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 566 - ((3114433/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_566).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_567 : ((173238511/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 567, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 567, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 566, cos1053o2c k) + cos1053o2c 567 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 566) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_566
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 567 - ((-508367/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_567).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_568 : ((32794693/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 568, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 568, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 567, cos1053o2c k) + cos1053o2c 568 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 567) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_567
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 568 - ((-4632023/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_568).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_569 : ((77697859/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 569, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 569, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 568, cos1053o2c k) + cos1053o2c 569 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 568) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_568
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 569 - ((-8576747/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_569).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_570 : ((38583557/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 570, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 570, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 569, cos1053o2c k) + cos1053o2c 570 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 569) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_569
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 570 - ((-106049/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_570).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_571 : ((40405453/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 571, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 571, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 570, cos1053o2c k) + cos1053o2c 571 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 570) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_570
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 571 - ((911073/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_571).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_572 : ((5358799/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 572, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 572, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 571, cos1053o2c k) + cos1053o2c 572 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 571) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_571
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 572 - ((2465189/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_572).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_573 : ((176134089/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 573, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 573, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 572, cos1053o2c k) + cos1053o2c 573 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 572) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_572
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 573 - ((4653521/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_573).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_574 : ((1719283/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 574, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 574, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 573, cos1053o2c k) + cos1053o2c 574 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 573) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_573
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 574 - ((-4204789/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_574).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_575 : ((81084539/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 575, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 575, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 574, cos1053o2c k) + cos1053o2c 575 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 574) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_574
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 575 - ((-4879111/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_575).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_576 : ((154484351/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 576, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 576, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 575, cos1053o2c k) + cos1053o2c 576 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 575) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_575
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 576 - ((-7683727/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_576).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_577 : ((154852989/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 577, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 577, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 576, cos1053o2c k) + cos1053o2c 577 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 576) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_576
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 577 - ((184819/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_577).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_578 : ((8148917/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 578, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 578, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 577, cos1053o2c k) + cos1053o2c 578 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 577) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_577
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 578 - ((8126351/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_578).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_579 : ((4314139/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 579, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 579, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 578, cos1053o2c k) + cos1053o2c 579 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 578) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_578
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 579 - ((479411/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_579).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_580 : ((704881/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 580, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 580, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 579, cos1053o2c k) + cos1053o2c 580 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 579) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_579
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 580 - ((365569/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_580).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_581 : ((85570299/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 581, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 581, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 580, cos1053o2c k) + cos1053o2c 581 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 580) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_580
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 581 - ((-1269663/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_581).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_582 : ((6449099/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 582, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 582, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 581, cos1053o2c k) + cos1053o2c 582 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 581) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_581
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 582 - ((-9912123/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_582).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_583 : ((7702777/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 583, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 583, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 582, cos1053o2c k) + cos1053o2c 583 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 582) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_582
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 583 - ((-1434187/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_583).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_584 : ((155079661/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 584, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 584, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 583, cos1053o2c k) + cos1053o2c 584 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 583) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_583
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 584 - ((1025121/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_584).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_585 : ((16351213/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 585, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 585, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 584, cos1053o2c k) + cos1053o2c 585 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 584) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_584
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 585 - ((8433469/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_585).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_586 : ((86482699/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 586, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 586, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 585, cos1053o2c k) + cos1053o2c 586 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 585) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_585
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 586 - ((2363567/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_586).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_587 : ((176310267/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 587, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 587, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 586, cos1053o2c k) + cos1053o2c 587 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 586) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_586
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 587 - ((3345869/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_587).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_588 : ((171039929/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 588, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 588, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 587, cos1053o2c k) + cos1053o2c 588 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 587) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_587
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 588 - ((-2634669/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_588).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_589 : ((161112261/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 589, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 589, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 588, cos1053o2c k) + cos1053o2c 589 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 588) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_588
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 589 - ((-2481667/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_589).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_590 : ((153945923/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 590, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 590, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 589, cos1053o2c k) + cos1053o2c 590 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 589) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_589
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 590 - ((-3582669/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_590).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_591 : ((30974333/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 591, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 591, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 590, cos1053o2c k) + cos1053o2c 591 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 590) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_590
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 591 - ((463371/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_591).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_592 : ((163191803/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 592, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 592, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 591, cos1053o2c k) + cos1053o2c 592 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 591) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_591
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 592 - ((4160569/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_592).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_593 : ((172742139/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 593, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 593, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 592, cos1053o2c k) + cos1053o2c 593 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 592) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_592
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 593 - ((1193917/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_593).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_594 : ((44119449/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 594, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 594, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 593, cos1053o2c k) + cos1053o2c 594 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 593) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_593
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 594 - ((3736657/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_594).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_595 : ((85829573/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 595, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 595, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 594, cos1053o2c k) + cos1053o2c 595 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 594) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_594
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 595 - ((-96353/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_595).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_596 : ((161827003/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 596, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 596, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 595, cos1053o2c k) + cos1053o2c 596 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 595) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_595
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 596 - ((-9831143/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_596).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_597 : ((1233351/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 597, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 597, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 596, cos1053o2c k) + cos1053o2c 597 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 596) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_596
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 597 - ((-957141/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_597).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_598 : ((154257889/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 598, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 598, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 597, cos1053o2c k) + cos1053o2c 598 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 597) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_597
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 598 - ((45007/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_598).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_599 : ((162019277/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 599, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 599, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 598, cos1053o2c k) + cos1053o2c 599 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 598) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_598
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 599 - ((1940597/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_599).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_600 : ((85913273/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 600, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 600, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 599, cos1053o2c k) + cos1053o2c 600 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 599) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_599
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 600 - ((9808269/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_600).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_601 : ((5518787/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 601, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 601, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 600, cos1053o2c k) + cos1053o2c 601 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 600) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_600
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 601 - ((2387819/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_601).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_602 : ((172914891/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 602, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 602, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 601, cos1053o2c k) + cos1053o2c 602 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 601) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_601
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 602 - ((-3685293/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_602).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_603 : ((40855021/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 603, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 603, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 602, cos1053o2c k) + cos1053o2c 603 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 602) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_602
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 603 - ((-9493807/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_603).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_604 : ((154908889/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 604, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 604, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 603, cos1053o2c k) + cos1053o2c 604 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 603) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_603
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 604 - ((-1702039/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_604).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_605 : ((153443823/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 605, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 605, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 604, cos1053o2c k) + cos1053o2c 605 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 604) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_604
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 605 - ((-732033/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_605).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_606 : ((32011209/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 606, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 606, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 605, cos1053o2c k) + cos1053o2c 606 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 605) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_605
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 606 - ((3306611/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_606).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_607 : ((17005307/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 607, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 607, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 606, cos1053o2c k) + cos1053o2c 607 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 606) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_606
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 607 - ((399921/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_607).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_608 : ((176372973/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 608, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 608, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 607, cos1053o2c k) + cos1053o2c 608 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 607) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_607
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 608 - ((6320903/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_608).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_609 : ((174571817/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 609, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 609, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 608, cos1053o2c k) + cos1053o2c 609 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 608) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_608
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 609 - ((-450039/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_609).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_610 : ((165922421/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 610, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 610, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 609, cos1053o2c k) + cos1053o2c 610 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 609) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_609
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 610 - ((-2162099/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_610).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_611 : ((156482067/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 611, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 611, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 610, cos1053o2c k) + cos1053o2c 611 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 610) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_610
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 611 - ((-4719677/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_611).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_612 : ((1910419/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 612, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 612, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 611, cos1053o2c k) + cos1053o2c 612 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 611) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_611
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 612 - ((-3647547/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_612).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_613 : ((78752817/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 613, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 613, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 612, cos1053o2c k) + cos1053o2c 613 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 612) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_612
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 613 - ((2336557/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_613).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_614 : ((33449909/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 614, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 614, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 613, cos1053o2c k) + cos1053o2c 614 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 613) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_613
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 614 - ((9744911/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_614).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_615 : ((175326349/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 615, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 615, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 614, cos1053o2c k) + cos1053o2c 615 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 614) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_614
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 615 - ((2019451/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_615).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_616 : ((176174051/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 616, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 616, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 615, cos1053o2c k) + cos1053o2c 616 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 615) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_615
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 616 - ((424351/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_616).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_617 : ((169218427/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 617, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 617, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 616, cos1053o2c k) + cos1053o2c 617 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 616) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_616
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 617 - ((-54333/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_617).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_618 : ((159230369/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 618, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 618, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 617, cos1053o2c k) + cos1053o2c 618 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 617) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_617
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 618 - ((-4993529/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_618).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_619 : ((153029939/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 619, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 619, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 618, cos1053o2c k) + cos1053o2c 619 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 618) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_618
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 619 - ((-619943/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_619).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_620 : ((1548311/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 620, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 620, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 619, cos1053o2c k) + cos1053o2c 620 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 619) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_619
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 620 - ((1802161/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_620).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_621 : ((32680323/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 621, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 621, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 620, cos1053o2c k) + cos1053o2c 621 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 620) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_620
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 621 - ((1714303/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_621).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_622 : ((172935909/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 622, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 622, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 621, cos1053o2c k) + cos1053o2c 622 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 621) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_621
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 622 - ((4767647/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_622).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_623 : ((35400527/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 623, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 623, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 622, cos1053o2c k) + cos1053o2c 623 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 622) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_622
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 623 - ((2033863/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_623).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_624 : ((172874033/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 624, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 624, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 623, cos1053o2c k) + cos1053o2c 624 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 623) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_623
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 624 - ((-2063801/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_624).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_625 : ((4083157/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 625, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 625, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 624, cos1053o2c k) + cos1053o2c 625 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 624) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_624
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 625 - ((-9546753/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_625).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_626 : ((9671597/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 626, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 626, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 625, cos1053o2c k) + cos1053o2c 626 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 625) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_625
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 626 - ((-536233/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_626).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_627 : ((76423509/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 627, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 627, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 626, cos1053o2c k) + cos1053o2c 627 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 626) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_626
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 627 - ((-948767/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_627).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_628 : ((1588829/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 628, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 628, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 627, cos1053o2c k) + cos1053o2c 628 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 627) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_627
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 628 - ((3018441/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_628).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_629 : ((42211457/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 629, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 629, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 628, cos1053o2c k) + cos1053o2c 629 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 628) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_628
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 629 - ((1245491/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_629).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_630 : ((176151927/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 630, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 630, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 629, cos1053o2c k) + cos1053o2c 630 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 629) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_629
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 630 - ((7307099/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_630).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_631 : ((35198851/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 631, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 631, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 630, cos1053o2c k) + cos1053o2c 631 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 630) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_630
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 631 - ((-1224/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_631).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_632 : ((168484541/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 632, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 632, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 631, cos1053o2c k) + cos1053o2c 632 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 631) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_631
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 632 - ((-3754357/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_632).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_633 : ((990907/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 633, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 633, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 632, cos1053o2c k) + cos1053o2c 633 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 632) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_632
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 633 - ((-9938421/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_633).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_634 : ((76331661/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 634, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 634, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 633, cos1053o2c k) + cos1053o2c 634 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 633) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_633
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 634 - ((-2940399/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_634).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_635 : ((38664903/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 635, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 635, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 634, cos1053o2c k) + cos1053o2c 635 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 634) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_634
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 635 - ((199729/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_635).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_636 : ((20403681/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 636, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 636, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 635, cos1053o2c k) + cos1053o2c 636 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 635) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_635
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 636 - ((2142709/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_636).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_637 : ((86411167/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 637, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 637, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 636, cos1053o2c k) + cos1053o2c 637 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 636) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_636
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 637 - ((4796943/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_637).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_638 : ((44312871/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 638, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 638, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 637, cos1053o2c k) + cos1053o2c 638 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 637) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_637
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 638 - ((88603/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_638).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_639 : ((173674963/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 639, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 639, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 638, cos1053o2c k) + cos1053o2c 639 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 638) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_638
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 639 - ((-3575521/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_639).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_640 : ((82197121/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 640, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 640, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 639, cos1053o2c k) + cos1053o2c 640 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 639) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_639
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 640 - ((-9279721/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_640).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_641 : ((77673207/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 641, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 641, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 640, cos1053o2c k) + cos1053o2c 641 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 640) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_640
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 641 - ((-2261707/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_641).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_642 : ((152296029/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 642, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 642, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 641, cos1053o2c k) + cos1053o2c 642 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 641) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_641
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 642 - ((-609877/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_642).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_643 : ((31434611/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 643, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 643, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 642, cos1053o2c k) + cos1053o2c 643 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 642) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_642
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 643 - ((2439013/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_643).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_644 : ((166878153/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 644, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 644, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 643, cos1053o2c k) + cos1053o2c 644 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 643) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_643
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 644 - ((4853049/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_644).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_645 : ((175275201/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 645, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 645, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 644, cos1053o2c k) + cos1053o2c 645 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 644) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_644
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 645 - ((262439/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_645).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_646 : ((177076987/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 646, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 646, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 645, cos1053o2c k) + cos1053o2c 646 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 645) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_645
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 646 - ((901393/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_646).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_647 : ((171159779/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 647, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 647, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 646, cos1053o2c k) + cos1053o2c 647 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 646) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_646
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 647 - ((-369763/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_647).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_648 : ((161236307/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 648, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 648, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 647, cos1053o2c k) + cos1053o2c 648 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 647) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_647
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 648 - ((-1240309/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_648).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_649 : ((9594111/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 649, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 649, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 648, cos1053o2c k) + cos1053o2c 649 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 648) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_648
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 649 - ((-7729531/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_649).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_650 : ((152776589/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 650, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 650, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 649, cos1053o2c k) + cos1053o2c 650 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 649) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_649
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 650 - ((-728187/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_650).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_651 : ((159492619/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 651, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 651, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 650, cos1053o2c k) + cos1053o2c 651 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 650) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_650
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 651 - ((671703/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_651).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_652 : ((42372049/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 652, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 652, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 651, cos1053o2c k) + cos1053o2c 652 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 651) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_651
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 652 - ((9996577/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_652).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_653 : ((176591071/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 653, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 653, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 652, cos1053o2c k) + cos1053o2c 653 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 652) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_652
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 653 - ((56831/80000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_653).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_654 : ((176434061/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 654, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 654, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 653, cos1053o2c k) + cos1053o2c 654 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 653) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_653
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 654 - ((-15601/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_654).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_655 : ((169121323/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 655, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 655, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 654, cos1053o2c k) + cos1053o2c 655 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 654) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_654
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 655 - ((-3655869/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_655).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_656 : ((159134059/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 656, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 656, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 655, cos1053o2c k) + cos1053o2c 656 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 655) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_655
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 656 - ((-1248283/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_656).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_657 : ((152566633/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 657, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 657, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 656, cos1053o2c k) + cos1053o2c 657 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 656) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_656
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 657 - ((-3283213/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_657).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_658 : ((76704293/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 658, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 658, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 657, cos1053o2c k) + cos1053o2c 658 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 657) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_657
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 658 - ((842953/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_658).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_659 : ((20142501/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 659, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 659, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 658, cos1053o2c k) + cos1053o2c 659 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 658) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_658
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 659 - ((3866211/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_659).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_660 : ((8553847/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 660, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 660, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 659, cos1053o2c k) + cos1053o2c 660 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 659) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_659
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 660 - ((2484483/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_660).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_661 : ((35444897/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 661, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 661, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 660, cos1053o2c k) + cos1053o2c 661 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 660) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_660
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 661 - ((1229709/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_661).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_662 : ((175890379/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 662, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 662, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 661, cos1053o2c k) + cos1053o2c 662 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 661) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_661
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 662 - ((-666553/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_662).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_663 : ((167882709/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 663, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 663, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 662, cos1053o2c k) + cos1053o2c 663 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 662) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_662
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 663 - ((-800667/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_663).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_664 : ((157995727/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 664, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 664, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 663, cos1053o2c k) + cos1053o2c 664 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 663) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_663
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 664 - ((-4942991/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_664).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_665 : ((76062501/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 665, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 665, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 664, cos1053o2c k) + cos1053o2c 665 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 664) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_664
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 665 - ((-234789/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_665).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_666 : ((153754733/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 666, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 666, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 665, cos1053o2c k) + cos1053o2c 666 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 665) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_665
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 666 - ((1630731/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_666).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_667 : ((40477433/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 667, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 667, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 666, cos1053o2c k) + cos1053o2c 667 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 666) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_666
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 667 - ((8155999/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_667).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_668 : ((85880829/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 668, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 668, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 667, cos1053o2c k) + cos1053o2c 668 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 667) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_667
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 668 - ((4926463/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_668).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_669 : ((17750151/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 669, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 669, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 668, cos1053o2c k) + cos1053o2c 669 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 668) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_668
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 669 - ((1435213/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_669).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_670 : ((87879977/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 670, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 670, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 669, cos1053o2c k) + cos1053o2c 670 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 669) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_669
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 670 - ((-435139/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_670).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_671 : ((167566071/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 671, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 671, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 670, cos1053o2c k) + cos1053o2c 671 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 670) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_670
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 671 - ((-8192883/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_671).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_672 : ((31543019/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 672, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 672, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 671, cos1053o2c k) + cos1053o2c 672 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 671) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_671
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 672 - ((-1231247/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_672).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_673 : ((30389793/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 673, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 673, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 672, cos1053o2c k) + cos1053o2c 673 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 672) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_672
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 673 - ((-576513/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_673).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_674 : ((76806549/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 674, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 674, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 673, cos1053o2c k) + cos1053o2c 674 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 673) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_673
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 674 - ((1665133/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_674).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_675 : ((32346721/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 675, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 675, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 674, cos1053o2c k) + cos1053o2c 675 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 674) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_674
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 675 - ((8121507/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_675).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_676 : ((171610451/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 676, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 676, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 675, cos1053o2c k) + cos1053o2c 676 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 675) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_675
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 676 - ((4938923/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_676).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_677 : ((44387441/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 677, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 677, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 676, cos1053o2c k) + cos1053o2c 677 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 676) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_676
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 677 - ((5940313/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_677).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_678 : ((88071453/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 678, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 678, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 677, cos1053o2c k) + cos1053o2c 678 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 677) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_677
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 678 - ((-702929/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_678).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_679 : ((168203727/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 679, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 679, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 678, cos1053o2c k) + cos1053o2c 679 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 678) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_678
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 679 - ((-7938179/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_679).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_680 : ((79137959/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 680, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 680, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 679, cos1053o2c k) + cos1053o2c 680 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 679) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_679
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 680 - ((-9926809/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_680).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_681 : ((152018223/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 681, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 681, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 680, cos1053o2c k) + cos1053o2c 681 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 680) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_680
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 681 - ((-1251339/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_681).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_682 : ((38245291/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 682, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 682, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 681, cos1053o2c k) + cos1053o2c 682 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 681) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_681
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 682 - ((963941/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_682).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_683 : ((160610359/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 683, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 683, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 682, cos1053o2c k) + cos1053o2c 683 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 682) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_682
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 683 - ((1526039/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_683).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_684 : ((42646647/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 684, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 684, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 683, cos1053o2c k) + cos1053o2c 684 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 683) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_683
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 684 - ((9977229/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_684).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_685 : ((177285039/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 685, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 685, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 684, cos1053o2c k) + cos1053o2c 685 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 684) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_684
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 685 - ((6699451/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_685).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_686 : ((176944871/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 686, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 686, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 685, cos1053o2c k) + cos1053o2c 686 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 685) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_685
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 686 - ((-10599/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_686).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_687 : ((169764577/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 687, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 687, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 686, cos1053o2c k) + cos1053o2c 687 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 686) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_686
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 687 - ((-3589647/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_687).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_688 : ((79881831/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 688, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 688, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 687, cos1053o2c k) + cos1053o2c 688 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 687) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_687
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 688 - ((-1999983/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_688).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_689 : ((76259089/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 689, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 689, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 688, cos1053o2c k) + cos1053o2c 689 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 688) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_688
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 689 - ((-1811121/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_689).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_690 : ((76025419/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 690, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 690, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 689, cos1053o2c k) + cos1053o2c 690 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 689) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_689
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 690 - ((-23317/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_690).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_691 : ((158612647/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 691, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 691, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 690, cos1053o2c k) + cos1053o2c 691 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 690) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_690
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 691 - ((6562809/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_691).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_692 : ((6742717/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 692, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 692, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 691, cos1053o2c k) + cos1053o2c 692 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 691) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_691
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 692 - ((4978139/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_692).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_693 : ((88212733/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 693, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 693, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 692, cos1053o2c k) + cos1053o2c 693 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 692) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_692
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 693 - ((7858541/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_693).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_694 : ((88934017/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 694, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 694, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 693, cos1053o2c k) + cos1053o2c 694 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 693) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_693
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 694 - ((90223/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_694).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_695 : ((172111797/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 695, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 695, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 694, cos1053o2c k) + cos1053o2c 695 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 694) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_694
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 695 - ((-5755237/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_695).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_696 : ((81155613/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 696, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 696, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 695, cos1053o2c k) + cos1053o2c 696 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 695) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_695
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 696 - ((-9799571/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_696).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_697 : ((76906661/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 697, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 697, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 696, cos1053o2c k) + cos1053o2c 697 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 696) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_696
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 697 - ((-1062113/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_697).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_698 : ((30247231/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 698, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 698, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 697, cos1053o2c k) + cos1053o2c 698 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 697) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_697
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 698 - ((-2576167/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_698).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_699 : ((155969471/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 699, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 699, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 698, cos1053o2c k) + cos1053o2c 699 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 698) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_698
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 699 - ((1183579/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_699).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_700 : ((41361301/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 700, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 700, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 699, cos1053o2c k) + cos1053o2c 700 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 699) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_699
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 700 - ((9476733/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_700).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_701 : ((87273889/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 701, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 701, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 700, cos1053o2c k) + cos1053o2c 701 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 700) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_700
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 701 - ((4551787/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_701).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_702 : ((44595411/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 702, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 702, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 701, cos1053o2c k) + cos1053o2c 702 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 701) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_701
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 702 - ((1917433/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_702).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_703 : ((174896757/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 703, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 703, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 702, cos1053o2c k) + cos1053o2c 703 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 702) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_702
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 703 - ((-3483887/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_703).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_704 : ((16596439/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 704, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 704, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 703, cos1053o2c k) + cos1053o2c 704 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 703) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_703
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 704 - ((-8931367/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_704).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_705 : ((31271033/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 705, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 705, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 704, cos1053o2c k) + cos1053o2c 705 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 704) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_704
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 705 - ((-384329/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_705).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_706 : ((151181161/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 706, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 706, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 705, cos1053o2c k) + cos1053o2c 706 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 705) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_705
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 706 - ((-1293251/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_706).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_707 : ((1196732/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 707, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 707, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 706, cos1053o2c k) + cos1053o2c 707 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 706) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_706
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 707 - ((400307/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_707).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_708 : ((80644793/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 708, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 708, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 707, cos1053o2c k) + cos1053o2c 708 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 707) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_707
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 708 - ((810889/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_708).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_709 : ((85609507/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 709, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 709, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 708, cos1053o2c k) + cos1053o2c 709 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 708) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_708
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 709 - ((2482607/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_709).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_710 : ((177741803/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 710, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 710, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 709, cos1053o2c k) + cos1053o2c 710 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 709) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_709
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 710 - ((6523789/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_710).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_711 : ((177437553/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 711, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 711, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 710, cos1053o2c k) + cos1053o2c 711 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 710) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_710
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 711 - ((-1213/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_711).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_712 : ((34094573/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 712, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 712, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 711, cos1053o2c k) + cos1053o2c 712 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 711) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_711
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 712 - ((-870461/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_712).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_713 : ((40122697/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 713, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 713, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 712, cos1053o2c k) + cos1053o2c 713 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 712) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_712
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 713 - ((-9981077/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_713).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_714 : ((76345617/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 714, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 714, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 713, cos1053o2c k) + cos1053o2c 714 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 713) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_713
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 714 - ((-3899277/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_714).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_715 : ((15112129/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 715, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 715, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 714, cos1053o2c k) + cos1053o2c 715 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 714) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_714
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 715 - ((-98059/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_715).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_716 : ((156586227/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 716, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 716, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 715, cos1053o2c k) + cos1053o2c 716 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 715) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_715
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 716 - ((5465937/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_716).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_717 : ((41563773/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 717, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 717, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 716, cos1053o2c k) + cos1053o2c 717 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 716) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_716
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 717 - ((1933973/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_717).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_718 : ((1094637/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 718, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 718, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 717, cos1053o2c k) + cos1053o2c 718 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 717) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_717
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 718 - ((2221957/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_718).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_719 : ((44670359/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 719, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 719, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 718, cos1053o2c k) + cos1053o2c 719 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 718) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_718
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 719 - ((885129/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_719).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_720 : ((175065377/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 720, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 720, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 719, cos1053o2c k) + cos1053o2c 720 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 719) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_719
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 720 - ((-3615059/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_720).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_721 : ((16614953/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 721, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 721, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 720, cos1053o2c k) + cos1053o2c 721 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 720) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_720
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 721 - ((-8914847/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_721).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_722 : ((7824173/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 722, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 722, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 721, cos1053o2c k) + cos1053o2c 722 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 721) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_721
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 722 - ((-966507/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_722).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_723 : ((150981133/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 723, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 723, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 722, cos1053o2c k) + cos1053o2c 723 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 722) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_722
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 723 - ((-5501327/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_723).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_724 : ((152426567/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 724, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 724, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 723, cos1053o2c k) + cos1053o2c 724 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 723) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_723
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 724 - ((723217/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_724).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_725 : ((160080969/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 725, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 725, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 724, cos1053o2c k) + cos1053o2c 725 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 724) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_724
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 725 - ((3827701/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_725).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_726 : ((1360611/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 726, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 726, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 725, cos1053o2c k) + cos1053o2c 726 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 725) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_725
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 726 - ((4998203/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_726).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_727 : ((44345531/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 727, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 727, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 726, cos1053o2c k) + cos1053o2c 727 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 726) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_726
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 727 - ((7306749/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_727).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_728 : ((356671/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 728, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 728, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 727, cos1053o2c k) + cos1053o2c 728 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 727) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_727
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 728 - ((119297/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_728).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_729 : ((86233079/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 729, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 729, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 728, cos1053o2c k) + cos1053o2c 729 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 728) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_728
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 729 - ((-2934171/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_729).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_730 : ((81355203/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 730, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 730, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 729, cos1053o2c k) + cos1053o2c 730 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 729) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_729
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 730 - ((-76209/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_730).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_731 : ((15392783/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 731, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 731, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 730, cos1053o2c k) + cos1053o2c 731 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 730) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_730
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 731 - ((-1097697/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_731).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_732 : ((18809627/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 732, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 732, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 731, cos1053o2c k) + cos1053o2c 732 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 731) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_731
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 732 - ((-1724907/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_732).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_733 : ((77030033/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 733, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 733, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 732, cos1053o2c k) + cos1053o2c 733 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 732) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_732
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 733 - ((71681/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_733).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_734 : ((162898999/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 734, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 734, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 733, cos1053o2c k) + cos1053o2c 734 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 733) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_733
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 734 - ((8839933/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_734).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_735 : ((8631697/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 735, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 735, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 734, cos1053o2c k) + cos1053o2c 735 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 734) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_734
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 735 - ((9735941/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_735).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_736 : ((89240323/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 736, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 736, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 735, cos1053o2c k) + cos1053o2c 736 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 735) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_735
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 736 - ((2923853/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_736).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_737 : ((22197319/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 737, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 737, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 736, cos1053o2c k) + cos1053o2c 737 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 736) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_736
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 737 - ((-450547/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_737).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_738 : ((17037503/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 738, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 738, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 737, cos1053o2c k) + cos1053o2c 738 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 737) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_737
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 738 - ((-3601261/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_738).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_739 : ((160388443/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 739, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 739, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 738, cos1053o2c k) + cos1053o2c 739 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 738) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_738
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 739 - ((-9985587/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_739).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_740 : ((1905959/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 740, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 740, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 739, cos1053o2c k) + cos1053o2c 740 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 739) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_739
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 740 - ((-7910723/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_740).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_741 : ((37618529/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 741, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 741, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 740, cos1053o2c k) + cos1053o2c 741 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 740) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_740
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 741 - ((-500401/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_741).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_742 : ((77670967/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 742, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 742, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 741, cos1053o2c k) + cos1053o2c 742 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 741) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_741
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 742 - ((2434409/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_742).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_743 : ((6588947/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 743, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 743, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 742, cos1053o2c k) + cos1053o2c 743 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 742) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_742
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 743 - ((9382741/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_743).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_744 : ((21762413/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 744, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 744, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 743, cos1053o2c k) + cos1053o2c 744 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 743) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_743
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 744 - ((9376629/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_744).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_745 : ((4474207/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 745, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 745, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 744, cos1053o2c k) + cos1053o2c 745 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 744) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_744
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 745 - ((608747/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_745).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_746 : ((177004131/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 746, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 746, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 745, cos1053o2c k) + cos1053o2c 746 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 745) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_745
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 746 - ((-1963149/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_746).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_747 : ((169152209/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 747, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 747, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 746, cos1053o2c k) + cos1053o2c 747 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 746) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_746
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 747 - ((-3925461/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_747).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_748 : ((159157833/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 748, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 748, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 747, cos1053o2c k) + cos1053o2c 748 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 747) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_747
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 748 - ((-312293/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_748).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_749 : ((37942707/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 749, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 749, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 748, cos1053o2c k) + cos1053o2c 749 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 748) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_748
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 749 - ((-1477201/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_749).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_750 : ((15048853/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 750, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 750, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 749, cos1053o2c k) + cos1053o2c 750 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 749) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_749
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 750 - ((-640649/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_750).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_751 : ((77954649/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 751, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 751, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 750, cos1053o2c k) + cos1053o2c 751 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 750) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_750
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 751 - ((677721/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_751).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_752 : ((6618801/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 752, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 752, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 751, cos1053o2c k) + cos1053o2c 752 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 751) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_751
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 752 - ((9561727/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_752).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_753 : ((174669837/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 753, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 753, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 752, cos1053o2c k) + cos1053o2c 753 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 752) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_752
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 753 - ((2300203/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_753).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_754 : ((179193861/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 754, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 754, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 753, cos1053o2c k) + cos1053o2c 754 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 753) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_753
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 754 - ((141407/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_754).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_755 : ((88465047/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 755, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 755, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 754, cos1053o2c k) + cos1053o2c 755 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 754) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_754
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 755 - ((-2262767/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_755).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_756 : ((16894211/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 756, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 756, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 755, cos1053o2c k) + cos1053o2c 756 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 755) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_755
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 756 - ((-998373/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_756).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_757 : ((39738441/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 757, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 757, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 756, cos1053o2c k) + cos1053o2c 757 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 756) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_756
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 757 - ((-4993673/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_757).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_758 : ((151604229/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 758, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 758, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 757, cos1053o2c k) + cos1053o2c 758 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 757) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_757
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 758 - ((-1469707/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_758).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_759 : ((150293869/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 759, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 759, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 758, cos1053o2c k) + cos1053o2c 759 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 758) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_758
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 759 - ((-16367/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_759).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_760 : ((38905267/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 760, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 760, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 759, cos1053o2c k) + cos1053o2c 760 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 759) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_759
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 760 - ((5328199/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_760).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_761 : ((3302463/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 761, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 761, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 760, cos1053o2c k) + cos1053o2c 761 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 760) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_760
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 761 - ((4751541/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_761).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_762 : ((174427857/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 762, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 762, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 761, cos1053o2c k) + cos1053o2c 762 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 761) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_761
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 762 - ((9305707/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_762).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_763 : ((17926899/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 763, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 763, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 762, cos1053o2c k) + cos1053o2c 763 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 762) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_762
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 763 - ((4842133/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_763).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_764 : ((88718719/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 764, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 764, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 763, cos1053o2c k) + cos1053o2c 764 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 763) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_763
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 764 - ((-228819/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_764).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_765 : ((169775073/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 765, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 765, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 764, cos1053o2c k) + cos1053o2c 765 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 764) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_764
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 765 - ((-1532273/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_765).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_766 : ((31954919/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 766, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 766, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 765, cos1053o2c k) + cos1053o2c 766 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 765) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_765
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 766 - ((-4999739/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_766).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_767 : ((151977179/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 767, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 767, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 766, cos1053o2c k) + cos1053o2c 767 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 766) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_766
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 767 - ((-121819/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_767).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_768 : ((74955003/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 768, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 768, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 767, cos1053o2c k) + cos1053o2c 768 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 767) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_767
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 768 - ((-2066173/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_768).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_769 : ((7724993/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 769, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 769, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 768, cos1053o2c k) + cos1053o2c 769 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 768) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_768
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 769 - ((2295427/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_769).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_770 : ((10229481/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 770, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 770, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 769, cos1053o2c k) + cos1053o2c 770 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 769) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_769
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 770 - ((2293209/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_770).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_771 : ((17329847/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 771, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 771, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 770, cos1053o2c k) + cos1053o2c 771 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 770) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_770
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 771 - ((4813887/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_771).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_772 : ((17906417/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 772, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 772, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 771, cos1053o2c k) + cos1053o2c 772 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 771) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_771
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 772 - ((57667/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_772).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_773 : ((35678919/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 773, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 773, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 772, cos1053o2c k) + cos1053o2c 773 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 772) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_772
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 773 - ((-26743/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_773).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_774 : ((171595033/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 774, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 774, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 773, cos1053o2c k) + cos1053o2c 774 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 773) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_773
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 774 - ((-3399281/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_774).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_775 : ((161696693/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 775, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 775, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 774, cos1053o2c k) + cos1053o2c 775 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 774) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_774
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 775 - ((-494867/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_775).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_776 : ((76547801/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 776, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 776, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 775, cos1053o2c k) + cos1053o2c 776 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 775) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_775
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 776 - ((-8600091/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_776).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_777 : ((149597509/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 777, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 777, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 776, cos1053o2c k) + cos1053o2c 777 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 776) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_776
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 777 - ((-3497093/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_777).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_778 : ((19092681/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 778, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 778, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 777, cos1053o2c k) + cos1053o2c 778 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 777) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_777
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 778 - ((3144939/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_778).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_779 : ((32226927/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 779, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 779, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 778, cos1053o2c k) + cos1053o2c 779 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 778) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_778
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 779 - ((8394187/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_779).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_780 : ((171082811/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 780, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 780, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 779, cos1053o2c k) + cos1053o2c 780 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 779) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_779
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 780 - ((1243647/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_780).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_781 : ((44555779/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 781, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 781, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 780, cos1053o2c k) + cos1053o2c 781 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 780) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_780
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 781 - ((1428261/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_781).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_782 : ((35887167/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 782, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 782, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 781, cos1053o2c k) + cos1053o2c 782 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 781) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_781
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 782 - ((1213719/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_782).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_783 : ((87099113/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 783, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 783, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 782, cos1053o2c k) + cos1053o2c 783 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 782) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_782
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 783 - ((-5236609/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_783).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_784 : ((41198849/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 784, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 784, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 783, cos1053o2c k) + cos1053o2c 784 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 783) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_783
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 784 - ((-940183/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_784).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_785 : ((155313111/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 785, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 785, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 784, cos1053o2c k) + cos1053o2c 785 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 784) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_784
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 785 - ((-1896257/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_785).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_786 : ((5994259/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 786, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 786, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 785, cos1053o2c k) + cos1053o2c 786 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 785) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_785
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 786 - ((-1363909/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_786).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_787 : ((75388997/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 787, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 787, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 786, cos1053o2c k) + cos1053o2c 787 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 786) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_786
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 787 - ((922519/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_787).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_788 : ((19709121/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 788, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 788, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 787, cos1053o2c k) + cos1053o2c 788 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 787) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_787
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 788 - ((3447987/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_788).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_789 : ((167571171/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 789, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 789, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 788, cos1053o2c k) + cos1053o2c 789 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 788) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_788
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 789 - ((9899203/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_789).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_790 : ((88112303/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 790, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 790, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 789, cos1053o2c k) + cos1053o2c 790 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 789) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_789
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 790 - ((1730887/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_790).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_791 : ((89966463/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 791, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 791, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 790, cos1053o2c k) + cos1053o2c 791 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 790) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_790
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 791 - ((92733/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_791).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_792 : ((88559371/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 792, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 792, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 791, cos1053o2c k) + cos1053o2c 792 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 791) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_791
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 792 - ((-21978/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_792).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_793 : ((84493079/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 793, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 793, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 792, cos1053o2c k) + cos1053o2c 793 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 792) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_792
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 793 - ((-63528/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_793).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_794 : ((31798817/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 794, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 794, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 793, cos1053o2c k) + cos1053o2c 794 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 793) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_793
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 794 - ((-9991073/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_794).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_795 : ((151376727/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 795, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 795, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 794, cos1053o2c k) + cos1053o2c 795 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 794) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_794
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 795 - ((-3808179/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_795).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_796 : ((7467481/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 796, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 796, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 795, cos1053o2c k) + cos1053o2c 796 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 795) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_795
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 796 - ((-2026107/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_796).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_797 : ((153761177/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 797, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 797, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 796, cos1053o2c k) + cos1053o2c 797 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 796) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_796
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 797 - ((4412557/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_797).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_798 : ((162748841/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 798, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 798, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 797, cos1053o2c k) + cos1053o2c 798 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 797) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_797
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 798 - ((1123583/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_798).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_799 : ((43134221/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 799, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 799, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 798, cos1053o2c k) + cos1053o2c 799 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 798) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_798
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 799 - ((9789043/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_799).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_800 : ((89513751/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 800, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 800, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 799, cos1053o2c k) + cos1053o2c 800 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 799) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_799
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 800 - ((3245809/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_800).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_801 : ((17951409/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 801, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 801, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 800, cos1053o2c k) + cos1053o2c 801 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 800) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_800
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 801 - ((121897/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_801).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_802 : ((34759941/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 802, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 802, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 801, cos1053o2c k) + cos1053o2c 802 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 801) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_801
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 802 - ((-1142677/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_802).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_803 : ((164265019/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 803, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 803, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 802, cos1053o2c k) + cos1053o2c 803 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 802) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_802
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 803 - ((-4766843/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_803).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_804 : ((154865639/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 804, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 804, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 803, cos1053o2c k) + cos1053o2c 804 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 803) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_803
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 804 - ((-469919/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_804).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_805 : ((74743779/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 805, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 805, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 804, cos1053o2c k) + cos1053o2c 805 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 804) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_804
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 805 - ((-5377081/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_805).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_806 : ((75172417/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 806, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 806, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 805, cos1053o2c k) + cos1053o2c 806 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 805) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_805
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 806 - ((214569/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_806).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_807 : ((4908669/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 807, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 807, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 806, cos1053o2c k) + cos1053o2c 807 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 806) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_806
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 807 - ((3366787/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_807).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_808 : ((166914777/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 808, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 808, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 807, cos1053o2c k) + cos1053o2c 808 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 807) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_807
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 808 - ((9838369/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_808).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_809 : ((35164813/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 809, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 809, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 808, cos1053o2c k) + cos1053o2c 809 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 808) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_808
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 809 - ((556893/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_809).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_810 : ((36033141/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 810, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 810, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 809, cos1053o2c k) + cos1053o2c 810 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 809) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_809
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 810 - ((54283/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_810).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_811 : ((8908717/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 811, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 811, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 810, cos1053o2c k) + cos1053o2c 811 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 810) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_810
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 811 - ((-398073/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_811).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_812 : ((85332973/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 812, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 812, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 811, cos1053o2c k) + cos1053o2c 812 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 811) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_811
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 812 - ((-3753697/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_812).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_813 : ((80346009/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 813, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 813, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 812, cos1053o2c k) + cos1053o2c 813 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 812) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_812
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 813 - ((-155827/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_813).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_814 : ((3045827/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 814, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 814, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 813, cos1053o2c k) + cos1053o2c 814 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 813) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_813
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 814 - ((-2099917/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_814).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_815 : ((37213499/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 815, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 815, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 814, cos1053o2c k) + cos1053o2c 815 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 814) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_814
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 815 - ((-1718177/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_815).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_816 : ((151758567/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 816, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 816, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 815, cos1053o2c k) + cos1053o2c 816 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 815) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_815
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 816 - ((2905571/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_816).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_817 : ((39957717/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 817, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 817, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 816, cos1053o2c k) + cos1053o2c 817 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 816) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_816
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 817 - ((8073301/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_817).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_818 : ((84914519/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 818, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 818, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 817, cos1053o2c k) + cos1053o2c 818 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 817) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_817
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 818 - ((999917/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_818).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_819 : ((177751753/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 819, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 819, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 818, cos1053o2c k) + cos1053o2c 819 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 818) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_818
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 819 - ((1584743/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_819).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_820 : ((180439251/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 820, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 820, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 819, cos1053o2c k) + cos1053o2c 820 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 819) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_819
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 820 - ((1344249/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_820).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_821 : ((176826763/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 821, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 821, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 820, cos1053o2c k) + cos1053o2c 821 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 820) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_820
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 821 - ((-112859/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_821).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_822 : ((33671111/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 822, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 822, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 821, cos1053o2c k) + cos1053o2c 822 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 821) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_821
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 822 - ((-132347/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_822).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_823 : ((158386323/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 823, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 823, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 822, cos1053o2c k) + cos1053o2c 823 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 822) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_822
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 823 - ((-1246029/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_823).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_824 : ((75430533/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 824, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 824, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 823, cos1053o2c k) + cos1053o2c 824 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 823) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_823
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 824 - ((-7524257/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_824).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_825 : ((74372101/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 825, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 825, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 824, cos1053o2c k) + cos1053o2c 825 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 824) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_824
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 825 - ((-264483/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_825).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_826 : ((38215701/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 826, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 826, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 825, cos1053o2c k) + cos1053o2c 826 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 825) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_825
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 826 - ((2059801/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_826).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_827 : ((161593251/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 827, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 827, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 826, cos1053o2c k) + cos1053o2c 827 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 826) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_826
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 827 - ((8731447/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_827).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_828 : ((171511593/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 828, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 828, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 827, cos1053o2c k) + cos1053o2c 828 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 827) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_827
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 828 - ((4959671/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_828).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_829 : ((44685287/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 829, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 829, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 828, cos1053o2c k) + cos1053o2c 829 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 828) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_828
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 829 - ((1446111/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_829).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_830 : ((18046613/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 830, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 830, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 829, cos1053o2c k) + cos1053o2c 830 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 829) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_829
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 830 - ((862991/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_830).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_831 : ((35204343/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 831, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 831, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 830, cos1053o2c k) + cos1053o2c 831 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 830) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_830
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 831 - ((-888683/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_831).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_832 : ((6685503/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 832, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 832, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 831, cos1053o2c k) + cos1053o2c 832 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 831) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_831
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 832 - ((-444157/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_832).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_833 : ((157256917/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 833, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 833, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 832, cos1053o2c k) + cos1053o2c 833 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 832) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_832
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 833 - ((-4939829/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_833).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_834 : ((3754903/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 834, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 834, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 833, cos1053o2c k) + cos1053o2c 834 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 833) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_833
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 834 - ((-7059797/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_834).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_835 : ((29734413/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 835, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 835, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 834, cos1053o2c k) + cos1053o2c 835 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 834) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_834
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 835 - ((-304611/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_835).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_836 : ((153264601/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 836, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 836, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 835, cos1053o2c k) + cos1053o2c 836 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 835) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_835
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 836 - ((35887/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_836).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_837 : ((162205621/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 837, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 837, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 836, cos1053o2c k) + cos1053o2c 837 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 836) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_836
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 837 - ((447101/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_837).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_838 : ((34413911/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 838, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 838, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 837, cos1053o2c k) + cos1053o2c 838 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 837) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_837
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 838 - ((4932467/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_838).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_839 : ((179089607/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 839, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 839, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 838, cos1053o2c k) + cos1053o2c 839 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 838) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_838
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 839 - ((1755263/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_839).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_840 : ((45148801/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 840, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 840, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 839, cos1053o2c k) + cos1053o2c 840 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 839) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_839
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 840 - ((1506597/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_840).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_841 : ((176019093/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 841, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 841, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 840, cos1053o2c k) + cos1053o2c 841 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 840) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_840
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 841 - ((-4575111/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_841).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_842 : ((167102001/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 842, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 842, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 841, cos1053o2c k) + cos1053o2c 842 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 841) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_841
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 842 - ((-2229023/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_842).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_843 : ((1257767/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 843, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 843, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 842, cos1053o2c k) + cos1053o2c 843 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 842) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_842
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 843 - ((-4940063/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_843).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_844 : ((37526207/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 844, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 844, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 843, cos1053o2c k) + cos1053o2c 844 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 843) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_843
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 844 - ((-7115047/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_844).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_845 : ((74215091/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 845, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 845, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 844, cos1053o2c k) + cos1053o2c 845 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 844) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_844
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 845 - ((-836823/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_845).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_846 : ((9551227/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 846, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 846, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 845, cos1053o2c k) + cos1053o2c 846 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 845) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_845
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 846 - ((87809/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_846).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_847 : ((40405403/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 847, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 847, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 846, cos1053o2c k) + cos1053o2c 847 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 846) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_846
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 847 - ((440149/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_847).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_848 : ((171540121/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 848, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 848, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 847, cos1053o2c k) + cos1053o2c 848 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 847) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_847
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 848 - ((9919509/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_848).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_849 : ((178873409/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 849, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 849, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 848, cos1053o2c k) + cos1053o2c 849 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 848) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_848
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 849 - ((458393/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_849).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_850 : ((180893947/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 850, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 850, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 849, cos1053o2c k) + cos1053o2c 850 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 849) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_849
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 850 - ((1010769/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_850).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_851 : ((88428227/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 851, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 851, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 850, cos1053o2c k) + cos1053o2c 851 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 850) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_850
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 851 - ((-4036493/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_851).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_852 : ((84131421/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 852, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 852, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 851, cos1053o2c k) + cos1053o2c 852 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 851) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_851
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 852 - ((-2148153/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_852).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_853 : ((39573579/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 853, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 853, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 852, cos1053o2c k) + cos1053o2c 853 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 852) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_852
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 853 - ((-4983763/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_853).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_854 : ((150628551/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 854, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 854, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 853, cos1053o2c k) + cos1053o2c 854 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 853) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_853
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 854 - ((-1532953/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_854).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_855 : ((29616813/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 855, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 855, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 854, cos1053o2c k) + cos1053o2c 855 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 854) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_854
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 855 - ((-1271743/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_855).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_856 : ((473717/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 856, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 856, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 855, cos1053o2c k) + cos1053o2c 856 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 855) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_855
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 856 - ((28051/80000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_856).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_857 : ((7992709/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 857, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 857, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 856, cos1053o2c k) + cos1053o2c 857 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 856) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_856
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 857 - ((413287/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_857).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_858 : ((42462969/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 858, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 858, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 857, cos1053o2c k) + cos1053o2c 858 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 857) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_857
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 858 - ((1249837/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_858).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_859 : ((88967141/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 859, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 859, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 858, cos1053o2c k) + cos1053o2c 859 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 858) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_858
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 859 - ((4041703/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_859).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_860 : ((90581169/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 860, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 860, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 859, cos1053o2c k) + cos1053o2c 860 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 859) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_859
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 860 - ((25227/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_860).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_861 : ((89183999/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 861, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 861, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 860, cos1053o2c k) + cos1053o2c 861 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 860) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_860
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 861 - ((-139667/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_861).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_862 : ((85284929/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 862, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 862, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 861, cos1053o2c k) + cos1053o2c 862 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 861) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_861
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 862 - ((-389857/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_862).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_863 : ((80295369/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 863, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 863, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 862, cos1053o2c k) + cos1053o2c 863 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 862) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_862
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 863 - ((-249453/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_863).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_864 : ((152031093/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 864, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 864, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 863, cos1053o2c k) + cos1053o2c 864 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 863) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_863
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 864 - ((-1711729/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_864).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_865 : ((147969253/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 865, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 865, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 864, cos1053o2c k) + cos1053o2c 865 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 864) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_864
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 865 - ((-101521/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_865).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_866 : ((37464587/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 866, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 866, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 865, cos1053o2c k) + cos1053o2c 866 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 865) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_865
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 866 - ((378019/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_866).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_867 : ((31403021/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 867, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 867, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 866, cos1053o2c k) + cos1053o2c 867 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 866) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_866
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 867 - ((7157757/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_867).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_868 : ((33375291/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 868, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 868, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 867, cos1053o2c k) + cos1053o2c 868 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 867) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_867
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 868 - ((197247/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_868).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_869 : ((175922549/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 869, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 869, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 868, cos1053o2c k) + cos1053o2c 869 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 868) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_868
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 869 - ((4523547/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_869).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_870 : ((36187029/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 870, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 870, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 869, cos1053o2c k) + cos1053o2c 870 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 869) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_869
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 870 - ((1253399/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_870).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_871 : ((90069387/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 871, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 871, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 870, cos1053o2c k) + cos1053o2c 871 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 870) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_870
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 871 - ((-795371/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_871).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_872 : ((173820497/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 872, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 872, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 871, cos1053o2c k) + cos1053o2c 872 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 871) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_871
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 872 - ((-6317277/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_872).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_873 : ((164218939/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 873, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 873, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 872, cos1053o2c k) + cos1053o2c 873 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 872) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_872
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 873 - ((-4800279/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_873).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_874 : ((154722891/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 874, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 874, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 873, cos1053o2c k) + cos1053o2c 874 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 873) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_873
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 874 - ((-1186881/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_874).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_875 : ((148673203/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 875, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 875, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 874, cos1053o2c k) + cos1053o2c 875 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 874) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_874
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 875 - ((-378043/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_875).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_876 : ((74095031/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 876, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 876, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 875, cos1053o2c k) + cos1053o2c 876 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 875) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_875
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 876 - ((-482141/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_876).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_877 : ((76718407/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 877, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 877, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 876, cos1053o2c k) + cos1053o2c 877 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 876) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_876
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 877 - ((655969/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_877).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_878 : ((40643359/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 878, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 878, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 877, cos1053o2c k) + cos1053o2c 878 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 877) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_877
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 878 - ((4568811/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_878).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_879 : ((172409133/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 879, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 879, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 878, cos1053o2c k) + cos1053o2c 879 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 878) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_878
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 879 - ((9836697/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_879).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_880 : ((89759857/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 880, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 880, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 879, cos1053o2c k) + cos1053o2c 880 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 879) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_879
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 880 - ((7111581/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_880).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_881 : ((181438699/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 881, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 881, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 880, cos1053o2c k) + cos1053o2c 881 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 880) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_880
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 881 - ((383997/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_881).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_882 : ((4437653/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 882, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 882, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 881, cos1053o2c k) + cos1053o2c 882 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 881) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_881
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 882 - ((-3931579/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_882).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_883 : ((84543333/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 883, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 883, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 882, cos1053o2c k) + cos1053o2c 883 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 882) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_882
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 883 - ((-4209227/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_883).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_884 : ((159088991/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 884, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 884, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 883, cos1053o2c k) + cos1053o2c 884 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 883) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_883
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 884 - ((-399867/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_884).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_885 : ((30191063/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 885, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 885, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 884, cos1053o2c k) + cos1053o2c 885 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 884) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_884
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 885 - ((-2033169/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_885).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_886 : ((18434603/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 886, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 886, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 885, cos1053o2c k) + cos1053o2c 886 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 885) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_885
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 886 - ((-3477491/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_886).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_887 : ((74920221/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 887, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 887, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 886, cos1053o2c k) + cos1053o2c 887 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 886) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_886
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 887 - ((1182309/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_887).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_888 : ((157232123/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 888, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 888, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 887, cos1053o2c k) + cos1053o2c 888 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 887) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_887
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 888 - ((7392681/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_888).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_889 : ((83562193/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 889, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 889, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 888, cos1053o2c k) + cos1053o2c 889 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 888) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_888
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 889 - ((9893263/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_889).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_890 : ((176146677/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 890, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 890, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 889, cos1053o2c k) + cos1053o2c 890 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 889) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_889
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 890 - ((9023291/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_890).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_891 : ((181234477/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 891, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 891, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 890, cos1053o2c k) + cos1053o2c 891 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 890) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_890
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 891 - ((6361/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_891).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_892 : ((90333431/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 892, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 892, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 891, cos1053o2c k) + cos1053o2c 892 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 891) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_891
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 892 - ((-113323/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_892).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_893 : ((4366031/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 893, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 893, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 892, cos1053o2c k) + cos1053o2c 893 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 892) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_892
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 893 - ((-3012311/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_893).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_894 : ((165195989/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 894, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 894, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 893, cos1053o2c k) + cos1053o2c 894 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 893) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_893
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 894 - ((-9444251/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_894).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_895 : ((31103003/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 895, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 895, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 894, cos1053o2c k) + cos1053o2c 895 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 894) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_894
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 895 - ((-4839987/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_895).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_896 : ((74425709/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 896, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 896, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 895, cos1053o2c k) + cos1053o2c 896 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 895) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_895
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 896 - ((-6662597/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_896).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_897 : ((7371797/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 897, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 897, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 896, cos1053o2c k) + cos1053o2c 897 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 896) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_896
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 897 - ((-707239/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_897).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_898 : ((75868417/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 898, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 898, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 897, cos1053o2c k) + cos1053o2c 898 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 897) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_897
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 898 - ((2150947/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_898).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_899 : ((16031241/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 899, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 899, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 898, cos1053o2c k) + cos1053o2c 899 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 898) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_898
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 899 - ((134009/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_899).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_900 : ((21287649/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 900, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 900, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 899, cos1053o2c k) + cos1053o2c 900 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 899) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_899
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 900 - ((4994891/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_900).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_901 : ((178381121/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 901, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 901, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 900, cos1053o2c k) + cos1053o2c 901 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 900) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_900
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 901 - ((8080929/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_901).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_902 : ((181873467/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 902, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 902, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 901, cos1053o2c k) + cos1053o2c 902 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 901) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_901
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 902 - ((1746673/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_902).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_903 : ((179626773/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 903, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 903, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 902, cos1053o2c k) + cos1053o2c 903 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 902) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_902
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 903 - ((-1122847/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_903).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_904 : ((172388203/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 904, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 904, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 903, cos1053o2c k) + cos1053o2c 904 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 903) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_903
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 904 - ((-723757/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_904).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_905 : ((40636953/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 905, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 905, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 904, cos1053o2c k) + cos1053o2c 905 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 904) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_904
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 905 - ((-9839391/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_905).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_906 : ((153344009/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 906, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 906, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 905, cos1053o2c k) + cos1053o2c 906 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 905) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_905
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 906 - ((-9202803/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_906).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_907 : ((147795911/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 907, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 907, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 906, cos1053o2c k) + cos1053o2c 907 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 906) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_906
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 907 - ((-2773549/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_907).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_908 : ((73858137/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 908, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 908, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 907, cos1053o2c k) + cos1053o2c 908 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 907) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_907
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 908 - ((-78637/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_908).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_909 : ((153125519/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 909, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 909, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 908, cos1053o2c k) + cos1053o2c 909 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 908) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_908
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 909 - ((1082049/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_909).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_910 : ((162254369/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 910, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 910, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 909, cos1053o2c k) + cos1053o2c 910 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 909) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_909
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 910 - ((182597/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_910).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_911 : ((21516101/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 911, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 911, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 910, cos1053o2c k) + cos1053o2c 911 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 910) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_910
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 911 - ((9875439/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_911).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_912 : ((89770967/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 912, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 912, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 911, cos1053o2c k) + cos1053o2c 912 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 911) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_911
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 912 - ((3707063/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_912).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_913 : ((182094163/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 913, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 913, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 912, cos1053o2c k) + cos1053o2c 913 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 912) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_912
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 913 - ((2553229/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_913).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_914 : ((178964799/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 914, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 914, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 913, cos1053o2c k) + cos1053o2c 914 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 913) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_913
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 914 - ((-782091/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_914).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_915 : ((171168559/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 915, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 915, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 914, cos1053o2c k) + cos1053o2c 915 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 914) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_914
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 915 - ((-194881/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_915).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_916 : ((6448773/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 916, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 916, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 915, cos1053o2c k) + cos1053o2c 916 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 915) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_915
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 916 - ((-4974117/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_916).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_917 : ((152314763/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 917, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 917, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 916, cos1053o2c k) + cos1053o2c 917 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 916) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_916
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 917 - ((-4451781/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_917).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_918 : ((73653869/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 918, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 918, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 917, cos1053o2c k) + cos1053o2c 918 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 917) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_917
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 918 - ((-200241/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_918).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_919 : ((147796129/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 919, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 919, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 918, cos1053o2c k) + cos1053o2c 919 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 918) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_918
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 919 - ((489391/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_919).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_920 : ((9601119/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 920, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 920, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 919, cos1053o2c k) + cos1053o2c 920 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 919) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_919
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 920 - ((232911/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_920).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_921 : ((162913607/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 921, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 921, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 920, cos1053o2c k) + cos1053o2c 921 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 920) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_920
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 921 - ((9296703/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_921).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_922 : ((34544973/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 922, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 922, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 921, cos1053o2c k) + cos1053o2c 922 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 921) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_921
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 922 - ((4906129/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_922).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_923 : ((179939043/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 923, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 923, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 922, cos1053o2c k) + cos1053o2c 923 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 922) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_922
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 923 - ((3607589/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_923).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_924 : ((91137601/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 924, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 924, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 923, cos1053o2c k) + cos1053o2c 924 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 923) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_923
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 924 - ((2337159/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_924).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_925 : ((178999571/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 925, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 925, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 924, cos1053o2c k) + cos1053o2c 925 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 924) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_924
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 925 - ((-3274631/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_925).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_926 : ((85574891/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 926, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 926, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 925, cos1053o2c k) + cos1053o2c 926 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 925) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_925
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 926 - ((-7848789/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_926).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_927 : ((32239757/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 927, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 927, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 926, cos1053o2c k) + cos1053o2c 927 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 926) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_926
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 927 - ((-9949997/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_927).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_928 : ((30454277/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 928, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 928, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 927, cos1053o2c k) + cos1053o2c 928 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 927) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_927
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 928 - ((-5579/6250 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_928).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_929 : ((36790569/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 929, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 929, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 928, cos1053o2c k) + cos1053o2c 929 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 928) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_928
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 929 - ((-5108109/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_929).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_930 : ((147464039/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 930, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 930, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 929, cos1053o2c k) + cos1053o2c 930 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 929) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_929
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 930 - ((302763/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_930).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_931 : ((153077319/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 931, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 931, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 930, cos1053o2c k) + cos1053o2c 931 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 930) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_930
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 931 - ((140357/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_931).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_932 : ((10140611/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 932, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 932, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 931, cos1053o2c k) + cos1053o2c 932 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 931) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_931
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 932 - ((9173457/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_932).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_933 : ((5379019/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 933, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 933, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 932, cos1053o2c k) + cos1053o2c 933 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 932) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_932
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 933 - ((1234979/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_933).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_934 : ((2807049/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 934, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 934, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 933, cos1053o2c k) + cos1053o2c 934 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 933) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_933
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 934 - ((940441/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_934).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_935 : ((36498517/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 935, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 935, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 934, cos1053o2c k) + cos1053o2c 935 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 934) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_934
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 935 - ((2842449/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_935).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_936 : ((179780379/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 936, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 936, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 935, cos1053o2c k) + cos1053o2c 936 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 935) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_935
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 936 - ((-1355603/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_936).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_937 : ((86177327/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 937, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 937, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 936, cos1053o2c k) + cos1053o2c 937 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 936) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_936
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 937 - ((-296989/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_937).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_938 : ((81250969/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 938, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 938, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 937, cos1053o2c k) + cos1053o2c 938 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 937) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_937
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 938 - ((-2462929/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_938).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_939 : ((30649277/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 939, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 939, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 938, cos1053o2c k) + cos1053o2c 939 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 938) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_938
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 939 - ((-9254553/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_939).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_940 : ((73710079/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 940, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 940, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 939, cos1053o2c k) + cos1053o2c 940 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 939) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_939
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 940 - ((-5825227/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_940).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_941 : ((7339977/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 941, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 941, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 940, cos1053o2c k) + cos1053o2c 941 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 940) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_940
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 941 - ((-309809/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_941).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_942 : ((151568153/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 942, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 942, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 941, cos1053o2c k) + cos1053o2c 942 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 941) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_941
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 942 - ((4769613/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_942).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_943 : ((160270151/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 943, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 943, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 942, cos1053o2c k) + cos1053o2c 943 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 942) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_942
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 943 - ((4351499/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_943).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_944 : ((34051977/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 944, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 944, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 943, cos1053o2c k) + cos1053o2c 944 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 943) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_943
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 944 - ((4995367/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_944).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_945 : ((178509361/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 945, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 945, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 944, cos1053o2c k) + cos1053o2c 945 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 944) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_944
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 945 - ((2062619/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_945).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_946 : ((45631541/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 946, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 946, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 945, cos1053o2c k) + cos1053o2c 946 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 945) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_945
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 946 - ((4017803/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_946).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_947 : ((181102139/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 947, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 947, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 946, cos1053o2c k) + cos1053o2c 947 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 946) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_946
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 947 - ((-56921/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_947).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_948 : ((174670381/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 948, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 948, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 947, cos1053o2c k) + cos1053o2c 948 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 947) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_947
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 948 - ((-3215379/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_948).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_949 : ((165168419/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 949, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 949, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 948, cos1053o2c k) + cos1053o2c 949 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 948) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_948
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 949 - ((-4750481/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_949).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_950 : ((155447557/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 950, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 950, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 949, cos1053o2c k) + cos1053o2c 950 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 949) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_949
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 950 - ((-4859931/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_950).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_951 : ((2968331/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 951, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 951, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 950, cos1053o2c k) + cos1053o2c 951 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 950) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_950
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 951 - ((-7030007/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_951).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_952 : ((1827153/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 952, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 952, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 951, cos1053o2c k) + cos1053o2c 952 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 951) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_951
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 952 - ((-224331/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_952).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_953 : ((149378689/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 953, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 953, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 952, cos1053o2c k) + cos1053o2c 953 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 952) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_952
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 953 - ((3207449/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_953).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_954 : ((15707651/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 954, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 954, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 953, cos1053o2c k) + cos1053o2c 954 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 953) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_953
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 954 - ((7698821/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_954).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_955 : ((33395387/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 955, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 955, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 954, cos1053o2c k) + cos1053o2c 955 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 954) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_954
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 955 - ((396057/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_955).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_956 : ((176145113/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 956, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 956, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 955, cos1053o2c k) + cos1053o2c 956 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 955) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_955
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 956 - ((4584589/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_956).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_957 : ((90935919/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 957, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 957, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 956, cos1053o2c k) + cos1053o2c 957 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 956) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_956
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 957 - ((229109/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_957).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_958 : ((91235277/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 958, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 958, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 957, cos1053o2c k) + cos1053o2c 958 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 957) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_957
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 958 - ((149929/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_958).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_959 : ((88884781/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 959, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 959, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 958, cos1053o2c k) + cos1053o2c 959 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 958) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_958
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 959 - ((-587499/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_959).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_960 : ((8457731/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 960, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 960, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 959, cos1053o2c k) + cos1053o2c 960 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 959) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_959
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 960 - ((-4306971/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_960).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_961 : ((79577403/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 961, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 961, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 960, cos1053o2c k) + cos1053o2c 961 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 960) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_960
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 961 - ((-4999407/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_961).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_962 : ((30139407/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 962, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 962, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 961, cos1053o2c k) + cos1053o2c 962 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 961) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_961
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 962 - ((-8456771/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_962).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_963 : ((73124697/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 963, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 963, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 962, cos1053o2c k) + cos1053o2c 963 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 962) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_962
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 963 - ((-4446641/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_963).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_964 : ((73551687/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 964, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 964, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 963, cos1053o2c k) + cos1053o2c 964 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 963) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_963
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 964 - ((42749/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_964).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_965 : ((7650309/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 965, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 965, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 964, cos1053o2c k) + cos1053o2c 965 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 964) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_964
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 965 - ((2951903/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_965).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_966 : ((32447821/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 966, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 966, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 965, cos1053o2c k) + cos1053o2c 966 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 965) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_965
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 966 - ((369357/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_966).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_967 : ((172124697/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 967, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 967, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 966, cos1053o2c k) + cos1053o2c 967 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 966) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_966
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 967 - ((77239/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_967).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_968 : ((35960927/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 968, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 968, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 967, cos1053o2c k) + cos1053o2c 968 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 967) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_967
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 968 - ((3840469/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_968).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_969 : ((22883103/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 969, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 969, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 968, cos1053o2c k) + cos1053o2c 969 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 968) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_968
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 969 - ((3261189/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_969).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_970 : ((180971039/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 970, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 970, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 969, cos1053o2c k) + cos1053o2c 970 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 969) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_969
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 970 - ((-418557/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_970).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_971 : ((10883077/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 971, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 971, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 970, cos1053o2c k) + cos1053o2c 971 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 970) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_970
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 971 - ((-6840807/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_971).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_972 : ((16450527/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 972, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 972, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 971, cos1053o2c k) + cos1053o2c 972 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 971) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_971
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 972 - ((-4811481/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_972).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_973 : ((77427817/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 973, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 973, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 972, cos1053o2c k) + cos1053o2c 973 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 972) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_972
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 973 - ((-2412159/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_973).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_974 : ((147936119/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 974, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 974, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 973, cos1053o2c k) + cos1053o2c 974 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 973) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_973
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 974 - ((-1383703/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_974).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_975 : ((18214459/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 975, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 975, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 974, cos1053o2c k) + cos1053o2c 975 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 974) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_974
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 975 - ((-2219447/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_975).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_976 : ((9301341/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 976, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 976, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 975, cos1053o2c k) + cos1053o2c 976 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 975) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_975
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 976 - ((97087/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_976).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_977 : ((156366791/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 977, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 977, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 976, cos1053o2c k) + cos1053o2c 977 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 976) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_976
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 977 - ((1509267/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_977).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_978 : ((166209393/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 978, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 978, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 977, cos1053o2c k) + cos1053o2c 978 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 977) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_977
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 978 - ((4921801/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_978).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_979 : ((21945483/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 979, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 979, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 978, cos1053o2c k) + cos1053o2c 979 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 978) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_978
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 979 - ((9355471/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_979).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_980 : ((181790743/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 980, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 980, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 979, cos1053o2c k) + cos1053o2c 980 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 979) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_979
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 980 - ((6227879/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_980).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_981 : ((183138853/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 981, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 981, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 980, cos1053o2c k) + cos1053o2c 981 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 980) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_980
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 981 - ((134911/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_981).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_982 : ((17923329/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 982, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 982, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 981, cos1053o2c k) + cos1053o2c 982 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 981) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_981
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 982 - ((-3904563/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_982).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_983 : ((34234889/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 983, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 983, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 982, cos1053o2c k) + cos1053o2c 983 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 982) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_982
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 983 - ((-1611569/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_983).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_984 : ((80610961/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 984, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 984, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 983, cos1053o2c k) + cos1053o2c 984 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 983) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_983
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 984 - ((-9951523/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_984).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_985 : ((76078883/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 985, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 985, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 984, cos1053o2c k) + cos1053o2c 985 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 984) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_984
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 985 - ((-2265789/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_985).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_986 : ((9156771/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 986, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 986, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 985, cos1053o2c k) + cos1053o2c 986 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 985) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_985
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 986 - ((-564843/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_986).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_987 : ((4557579/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 987, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 987, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 986, cos1053o2c k) + cos1053o2c 987 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 986) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_986
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 987 - ((-83101/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_987).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_988 : ((150340087/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 988, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 988, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 987, cos1053o2c k) + cos1053o2c 988 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 987) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_987
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 988 - ((4498559/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_988).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_989 : ((79374909/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 989, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 989, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 988, cos1053o2c k) + cos1053o2c 989 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 988) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_988
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 989 - ((8410731/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_989).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_990 : ((168741037/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 990, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 990, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 989, cos1053o2c k) + cos1053o2c 990 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 989) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_989
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 990 - ((9992219/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_990).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_991 : ((177553449/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 991, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 991, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 990, cos1053o2c k) + cos1053o2c 991 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 990) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_990
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 991 - ((2203353/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_991).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_992 : ((45689851/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 992, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 992, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 991, cos1053o2c k) + cos1053o2c 992 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 991) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_991
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 992 - ((1041391/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_992).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_993 : ((91465281/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 993, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 993, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 992, cos1053o2c k) + cos1053o2c 993 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 992) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_992
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 993 - ((86079/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_993).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_994 : ((22252967/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 994, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 994, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 993, cos1053o2c k) + cos1053o2c 994 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 993) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_993
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 994 - ((-2452913/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_994).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_995 : ((16938781/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 995, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 995, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 994, cos1053o2c k) + cos1053o2c 995 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 994) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_994
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 995 - ((-4317463/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_995).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_996 : ((15938681/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 996, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 996, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 995, cos1053o2c k) + cos1053o2c 996 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 995) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_995
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 996 - ((-1 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_996).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_997 : ((150750517/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 997, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 997, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 996, cos1053o2c k) + cos1053o2c 997 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 996) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_996
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 997 - ((-8635293/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_997).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_998 : ((145829301/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 998, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 998, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 997, cos1053o2c k) + cos1053o2c 998 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 997) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_997
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 998 - ((-615027/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_998).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_999 : ((145957091/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 999, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 999, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 998, cos1053o2c k) + cos1053o2c 999 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 998) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_998
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 999 - ((12879/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_999).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1053o2_1000 : ((30218877/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 1000, cos1053o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 1000, cos1053o2c k)
      = (∑ k ∈ Finset.Icc 11 999, cos1053o2c k) + cos1053o2c 1000 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 999) (by norm_num) cos1053o2c
    simpa using h
  have hprev := psum1053o2_999
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1053o2c 1000 - ((2569147/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1053o2_br_1000).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 32768 in
theorem psum1053o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 1000 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos1053o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum1053o2_11
  · exact le_trans (by norm_num) psum1053o2_12
  · exact le_trans (by norm_num) psum1053o2_13
  · exact le_trans (by norm_num) psum1053o2_14
  · exact le_trans (by norm_num) psum1053o2_15
  · exact le_trans (by norm_num) psum1053o2_16
  · exact le_trans (by norm_num) psum1053o2_17
  · exact le_trans (by norm_num) psum1053o2_18
  · exact le_trans (by norm_num) psum1053o2_19
  · exact le_trans (by norm_num) psum1053o2_20
  · exact le_trans (by norm_num) psum1053o2_21
  · exact le_trans (by norm_num) psum1053o2_22
  · exact le_trans (by norm_num) psum1053o2_23
  · exact le_trans (by norm_num) psum1053o2_24
  · exact le_trans (by norm_num) psum1053o2_25
  · exact le_trans (by norm_num) psum1053o2_26
  · exact le_trans (by norm_num) psum1053o2_27
  · exact le_trans (by norm_num) psum1053o2_28
  · exact le_trans (by norm_num) psum1053o2_29
  · exact le_trans (by norm_num) psum1053o2_30
  · exact le_trans (by norm_num) psum1053o2_31
  · exact le_trans (by norm_num) psum1053o2_32
  · exact le_trans (by norm_num) psum1053o2_33
  · exact le_trans (by norm_num) psum1053o2_34
  · exact le_trans (by norm_num) psum1053o2_35
  · exact le_trans (by norm_num) psum1053o2_36
  · exact le_trans (by norm_num) psum1053o2_37
  · exact le_trans (by norm_num) psum1053o2_38
  · exact le_trans (by norm_num) psum1053o2_39
  · exact le_trans (by norm_num) psum1053o2_40
  · exact le_trans (by norm_num) psum1053o2_41
  · exact le_trans (by norm_num) psum1053o2_42
  · exact le_trans (by norm_num) psum1053o2_43
  · exact le_trans (by norm_num) psum1053o2_44
  · exact le_trans (by norm_num) psum1053o2_45
  · exact le_trans (by norm_num) psum1053o2_46
  · exact le_trans (by norm_num) psum1053o2_47
  · exact le_trans (by norm_num) psum1053o2_48
  · exact le_trans (by norm_num) psum1053o2_49
  · exact le_trans (by norm_num) psum1053o2_50
  · exact le_trans (by norm_num) psum1053o2_51
  · exact le_trans (by norm_num) psum1053o2_52
  · exact le_trans (by norm_num) psum1053o2_53
  · exact le_trans (by norm_num) psum1053o2_54
  · exact le_trans (by norm_num) psum1053o2_55
  · exact le_trans (by norm_num) psum1053o2_56
  · exact le_trans (by norm_num) psum1053o2_57
  · exact le_trans (by norm_num) psum1053o2_58
  · exact le_trans (by norm_num) psum1053o2_59
  · exact le_trans (by norm_num) psum1053o2_60
  · exact le_trans (by norm_num) psum1053o2_61
  · exact le_trans (by norm_num) psum1053o2_62
  · exact le_trans (by norm_num) psum1053o2_63
  · exact le_trans (by norm_num) psum1053o2_64
  · exact le_trans (by norm_num) psum1053o2_65
  · exact le_trans (by norm_num) psum1053o2_66
  · exact le_trans (by norm_num) psum1053o2_67
  · exact le_trans (by norm_num) psum1053o2_68
  · exact le_trans (by norm_num) psum1053o2_69
  · exact le_trans (by norm_num) psum1053o2_70
  · exact le_trans (by norm_num) psum1053o2_71
  · exact le_trans (by norm_num) psum1053o2_72
  · exact le_trans (by norm_num) psum1053o2_73
  · exact le_trans (by norm_num) psum1053o2_74
  · exact le_trans (by norm_num) psum1053o2_75
  · exact le_trans (by norm_num) psum1053o2_76
  · exact le_trans (by norm_num) psum1053o2_77
  · exact le_trans (by norm_num) psum1053o2_78
  · exact le_trans (by norm_num) psum1053o2_79
  · exact le_trans (by norm_num) psum1053o2_80
  · exact le_trans (by norm_num) psum1053o2_81
  · exact le_trans (by norm_num) psum1053o2_82
  · exact le_trans (by norm_num) psum1053o2_83
  · exact le_trans (by norm_num) psum1053o2_84
  · exact le_trans (by norm_num) psum1053o2_85
  · exact le_trans (by norm_num) psum1053o2_86
  · exact le_trans (by norm_num) psum1053o2_87
  · exact le_trans (by norm_num) psum1053o2_88
  · exact le_trans (by norm_num) psum1053o2_89
  · exact le_trans (by norm_num) psum1053o2_90
  · exact le_trans (by norm_num) psum1053o2_91
  · exact le_trans (by norm_num) psum1053o2_92
  · exact le_trans (by norm_num) psum1053o2_93
  · exact le_trans (by norm_num) psum1053o2_94
  · exact le_trans (by norm_num) psum1053o2_95
  · exact le_trans (by norm_num) psum1053o2_96
  · exact le_trans (by norm_num) psum1053o2_97
  · exact le_trans (by norm_num) psum1053o2_98
  · exact le_trans (by norm_num) psum1053o2_99
  · exact le_trans (by norm_num) psum1053o2_100
  · exact le_trans (by norm_num) psum1053o2_101
  · exact le_trans (by norm_num) psum1053o2_102
  · exact le_trans (by norm_num) psum1053o2_103
  · exact le_trans (by norm_num) psum1053o2_104
  · exact le_trans (by norm_num) psum1053o2_105
  · exact le_trans (by norm_num) psum1053o2_106
  · exact le_trans (by norm_num) psum1053o2_107
  · exact le_trans (by norm_num) psum1053o2_108
  · exact le_trans (by norm_num) psum1053o2_109
  · exact le_trans (by norm_num) psum1053o2_110
  · exact le_trans (by norm_num) psum1053o2_111
  · exact le_trans (by norm_num) psum1053o2_112
  · exact le_trans (by norm_num) psum1053o2_113
  · exact le_trans (by norm_num) psum1053o2_114
  · exact le_trans (by norm_num) psum1053o2_115
  · exact le_trans (by norm_num) psum1053o2_116
  · exact le_trans (by norm_num) psum1053o2_117
  · exact le_trans (by norm_num) psum1053o2_118
  · exact le_trans (by norm_num) psum1053o2_119
  · exact le_trans (by norm_num) psum1053o2_120
  · exact le_trans (by norm_num) psum1053o2_121
  · exact le_trans (by norm_num) psum1053o2_122
  · exact le_trans (by norm_num) psum1053o2_123
  · exact le_trans (by norm_num) psum1053o2_124
  · exact le_trans (by norm_num) psum1053o2_125
  · exact le_trans (by norm_num) psum1053o2_126
  · exact le_trans (by norm_num) psum1053o2_127
  · exact le_trans (by norm_num) psum1053o2_128
  · exact le_trans (by norm_num) psum1053o2_129
  · exact le_trans (by norm_num) psum1053o2_130
  · exact le_trans (by norm_num) psum1053o2_131
  · exact le_trans (by norm_num) psum1053o2_132
  · exact le_trans (by norm_num) psum1053o2_133
  · exact le_trans (by norm_num) psum1053o2_134
  · exact le_trans (by norm_num) psum1053o2_135
  · exact le_trans (by norm_num) psum1053o2_136
  · exact le_trans (by norm_num) psum1053o2_137
  · exact le_trans (by norm_num) psum1053o2_138
  · exact le_trans (by norm_num) psum1053o2_139
  · exact le_trans (by norm_num) psum1053o2_140
  · exact le_trans (by norm_num) psum1053o2_141
  · exact le_trans (by norm_num) psum1053o2_142
  · exact le_trans (by norm_num) psum1053o2_143
  · exact le_trans (by norm_num) psum1053o2_144
  · exact le_trans (by norm_num) psum1053o2_145
  · exact le_trans (by norm_num) psum1053o2_146
  · exact le_trans (by norm_num) psum1053o2_147
  · exact le_trans (by norm_num) psum1053o2_148
  · exact le_trans (by norm_num) psum1053o2_149
  · exact le_trans (by norm_num) psum1053o2_150
  · exact le_trans (by norm_num) psum1053o2_151
  · exact le_trans (by norm_num) psum1053o2_152
  · exact le_trans (by norm_num) psum1053o2_153
  · exact le_trans (by norm_num) psum1053o2_154
  · exact le_trans (by norm_num) psum1053o2_155
  · exact le_trans (by norm_num) psum1053o2_156
  · exact le_trans (by norm_num) psum1053o2_157
  · exact le_trans (by norm_num) psum1053o2_158
  · exact le_trans (by norm_num) psum1053o2_159
  · exact le_trans (by norm_num) psum1053o2_160
  · exact le_trans (by norm_num) psum1053o2_161
  · exact le_trans (by norm_num) psum1053o2_162
  · exact le_trans (by norm_num) psum1053o2_163
  · exact le_trans (by norm_num) psum1053o2_164
  · exact le_trans (by norm_num) psum1053o2_165
  · exact le_trans (by norm_num) psum1053o2_166
  · exact le_trans (by norm_num) psum1053o2_167
  · exact le_trans (by norm_num) psum1053o2_168
  · exact le_trans (by norm_num) psum1053o2_169
  · exact le_trans (by norm_num) psum1053o2_170
  · exact le_trans (by norm_num) psum1053o2_171
  · exact le_trans (by norm_num) psum1053o2_172
  · exact le_trans (by norm_num) psum1053o2_173
  · exact le_trans (by norm_num) psum1053o2_174
  · exact le_trans (by norm_num) psum1053o2_175
  · exact le_trans (by norm_num) psum1053o2_176
  · exact le_trans (by norm_num) psum1053o2_177
  · exact le_trans (by norm_num) psum1053o2_178
  · exact le_trans (by norm_num) psum1053o2_179
  · exact le_trans (by norm_num) psum1053o2_180
  · exact le_trans (by norm_num) psum1053o2_181
  · exact le_trans (by norm_num) psum1053o2_182
  · exact le_trans (by norm_num) psum1053o2_183
  · exact le_trans (by norm_num) psum1053o2_184
  · exact le_trans (by norm_num) psum1053o2_185
  · exact le_trans (by norm_num) psum1053o2_186
  · exact le_trans (by norm_num) psum1053o2_187
  · exact le_trans (by norm_num) psum1053o2_188
  · exact le_trans (by norm_num) psum1053o2_189
  · exact le_trans (by norm_num) psum1053o2_190
  · exact le_trans (by norm_num) psum1053o2_191
  · exact le_trans (by norm_num) psum1053o2_192
  · exact le_trans (by norm_num) psum1053o2_193
  · exact le_trans (by norm_num) psum1053o2_194
  · exact le_trans (by norm_num) psum1053o2_195
  · exact le_trans (by norm_num) psum1053o2_196
  · exact le_trans (by norm_num) psum1053o2_197
  · exact le_trans (by norm_num) psum1053o2_198
  · exact le_trans (by norm_num) psum1053o2_199
  · exact le_trans (by norm_num) psum1053o2_200
  · exact le_trans (by norm_num) psum1053o2_201
  · exact le_trans (by norm_num) psum1053o2_202
  · exact le_trans (by norm_num) psum1053o2_203
  · exact le_trans (by norm_num) psum1053o2_204
  · exact le_trans (by norm_num) psum1053o2_205
  · exact le_trans (by norm_num) psum1053o2_206
  · exact le_trans (by norm_num) psum1053o2_207
  · exact le_trans (by norm_num) psum1053o2_208
  · exact le_trans (by norm_num) psum1053o2_209
  · exact le_trans (by norm_num) psum1053o2_210
  · exact le_trans (by norm_num) psum1053o2_211
  · exact le_trans (by norm_num) psum1053o2_212
  · exact le_trans (by norm_num) psum1053o2_213
  · exact le_trans (by norm_num) psum1053o2_214
  · exact le_trans (by norm_num) psum1053o2_215
  · exact le_trans (by norm_num) psum1053o2_216
  · exact le_trans (by norm_num) psum1053o2_217
  · exact le_trans (by norm_num) psum1053o2_218
  · exact le_trans (by norm_num) psum1053o2_219
  · exact le_trans (by norm_num) psum1053o2_220
  · exact le_trans (by norm_num) psum1053o2_221
  · exact le_trans (by norm_num) psum1053o2_222
  · exact le_trans (by norm_num) psum1053o2_223
  · exact le_trans (by norm_num) psum1053o2_224
  · exact le_trans (by norm_num) psum1053o2_225
  · exact le_trans (by norm_num) psum1053o2_226
  · exact le_trans (by norm_num) psum1053o2_227
  · exact le_trans (by norm_num) psum1053o2_228
  · exact le_trans (by norm_num) psum1053o2_229
  · exact le_trans (by norm_num) psum1053o2_230
  · exact le_trans (by norm_num) psum1053o2_231
  · exact le_trans (by norm_num) psum1053o2_232
  · exact le_trans (by norm_num) psum1053o2_233
  · exact le_trans (by norm_num) psum1053o2_234
  · exact le_trans (by norm_num) psum1053o2_235
  · exact le_trans (by norm_num) psum1053o2_236
  · exact le_trans (by norm_num) psum1053o2_237
  · exact le_trans (by norm_num) psum1053o2_238
  · exact le_trans (by norm_num) psum1053o2_239
  · exact le_trans (by norm_num) psum1053o2_240
  · exact le_trans (by norm_num) psum1053o2_241
  · exact le_trans (by norm_num) psum1053o2_242
  · exact le_trans (by norm_num) psum1053o2_243
  · exact le_trans (by norm_num) psum1053o2_244
  · exact le_trans (by norm_num) psum1053o2_245
  · exact le_trans (by norm_num) psum1053o2_246
  · exact le_trans (by norm_num) psum1053o2_247
  · exact le_trans (by norm_num) psum1053o2_248
  · exact le_trans (by norm_num) psum1053o2_249
  · exact le_trans (by norm_num) psum1053o2_250
  · exact le_trans (by norm_num) psum1053o2_251
  · exact le_trans (by norm_num) psum1053o2_252
  · exact le_trans (by norm_num) psum1053o2_253
  · exact le_trans (by norm_num) psum1053o2_254
  · exact le_trans (by norm_num) psum1053o2_255
  · exact le_trans (by norm_num) psum1053o2_256
  · exact le_trans (by norm_num) psum1053o2_257
  · exact le_trans (by norm_num) psum1053o2_258
  · exact le_trans (by norm_num) psum1053o2_259
  · exact le_trans (by norm_num) psum1053o2_260
  · exact le_trans (by norm_num) psum1053o2_261
  · exact le_trans (by norm_num) psum1053o2_262
  · exact le_trans (by norm_num) psum1053o2_263
  · exact le_trans (by norm_num) psum1053o2_264
  · exact le_trans (by norm_num) psum1053o2_265
  · exact le_trans (by norm_num) psum1053o2_266
  · exact le_trans (by norm_num) psum1053o2_267
  · exact le_trans (by norm_num) psum1053o2_268
  · exact le_trans (by norm_num) psum1053o2_269
  · exact le_trans (by norm_num) psum1053o2_270
  · exact le_trans (by norm_num) psum1053o2_271
  · exact le_trans (by norm_num) psum1053o2_272
  · exact le_trans (by norm_num) psum1053o2_273
  · exact le_trans (by norm_num) psum1053o2_274
  · exact le_trans (by norm_num) psum1053o2_275
  · exact le_trans (by norm_num) psum1053o2_276
  · exact le_trans (by norm_num) psum1053o2_277
  · exact le_trans (by norm_num) psum1053o2_278
  · exact le_trans (by norm_num) psum1053o2_279
  · exact le_trans (by norm_num) psum1053o2_280
  · exact le_trans (by norm_num) psum1053o2_281
  · exact le_trans (by norm_num) psum1053o2_282
  · exact le_trans (by norm_num) psum1053o2_283
  · exact le_trans (by norm_num) psum1053o2_284
  · exact le_trans (by norm_num) psum1053o2_285
  · exact le_trans (by norm_num) psum1053o2_286
  · exact le_trans (by norm_num) psum1053o2_287
  · exact le_trans (by norm_num) psum1053o2_288
  · exact le_trans (by norm_num) psum1053o2_289
  · exact le_trans (by norm_num) psum1053o2_290
  · exact le_trans (by norm_num) psum1053o2_291
  · exact le_trans (by norm_num) psum1053o2_292
  · exact le_trans (by norm_num) psum1053o2_293
  · exact le_trans (by norm_num) psum1053o2_294
  · exact le_trans (by norm_num) psum1053o2_295
  · exact le_trans (by norm_num) psum1053o2_296
  · exact le_trans (by norm_num) psum1053o2_297
  · exact le_trans (by norm_num) psum1053o2_298
  · exact le_trans (by norm_num) psum1053o2_299
  · exact le_trans (by norm_num) psum1053o2_300
  · exact le_trans (by norm_num) psum1053o2_301
  · exact le_trans (by norm_num) psum1053o2_302
  · exact le_trans (by norm_num) psum1053o2_303
  · exact le_trans (by norm_num) psum1053o2_304
  · exact le_trans (by norm_num) psum1053o2_305
  · exact le_trans (by norm_num) psum1053o2_306
  · exact le_trans (by norm_num) psum1053o2_307
  · exact le_trans (by norm_num) psum1053o2_308
  · exact le_trans (by norm_num) psum1053o2_309
  · exact le_trans (by norm_num) psum1053o2_310
  · exact le_trans (by norm_num) psum1053o2_311
  · exact le_trans (by norm_num) psum1053o2_312
  · exact le_trans (by norm_num) psum1053o2_313
  · exact le_trans (by norm_num) psum1053o2_314
  · exact le_trans (by norm_num) psum1053o2_315
  · exact le_trans (by norm_num) psum1053o2_316
  · exact le_trans (by norm_num) psum1053o2_317
  · exact le_trans (by norm_num) psum1053o2_318
  · exact le_trans (by norm_num) psum1053o2_319
  · exact le_trans (by norm_num) psum1053o2_320
  · exact le_trans (by norm_num) psum1053o2_321
  · exact le_trans (by norm_num) psum1053o2_322
  · exact le_trans (by norm_num) psum1053o2_323
  · exact le_trans (by norm_num) psum1053o2_324
  · exact le_trans (by norm_num) psum1053o2_325
  · exact le_trans (by norm_num) psum1053o2_326
  · exact le_trans (by norm_num) psum1053o2_327
  · exact le_trans (by norm_num) psum1053o2_328
  · exact le_trans (by norm_num) psum1053o2_329
  · exact le_trans (by norm_num) psum1053o2_330
  · exact le_trans (by norm_num) psum1053o2_331
  · exact le_trans (by norm_num) psum1053o2_332
  · exact le_trans (by norm_num) psum1053o2_333
  · exact le_trans (by norm_num) psum1053o2_334
  · exact le_trans (by norm_num) psum1053o2_335
  · exact le_trans (by norm_num) psum1053o2_336
  · exact le_trans (by norm_num) psum1053o2_337
  · exact le_trans (by norm_num) psum1053o2_338
  · exact le_trans (by norm_num) psum1053o2_339
  · exact le_trans (by norm_num) psum1053o2_340
  · exact le_trans (by norm_num) psum1053o2_341
  · exact le_trans (by norm_num) psum1053o2_342
  · exact le_trans (by norm_num) psum1053o2_343
  · exact le_trans (by norm_num) psum1053o2_344
  · exact le_trans (by norm_num) psum1053o2_345
  · exact le_trans (by norm_num) psum1053o2_346
  · exact le_trans (by norm_num) psum1053o2_347
  · exact le_trans (by norm_num) psum1053o2_348
  · exact le_trans (by norm_num) psum1053o2_349
  · exact le_trans (by norm_num) psum1053o2_350
  · exact le_trans (by norm_num) psum1053o2_351
  · exact le_trans (by norm_num) psum1053o2_352
  · exact le_trans (by norm_num) psum1053o2_353
  · exact le_trans (by norm_num) psum1053o2_354
  · exact le_trans (by norm_num) psum1053o2_355
  · exact le_trans (by norm_num) psum1053o2_356
  · exact le_trans (by norm_num) psum1053o2_357
  · exact le_trans (by norm_num) psum1053o2_358
  · exact le_trans (by norm_num) psum1053o2_359
  · exact le_trans (by norm_num) psum1053o2_360
  · exact le_trans (by norm_num) psum1053o2_361
  · exact le_trans (by norm_num) psum1053o2_362
  · exact le_trans (by norm_num) psum1053o2_363
  · exact le_trans (by norm_num) psum1053o2_364
  · exact le_trans (by norm_num) psum1053o2_365
  · exact le_trans (by norm_num) psum1053o2_366
  · exact le_trans (by norm_num) psum1053o2_367
  · exact le_trans (by norm_num) psum1053o2_368
  · exact le_trans (by norm_num) psum1053o2_369
  · exact le_trans (by norm_num) psum1053o2_370
  · exact le_trans (by norm_num) psum1053o2_371
  · exact le_trans (by norm_num) psum1053o2_372
  · exact le_trans (by norm_num) psum1053o2_373
  · exact le_trans (by norm_num) psum1053o2_374
  · exact le_trans (by norm_num) psum1053o2_375
  · exact le_trans (by norm_num) psum1053o2_376
  · exact le_trans (by norm_num) psum1053o2_377
  · exact le_trans (by norm_num) psum1053o2_378
  · exact le_trans (by norm_num) psum1053o2_379
  · exact le_trans (by norm_num) psum1053o2_380
  · exact le_trans (by norm_num) psum1053o2_381
  · exact le_trans (by norm_num) psum1053o2_382
  · exact le_trans (by norm_num) psum1053o2_383
  · exact le_trans (by norm_num) psum1053o2_384
  · exact le_trans (by norm_num) psum1053o2_385
  · exact le_trans (by norm_num) psum1053o2_386
  · exact le_trans (by norm_num) psum1053o2_387
  · exact le_trans (by norm_num) psum1053o2_388
  · exact le_trans (by norm_num) psum1053o2_389
  · exact le_trans (by norm_num) psum1053o2_390
  · exact le_trans (by norm_num) psum1053o2_391
  · exact le_trans (by norm_num) psum1053o2_392
  · exact le_trans (by norm_num) psum1053o2_393
  · exact le_trans (by norm_num) psum1053o2_394
  · exact le_trans (by norm_num) psum1053o2_395
  · exact le_trans (by norm_num) psum1053o2_396
  · exact le_trans (by norm_num) psum1053o2_397
  · exact le_trans (by norm_num) psum1053o2_398
  · exact le_trans (by norm_num) psum1053o2_399
  · exact le_trans (by norm_num) psum1053o2_400
  · exact le_trans (by norm_num) psum1053o2_401
  · exact le_trans (by norm_num) psum1053o2_402
  · exact le_trans (by norm_num) psum1053o2_403
  · exact le_trans (by norm_num) psum1053o2_404
  · exact le_trans (by norm_num) psum1053o2_405
  · exact le_trans (by norm_num) psum1053o2_406
  · exact le_trans (by norm_num) psum1053o2_407
  · exact le_trans (by norm_num) psum1053o2_408
  · exact le_trans (by norm_num) psum1053o2_409
  · exact le_trans (by norm_num) psum1053o2_410
  · exact le_trans (by norm_num) psum1053o2_411
  · exact le_trans (by norm_num) psum1053o2_412
  · exact le_trans (by norm_num) psum1053o2_413
  · exact le_trans (by norm_num) psum1053o2_414
  · exact le_trans (by norm_num) psum1053o2_415
  · exact le_trans (by norm_num) psum1053o2_416
  · exact le_trans (by norm_num) psum1053o2_417
  · exact le_trans (by norm_num) psum1053o2_418
  · exact le_trans (by norm_num) psum1053o2_419
  · exact le_trans (by norm_num) psum1053o2_420
  · exact le_trans (by norm_num) psum1053o2_421
  · exact le_trans (by norm_num) psum1053o2_422
  · exact le_trans (by norm_num) psum1053o2_423
  · exact le_trans (by norm_num) psum1053o2_424
  · exact le_trans (by norm_num) psum1053o2_425
  · exact le_trans (by norm_num) psum1053o2_426
  · exact le_trans (by norm_num) psum1053o2_427
  · exact le_trans (by norm_num) psum1053o2_428
  · exact le_trans (by norm_num) psum1053o2_429
  · exact le_trans (by norm_num) psum1053o2_430
  · exact le_trans (by norm_num) psum1053o2_431
  · exact le_trans (by norm_num) psum1053o2_432
  · exact le_trans (by norm_num) psum1053o2_433
  · exact le_trans (by norm_num) psum1053o2_434
  · exact le_trans (by norm_num) psum1053o2_435
  · exact le_trans (by norm_num) psum1053o2_436
  · exact le_trans (by norm_num) psum1053o2_437
  · exact le_trans (by norm_num) psum1053o2_438
  · exact le_trans (by norm_num) psum1053o2_439
  · exact le_trans (by norm_num) psum1053o2_440
  · exact le_trans (by norm_num) psum1053o2_441
  · exact le_trans (by norm_num) psum1053o2_442
  · exact le_trans (by norm_num) psum1053o2_443
  · exact le_trans (by norm_num) psum1053o2_444
  · exact le_trans (by norm_num) psum1053o2_445
  · exact le_trans (by norm_num) psum1053o2_446
  · exact le_trans (by norm_num) psum1053o2_447
  · exact le_trans (by norm_num) psum1053o2_448
  · exact le_trans (by norm_num) psum1053o2_449
  · exact le_trans (by norm_num) psum1053o2_450
  · exact le_trans (by norm_num) psum1053o2_451
  · exact le_trans (by norm_num) psum1053o2_452
  · exact le_trans (by norm_num) psum1053o2_453
  · exact le_trans (by norm_num) psum1053o2_454
  · exact le_trans (by norm_num) psum1053o2_455
  · exact le_trans (by norm_num) psum1053o2_456
  · exact le_trans (by norm_num) psum1053o2_457
  · exact le_trans (by norm_num) psum1053o2_458
  · exact le_trans (by norm_num) psum1053o2_459
  · exact le_trans (by norm_num) psum1053o2_460
  · exact le_trans (by norm_num) psum1053o2_461
  · exact le_trans (by norm_num) psum1053o2_462
  · exact le_trans (by norm_num) psum1053o2_463
  · exact le_trans (by norm_num) psum1053o2_464
  · exact le_trans (by norm_num) psum1053o2_465
  · exact le_trans (by norm_num) psum1053o2_466
  · exact le_trans (by norm_num) psum1053o2_467
  · exact le_trans (by norm_num) psum1053o2_468
  · exact le_trans (by norm_num) psum1053o2_469
  · exact le_trans (by norm_num) psum1053o2_470
  · exact le_trans (by norm_num) psum1053o2_471
  · exact le_trans (by norm_num) psum1053o2_472
  · exact le_trans (by norm_num) psum1053o2_473
  · exact le_trans (by norm_num) psum1053o2_474
  · exact le_trans (by norm_num) psum1053o2_475
  · exact le_trans (by norm_num) psum1053o2_476
  · exact le_trans (by norm_num) psum1053o2_477
  · exact le_trans (by norm_num) psum1053o2_478
  · exact le_trans (by norm_num) psum1053o2_479
  · exact le_trans (by norm_num) psum1053o2_480
  · exact le_trans (by norm_num) psum1053o2_481
  · exact le_trans (by norm_num) psum1053o2_482
  · exact le_trans (by norm_num) psum1053o2_483
  · exact le_trans (by norm_num) psum1053o2_484
  · exact le_trans (by norm_num) psum1053o2_485
  · exact le_trans (by norm_num) psum1053o2_486
  · exact le_trans (by norm_num) psum1053o2_487
  · exact le_trans (by norm_num) psum1053o2_488
  · exact le_trans (by norm_num) psum1053o2_489
  · exact le_trans (by norm_num) psum1053o2_490
  · exact le_trans (by norm_num) psum1053o2_491
  · exact le_trans (by norm_num) psum1053o2_492
  · exact le_trans (by norm_num) psum1053o2_493
  · exact le_trans (by norm_num) psum1053o2_494
  · exact le_trans (by norm_num) psum1053o2_495
  · exact le_trans (by norm_num) psum1053o2_496
  · exact le_trans (by norm_num) psum1053o2_497
  · exact le_trans (by norm_num) psum1053o2_498
  · exact le_trans (by norm_num) psum1053o2_499
  · exact le_trans (by norm_num) psum1053o2_500
  · exact le_trans (by norm_num) psum1053o2_501
  · exact le_trans (by norm_num) psum1053o2_502
  · exact le_trans (by norm_num) psum1053o2_503
  · exact le_trans (by norm_num) psum1053o2_504
  · exact le_trans (by norm_num) psum1053o2_505
  · exact le_trans (by norm_num) psum1053o2_506
  · exact le_trans (by norm_num) psum1053o2_507
  · exact le_trans (by norm_num) psum1053o2_508
  · exact le_trans (by norm_num) psum1053o2_509
  · exact le_trans (by norm_num) psum1053o2_510
  · exact le_trans (by norm_num) psum1053o2_511
  · exact le_trans (by norm_num) psum1053o2_512
  · exact le_trans (by norm_num) psum1053o2_513
  · exact le_trans (by norm_num) psum1053o2_514
  · exact le_trans (by norm_num) psum1053o2_515
  · exact le_trans (by norm_num) psum1053o2_516
  · exact le_trans (by norm_num) psum1053o2_517
  · exact le_trans (by norm_num) psum1053o2_518
  · exact le_trans (by norm_num) psum1053o2_519
  · exact le_trans (by norm_num) psum1053o2_520
  · exact le_trans (by norm_num) psum1053o2_521
  · exact le_trans (by norm_num) psum1053o2_522
  · exact le_trans (by norm_num) psum1053o2_523
  · exact le_trans (by norm_num) psum1053o2_524
  · exact le_trans (by norm_num) psum1053o2_525
  · exact le_trans (by norm_num) psum1053o2_526
  · exact le_trans (by norm_num) psum1053o2_527
  · exact le_trans (by norm_num) psum1053o2_528
  · exact le_trans (by norm_num) psum1053o2_529
  · exact le_trans (by norm_num) psum1053o2_530
  · exact le_trans (by norm_num) psum1053o2_531
  · exact le_trans (by norm_num) psum1053o2_532
  · exact le_trans (by norm_num) psum1053o2_533
  · exact le_trans (by norm_num) psum1053o2_534
  · exact le_trans (by norm_num) psum1053o2_535
  · exact le_trans (by norm_num) psum1053o2_536
  · exact le_trans (by norm_num) psum1053o2_537
  · exact le_trans (by norm_num) psum1053o2_538
  · exact le_trans (by norm_num) psum1053o2_539
  · exact le_trans (by norm_num) psum1053o2_540
  · exact le_trans (by norm_num) psum1053o2_541
  · exact le_trans (by norm_num) psum1053o2_542
  · exact le_trans (by norm_num) psum1053o2_543
  · exact le_trans (by norm_num) psum1053o2_544
  · exact le_trans (by norm_num) psum1053o2_545
  · exact le_trans (by norm_num) psum1053o2_546
  · exact le_trans (by norm_num) psum1053o2_547
  · exact le_trans (by norm_num) psum1053o2_548
  · exact le_trans (by norm_num) psum1053o2_549
  · exact le_trans (by norm_num) psum1053o2_550
  · exact le_trans (by norm_num) psum1053o2_551
  · exact le_trans (by norm_num) psum1053o2_552
  · exact le_trans (by norm_num) psum1053o2_553
  · exact le_trans (by norm_num) psum1053o2_554
  · exact le_trans (by norm_num) psum1053o2_555
  · exact le_trans (by norm_num) psum1053o2_556
  · exact le_trans (by norm_num) psum1053o2_557
  · exact le_trans (by norm_num) psum1053o2_558
  · exact le_trans (by norm_num) psum1053o2_559
  · exact le_trans (by norm_num) psum1053o2_560
  · exact le_trans (by norm_num) psum1053o2_561
  · exact le_trans (by norm_num) psum1053o2_562
  · exact le_trans (by norm_num) psum1053o2_563
  · exact le_trans (by norm_num) psum1053o2_564
  · exact le_trans (by norm_num) psum1053o2_565
  · exact le_trans (by norm_num) psum1053o2_566
  · exact le_trans (by norm_num) psum1053o2_567
  · exact le_trans (by norm_num) psum1053o2_568
  · exact le_trans (by norm_num) psum1053o2_569
  · exact le_trans (by norm_num) psum1053o2_570
  · exact le_trans (by norm_num) psum1053o2_571
  · exact le_trans (by norm_num) psum1053o2_572
  · exact le_trans (by norm_num) psum1053o2_573
  · exact le_trans (by norm_num) psum1053o2_574
  · exact le_trans (by norm_num) psum1053o2_575
  · exact le_trans (by norm_num) psum1053o2_576
  · exact le_trans (by norm_num) psum1053o2_577
  · exact le_trans (by norm_num) psum1053o2_578
  · exact le_trans (by norm_num) psum1053o2_579
  · exact le_trans (by norm_num) psum1053o2_580
  · exact le_trans (by norm_num) psum1053o2_581
  · exact le_trans (by norm_num) psum1053o2_582
  · exact le_trans (by norm_num) psum1053o2_583
  · exact le_trans (by norm_num) psum1053o2_584
  · exact le_trans (by norm_num) psum1053o2_585
  · exact le_trans (by norm_num) psum1053o2_586
  · exact le_trans (by norm_num) psum1053o2_587
  · exact le_trans (by norm_num) psum1053o2_588
  · exact le_trans (by norm_num) psum1053o2_589
  · exact le_trans (by norm_num) psum1053o2_590
  · exact le_trans (by norm_num) psum1053o2_591
  · exact le_trans (by norm_num) psum1053o2_592
  · exact le_trans (by norm_num) psum1053o2_593
  · exact le_trans (by norm_num) psum1053o2_594
  · exact le_trans (by norm_num) psum1053o2_595
  · exact le_trans (by norm_num) psum1053o2_596
  · exact le_trans (by norm_num) psum1053o2_597
  · exact le_trans (by norm_num) psum1053o2_598
  · exact le_trans (by norm_num) psum1053o2_599
  · exact le_trans (by norm_num) psum1053o2_600
  · exact le_trans (by norm_num) psum1053o2_601
  · exact le_trans (by norm_num) psum1053o2_602
  · exact le_trans (by norm_num) psum1053o2_603
  · exact le_trans (by norm_num) psum1053o2_604
  · exact le_trans (by norm_num) psum1053o2_605
  · exact le_trans (by norm_num) psum1053o2_606
  · exact le_trans (by norm_num) psum1053o2_607
  · exact le_trans (by norm_num) psum1053o2_608
  · exact le_trans (by norm_num) psum1053o2_609
  · exact le_trans (by norm_num) psum1053o2_610
  · exact le_trans (by norm_num) psum1053o2_611
  · exact le_trans (by norm_num) psum1053o2_612
  · exact le_trans (by norm_num) psum1053o2_613
  · exact le_trans (by norm_num) psum1053o2_614
  · exact le_trans (by norm_num) psum1053o2_615
  · exact le_trans (by norm_num) psum1053o2_616
  · exact le_trans (by norm_num) psum1053o2_617
  · exact le_trans (by norm_num) psum1053o2_618
  · exact le_trans (by norm_num) psum1053o2_619
  · exact le_trans (by norm_num) psum1053o2_620
  · exact le_trans (by norm_num) psum1053o2_621
  · exact le_trans (by norm_num) psum1053o2_622
  · exact le_trans (by norm_num) psum1053o2_623
  · exact le_trans (by norm_num) psum1053o2_624
  · exact le_trans (by norm_num) psum1053o2_625
  · exact le_trans (by norm_num) psum1053o2_626
  · exact le_trans (by norm_num) psum1053o2_627
  · exact le_trans (by norm_num) psum1053o2_628
  · exact le_trans (by norm_num) psum1053o2_629
  · exact le_trans (by norm_num) psum1053o2_630
  · exact le_trans (by norm_num) psum1053o2_631
  · exact le_trans (by norm_num) psum1053o2_632
  · exact le_trans (by norm_num) psum1053o2_633
  · exact le_trans (by norm_num) psum1053o2_634
  · exact le_trans (by norm_num) psum1053o2_635
  · exact le_trans (by norm_num) psum1053o2_636
  · exact le_trans (by norm_num) psum1053o2_637
  · exact le_trans (by norm_num) psum1053o2_638
  · exact le_trans (by norm_num) psum1053o2_639
  · exact le_trans (by norm_num) psum1053o2_640
  · exact le_trans (by norm_num) psum1053o2_641
  · exact le_trans (by norm_num) psum1053o2_642
  · exact le_trans (by norm_num) psum1053o2_643
  · exact le_trans (by norm_num) psum1053o2_644
  · exact le_trans (by norm_num) psum1053o2_645
  · exact le_trans (by norm_num) psum1053o2_646
  · exact le_trans (by norm_num) psum1053o2_647
  · exact le_trans (by norm_num) psum1053o2_648
  · exact le_trans (by norm_num) psum1053o2_649
  · exact le_trans (by norm_num) psum1053o2_650
  · exact le_trans (by norm_num) psum1053o2_651
  · exact le_trans (by norm_num) psum1053o2_652
  · exact le_trans (by norm_num) psum1053o2_653
  · exact le_trans (by norm_num) psum1053o2_654
  · exact le_trans (by norm_num) psum1053o2_655
  · exact le_trans (by norm_num) psum1053o2_656
  · exact le_trans (by norm_num) psum1053o2_657
  · exact le_trans (by norm_num) psum1053o2_658
  · exact le_trans (by norm_num) psum1053o2_659
  · exact le_trans (by norm_num) psum1053o2_660
  · exact le_trans (by norm_num) psum1053o2_661
  · exact le_trans (by norm_num) psum1053o2_662
  · exact le_trans (by norm_num) psum1053o2_663
  · exact le_trans (by norm_num) psum1053o2_664
  · exact le_trans (by norm_num) psum1053o2_665
  · exact le_trans (by norm_num) psum1053o2_666
  · exact le_trans (by norm_num) psum1053o2_667
  · exact le_trans (by norm_num) psum1053o2_668
  · exact le_trans (by norm_num) psum1053o2_669
  · exact le_trans (by norm_num) psum1053o2_670
  · exact le_trans (by norm_num) psum1053o2_671
  · exact le_trans (by norm_num) psum1053o2_672
  · exact le_trans (by norm_num) psum1053o2_673
  · exact le_trans (by norm_num) psum1053o2_674
  · exact le_trans (by norm_num) psum1053o2_675
  · exact le_trans (by norm_num) psum1053o2_676
  · exact le_trans (by norm_num) psum1053o2_677
  · exact le_trans (by norm_num) psum1053o2_678
  · exact le_trans (by norm_num) psum1053o2_679
  · exact le_trans (by norm_num) psum1053o2_680
  · exact le_trans (by norm_num) psum1053o2_681
  · exact le_trans (by norm_num) psum1053o2_682
  · exact le_trans (by norm_num) psum1053o2_683
  · exact le_trans (by norm_num) psum1053o2_684
  · exact le_trans (by norm_num) psum1053o2_685
  · exact le_trans (by norm_num) psum1053o2_686
  · exact le_trans (by norm_num) psum1053o2_687
  · exact le_trans (by norm_num) psum1053o2_688
  · exact le_trans (by norm_num) psum1053o2_689
  · exact le_trans (by norm_num) psum1053o2_690
  · exact le_trans (by norm_num) psum1053o2_691
  · exact le_trans (by norm_num) psum1053o2_692
  · exact le_trans (by norm_num) psum1053o2_693
  · exact le_trans (by norm_num) psum1053o2_694
  · exact le_trans (by norm_num) psum1053o2_695
  · exact le_trans (by norm_num) psum1053o2_696
  · exact le_trans (by norm_num) psum1053o2_697
  · exact le_trans (by norm_num) psum1053o2_698
  · exact le_trans (by norm_num) psum1053o2_699
  · exact le_trans (by norm_num) psum1053o2_700
  · exact le_trans (by norm_num) psum1053o2_701
  · exact le_trans (by norm_num) psum1053o2_702
  · exact le_trans (by norm_num) psum1053o2_703
  · exact le_trans (by norm_num) psum1053o2_704
  · exact le_trans (by norm_num) psum1053o2_705
  · exact le_trans (by norm_num) psum1053o2_706
  · exact le_trans (by norm_num) psum1053o2_707
  · exact le_trans (by norm_num) psum1053o2_708
  · exact le_trans (by norm_num) psum1053o2_709
  · exact le_trans (by norm_num) psum1053o2_710
  · exact le_trans (by norm_num) psum1053o2_711
  · exact le_trans (by norm_num) psum1053o2_712
  · exact le_trans (by norm_num) psum1053o2_713
  · exact le_trans (by norm_num) psum1053o2_714
  · exact le_trans (by norm_num) psum1053o2_715
  · exact le_trans (by norm_num) psum1053o2_716
  · exact le_trans (by norm_num) psum1053o2_717
  · exact le_trans (by norm_num) psum1053o2_718
  · exact le_trans (by norm_num) psum1053o2_719
  · exact le_trans (by norm_num) psum1053o2_720
  · exact le_trans (by norm_num) psum1053o2_721
  · exact le_trans (by norm_num) psum1053o2_722
  · exact le_trans (by norm_num) psum1053o2_723
  · exact le_trans (by norm_num) psum1053o2_724
  · exact le_trans (by norm_num) psum1053o2_725
  · exact le_trans (by norm_num) psum1053o2_726
  · exact le_trans (by norm_num) psum1053o2_727
  · exact le_trans (by norm_num) psum1053o2_728
  · exact le_trans (by norm_num) psum1053o2_729
  · exact le_trans (by norm_num) psum1053o2_730
  · exact le_trans (by norm_num) psum1053o2_731
  · exact le_trans (by norm_num) psum1053o2_732
  · exact le_trans (by norm_num) psum1053o2_733
  · exact le_trans (by norm_num) psum1053o2_734
  · exact le_trans (by norm_num) psum1053o2_735
  · exact le_trans (by norm_num) psum1053o2_736
  · exact le_trans (by norm_num) psum1053o2_737
  · exact le_trans (by norm_num) psum1053o2_738
  · exact le_trans (by norm_num) psum1053o2_739
  · exact le_trans (by norm_num) psum1053o2_740
  · exact le_trans (by norm_num) psum1053o2_741
  · exact le_trans (by norm_num) psum1053o2_742
  · exact le_trans (by norm_num) psum1053o2_743
  · exact le_trans (by norm_num) psum1053o2_744
  · exact le_trans (by norm_num) psum1053o2_745
  · exact le_trans (by norm_num) psum1053o2_746
  · exact le_trans (by norm_num) psum1053o2_747
  · exact le_trans (by norm_num) psum1053o2_748
  · exact le_trans (by norm_num) psum1053o2_749
  · exact le_trans (by norm_num) psum1053o2_750
  · exact le_trans (by norm_num) psum1053o2_751
  · exact le_trans (by norm_num) psum1053o2_752
  · exact le_trans (by norm_num) psum1053o2_753
  · exact le_trans (by norm_num) psum1053o2_754
  · exact le_trans (by norm_num) psum1053o2_755
  · exact le_trans (by norm_num) psum1053o2_756
  · exact le_trans (by norm_num) psum1053o2_757
  · exact le_trans (by norm_num) psum1053o2_758
  · exact le_trans (by norm_num) psum1053o2_759
  · exact le_trans (by norm_num) psum1053o2_760
  · exact le_trans (by norm_num) psum1053o2_761
  · exact le_trans (by norm_num) psum1053o2_762
  · exact le_trans (by norm_num) psum1053o2_763
  · exact le_trans (by norm_num) psum1053o2_764
  · exact le_trans (by norm_num) psum1053o2_765
  · exact le_trans (by norm_num) psum1053o2_766
  · exact le_trans (by norm_num) psum1053o2_767
  · exact le_trans (by norm_num) psum1053o2_768
  · exact le_trans (by norm_num) psum1053o2_769
  · exact le_trans (by norm_num) psum1053o2_770
  · exact le_trans (by norm_num) psum1053o2_771
  · exact le_trans (by norm_num) psum1053o2_772
  · exact le_trans (by norm_num) psum1053o2_773
  · exact le_trans (by norm_num) psum1053o2_774
  · exact le_trans (by norm_num) psum1053o2_775
  · exact le_trans (by norm_num) psum1053o2_776
  · exact le_trans (by norm_num) psum1053o2_777
  · exact le_trans (by norm_num) psum1053o2_778
  · exact le_trans (by norm_num) psum1053o2_779
  · exact le_trans (by norm_num) psum1053o2_780
  · exact le_trans (by norm_num) psum1053o2_781
  · exact le_trans (by norm_num) psum1053o2_782
  · exact le_trans (by norm_num) psum1053o2_783
  · exact le_trans (by norm_num) psum1053o2_784
  · exact le_trans (by norm_num) psum1053o2_785
  · exact le_trans (by norm_num) psum1053o2_786
  · exact le_trans (by norm_num) psum1053o2_787
  · exact le_trans (by norm_num) psum1053o2_788
  · exact le_trans (by norm_num) psum1053o2_789
  · exact le_trans (by norm_num) psum1053o2_790
  · exact le_trans (by norm_num) psum1053o2_791
  · exact le_trans (by norm_num) psum1053o2_792
  · exact le_trans (by norm_num) psum1053o2_793
  · exact le_trans (by norm_num) psum1053o2_794
  · exact le_trans (by norm_num) psum1053o2_795
  · exact le_trans (by norm_num) psum1053o2_796
  · exact le_trans (by norm_num) psum1053o2_797
  · exact le_trans (by norm_num) psum1053o2_798
  · exact le_trans (by norm_num) psum1053o2_799
  · exact le_trans (by norm_num) psum1053o2_800
  · exact le_trans (by norm_num) psum1053o2_801
  · exact le_trans (by norm_num) psum1053o2_802
  · exact le_trans (by norm_num) psum1053o2_803
  · exact le_trans (by norm_num) psum1053o2_804
  · exact le_trans (by norm_num) psum1053o2_805
  · exact le_trans (by norm_num) psum1053o2_806
  · exact le_trans (by norm_num) psum1053o2_807
  · exact le_trans (by norm_num) psum1053o2_808
  · exact le_trans (by norm_num) psum1053o2_809
  · exact le_trans (by norm_num) psum1053o2_810
  · exact le_trans (by norm_num) psum1053o2_811
  · exact le_trans (by norm_num) psum1053o2_812
  · exact le_trans (by norm_num) psum1053o2_813
  · exact le_trans (by norm_num) psum1053o2_814
  · exact le_trans (by norm_num) psum1053o2_815
  · exact le_trans (by norm_num) psum1053o2_816
  · exact le_trans (by norm_num) psum1053o2_817
  · exact le_trans (by norm_num) psum1053o2_818
  · exact le_trans (by norm_num) psum1053o2_819
  · exact le_trans (by norm_num) psum1053o2_820
  · exact le_trans (by norm_num) psum1053o2_821
  · exact le_trans (by norm_num) psum1053o2_822
  · exact le_trans (by norm_num) psum1053o2_823
  · exact le_trans (by norm_num) psum1053o2_824
  · exact le_trans (by norm_num) psum1053o2_825
  · exact le_trans (by norm_num) psum1053o2_826
  · exact le_trans (by norm_num) psum1053o2_827
  · exact le_trans (by norm_num) psum1053o2_828
  · exact le_trans (by norm_num) psum1053o2_829
  · exact le_trans (by norm_num) psum1053o2_830
  · exact le_trans (by norm_num) psum1053o2_831
  · exact le_trans (by norm_num) psum1053o2_832
  · exact le_trans (by norm_num) psum1053o2_833
  · exact le_trans (by norm_num) psum1053o2_834
  · exact le_trans (by norm_num) psum1053o2_835
  · exact le_trans (by norm_num) psum1053o2_836
  · exact le_trans (by norm_num) psum1053o2_837
  · exact le_trans (by norm_num) psum1053o2_838
  · exact le_trans (by norm_num) psum1053o2_839
  · exact le_trans (by norm_num) psum1053o2_840
  · exact le_trans (by norm_num) psum1053o2_841
  · exact le_trans (by norm_num) psum1053o2_842
  · exact le_trans (by norm_num) psum1053o2_843
  · exact le_trans (by norm_num) psum1053o2_844
  · exact le_trans (by norm_num) psum1053o2_845
  · exact le_trans (by norm_num) psum1053o2_846
  · exact le_trans (by norm_num) psum1053o2_847
  · exact le_trans (by norm_num) psum1053o2_848
  · exact le_trans (by norm_num) psum1053o2_849
  · exact le_trans (by norm_num) psum1053o2_850
  · exact le_trans (by norm_num) psum1053o2_851
  · exact le_trans (by norm_num) psum1053o2_852
  · exact le_trans (by norm_num) psum1053o2_853
  · exact le_trans (by norm_num) psum1053o2_854
  · exact le_trans (by norm_num) psum1053o2_855
  · exact le_trans (by norm_num) psum1053o2_856
  · exact le_trans (by norm_num) psum1053o2_857
  · exact le_trans (by norm_num) psum1053o2_858
  · exact le_trans (by norm_num) psum1053o2_859
  · exact le_trans (by norm_num) psum1053o2_860
  · exact le_trans (by norm_num) psum1053o2_861
  · exact le_trans (by norm_num) psum1053o2_862
  · exact le_trans (by norm_num) psum1053o2_863
  · exact le_trans (by norm_num) psum1053o2_864
  · exact le_trans (by norm_num) psum1053o2_865
  · exact le_trans (by norm_num) psum1053o2_866
  · exact le_trans (by norm_num) psum1053o2_867
  · exact le_trans (by norm_num) psum1053o2_868
  · exact le_trans (by norm_num) psum1053o2_869
  · exact le_trans (by norm_num) psum1053o2_870
  · exact le_trans (by norm_num) psum1053o2_871
  · exact le_trans (by norm_num) psum1053o2_872
  · exact le_trans (by norm_num) psum1053o2_873
  · exact le_trans (by norm_num) psum1053o2_874
  · exact le_trans (by norm_num) psum1053o2_875
  · exact le_trans (by norm_num) psum1053o2_876
  · exact le_trans (by norm_num) psum1053o2_877
  · exact le_trans (by norm_num) psum1053o2_878
  · exact le_trans (by norm_num) psum1053o2_879
  · exact le_trans (by norm_num) psum1053o2_880
  · exact le_trans (by norm_num) psum1053o2_881
  · exact le_trans (by norm_num) psum1053o2_882
  · exact le_trans (by norm_num) psum1053o2_883
  · exact le_trans (by norm_num) psum1053o2_884
  · exact le_trans (by norm_num) psum1053o2_885
  · exact le_trans (by norm_num) psum1053o2_886
  · exact le_trans (by norm_num) psum1053o2_887
  · exact le_trans (by norm_num) psum1053o2_888
  · exact le_trans (by norm_num) psum1053o2_889
  · exact le_trans (by norm_num) psum1053o2_890
  · exact le_trans (by norm_num) psum1053o2_891
  · exact le_trans (by norm_num) psum1053o2_892
  · exact le_trans (by norm_num) psum1053o2_893
  · exact le_trans (by norm_num) psum1053o2_894
  · exact le_trans (by norm_num) psum1053o2_895
  · exact le_trans (by norm_num) psum1053o2_896
  · exact le_trans (by norm_num) psum1053o2_897
  · exact le_trans (by norm_num) psum1053o2_898
  · exact le_trans (by norm_num) psum1053o2_899
  · exact le_trans (by norm_num) psum1053o2_900
  · exact le_trans (by norm_num) psum1053o2_901
  · exact le_trans (by norm_num) psum1053o2_902
  · exact le_trans (by norm_num) psum1053o2_903
  · exact le_trans (by norm_num) psum1053o2_904
  · exact le_trans (by norm_num) psum1053o2_905
  · exact le_trans (by norm_num) psum1053o2_906
  · exact le_trans (by norm_num) psum1053o2_907
  · exact le_trans (by norm_num) psum1053o2_908
  · exact le_trans (by norm_num) psum1053o2_909
  · exact le_trans (by norm_num) psum1053o2_910
  · exact le_trans (by norm_num) psum1053o2_911
  · exact le_trans (by norm_num) psum1053o2_912
  · exact le_trans (by norm_num) psum1053o2_913
  · exact le_trans (by norm_num) psum1053o2_914
  · exact le_trans (by norm_num) psum1053o2_915
  · exact le_trans (by norm_num) psum1053o2_916
  · exact le_trans (by norm_num) psum1053o2_917
  · exact le_trans (by norm_num) psum1053o2_918
  · exact le_trans (by norm_num) psum1053o2_919
  · exact le_trans (by norm_num) psum1053o2_920
  · exact le_trans (by norm_num) psum1053o2_921
  · exact le_trans (by norm_num) psum1053o2_922
  · exact le_trans (by norm_num) psum1053o2_923
  · exact le_trans (by norm_num) psum1053o2_924
  · exact le_trans (by norm_num) psum1053o2_925
  · exact le_trans (by norm_num) psum1053o2_926
  · exact le_trans (by norm_num) psum1053o2_927
  · exact le_trans (by norm_num) psum1053o2_928
  · exact le_trans (by norm_num) psum1053o2_929
  · exact le_trans (by norm_num) psum1053o2_930
  · exact le_trans (by norm_num) psum1053o2_931
  · exact le_trans (by norm_num) psum1053o2_932
  · exact le_trans (by norm_num) psum1053o2_933
  · exact le_trans (by norm_num) psum1053o2_934
  · exact le_trans (by norm_num) psum1053o2_935
  · exact le_trans (by norm_num) psum1053o2_936
  · exact le_trans (by norm_num) psum1053o2_937
  · exact le_trans (by norm_num) psum1053o2_938
  · exact le_trans (by norm_num) psum1053o2_939
  · exact le_trans (by norm_num) psum1053o2_940
  · exact le_trans (by norm_num) psum1053o2_941
  · exact le_trans (by norm_num) psum1053o2_942
  · exact le_trans (by norm_num) psum1053o2_943
  · exact le_trans (by norm_num) psum1053o2_944
  · exact le_trans (by norm_num) psum1053o2_945
  · exact le_trans (by norm_num) psum1053o2_946
  · exact le_trans (by norm_num) psum1053o2_947
  · exact le_trans (by norm_num) psum1053o2_948
  · exact le_trans (by norm_num) psum1053o2_949
  · exact le_trans (by norm_num) psum1053o2_950
  · exact le_trans (by norm_num) psum1053o2_951
  · exact le_trans (by norm_num) psum1053o2_952
  · exact le_trans (by norm_num) psum1053o2_953
  · exact le_trans (by norm_num) psum1053o2_954
  · exact le_trans (by norm_num) psum1053o2_955
  · exact le_trans (by norm_num) psum1053o2_956
  · exact le_trans (by norm_num) psum1053o2_957
  · exact le_trans (by norm_num) psum1053o2_958
  · exact le_trans (by norm_num) psum1053o2_959
  · exact le_trans (by norm_num) psum1053o2_960
  · exact le_trans (by norm_num) psum1053o2_961
  · exact le_trans (by norm_num) psum1053o2_962
  · exact le_trans (by norm_num) psum1053o2_963
  · exact le_trans (by norm_num) psum1053o2_964
  · exact le_trans (by norm_num) psum1053o2_965
  · exact le_trans (by norm_num) psum1053o2_966
  · exact le_trans (by norm_num) psum1053o2_967
  · exact le_trans (by norm_num) psum1053o2_968
  · exact le_trans (by norm_num) psum1053o2_969
  · exact le_trans (by norm_num) psum1053o2_970
  · exact le_trans (by norm_num) psum1053o2_971
  · exact le_trans (by norm_num) psum1053o2_972
  · exact le_trans (by norm_num) psum1053o2_973
  · exact le_trans (by norm_num) psum1053o2_974
  · exact le_trans (by norm_num) psum1053o2_975
  · exact le_trans (by norm_num) psum1053o2_976
  · exact le_trans (by norm_num) psum1053o2_977
  · exact le_trans (by norm_num) psum1053o2_978
  · exact le_trans (by norm_num) psum1053o2_979
  · exact le_trans (by norm_num) psum1053o2_980
  · exact le_trans (by norm_num) psum1053o2_981
  · exact le_trans (by norm_num) psum1053o2_982
  · exact le_trans (by norm_num) psum1053o2_983
  · exact le_trans (by norm_num) psum1053o2_984
  · exact le_trans (by norm_num) psum1053o2_985
  · exact le_trans (by norm_num) psum1053o2_986
  · exact le_trans (by norm_num) psum1053o2_987
  · exact le_trans (by norm_num) psum1053o2_988
  · exact le_trans (by norm_num) psum1053o2_989
  · exact le_trans (by norm_num) psum1053o2_990
  · exact le_trans (by norm_num) psum1053o2_991
  · exact le_trans (by norm_num) psum1053o2_992
  · exact le_trans (by norm_num) psum1053o2_993
  · exact le_trans (by norm_num) psum1053o2_994
  · exact le_trans (by norm_num) psum1053o2_995
  · exact le_trans (by norm_num) psum1053o2_996
  · exact le_trans (by norm_num) psum1053o2_997
  · exact le_trans (by norm_num) psum1053o2_998
  · exact le_trans (by norm_num) psum1053o2_999
  · exact le_trans (by norm_num) psum1053o2_1000

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum1053o2_floor
#print axioms CriticalLinePhasor.DVP.psum1053o2_1000
end AxiomAudit
