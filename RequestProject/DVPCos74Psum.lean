import RequestProject.DVPCos74Table

/-!
# The cosine partial-sum floor, `t = 74`
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 74` segment certificate. -/
def cos74c (n : ℕ) : ℝ := Real.cos (((74:ℕ):ℝ) * Real.log n)

theorem psum74_11 : ((27833/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos74c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/25000 : ℚ) : ℝ) ≤ cos74c 11 - ((27853/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_11).1
  push_cast at h ⊢
  linarith

theorem psum74_12 : ((-44129/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos74c k)
      = (∑ k ∈ Finset.Icc 11 11, cos74c k) + cos74c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_11
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 12 - ((-19951/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_13 : ((213011/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos74c k)
      = (∑ k ∈ Finset.Icc 11 12, cos74c k) + cos74c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_12
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 13 - ((12859/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_14 : ((1084983/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos74c k)
      = (∑ k ∈ Finset.Icc 11 13, cos74c k) + cos74c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_13
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 14 - ((218003/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_15 : ((1871109/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos74c k)
      = (∑ k ∈ Finset.Icc 11 14, cos74c k) + cos74c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_14
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 15 - ((393083/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_16 : ((326039/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos74c k)
      = (∑ k ∈ Finset.Icc 11 15, cos74c k) + cos74c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_15
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 16 - ((-566913/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_17 : ((157111/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos74c k)
      = (∑ k ∈ Finset.Icc 11 16, cos74c k) + cos74c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_16
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 17 - ((-84459/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_18 : ((1594997/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos74c k)
      = (∑ k ∈ Finset.Icc 11 17, cos74c k) + cos74c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_17
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 18 - ((966593/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_19 : ((1158007/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos74c k)
      = (∑ k ∈ Finset.Icc 11 18, cos74c k) + cos74c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_18
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 19 - ((-8739/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_20 : ((95743/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos74c k)
      = (∑ k ∈ Finset.Icc 11 19, cos74c k) + cos74c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_19
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 20 - ((-200537/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_21 : ((98687/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos74c k)
      = (∑ k ∈ Finset.Icc 11 20, cos74c k) + cos74c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_20
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 21 - ((310801/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_22 : ((753121/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos74c k)
      = (∑ k ∈ Finset.Icc 11 21, cos74c k) + cos74c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_21
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 22 - ((-825831/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_23 : ((1652969/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos74c k)
      = (∑ k ∈ Finset.Icc 11 22, cos74c k) + cos74c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_22
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 23 - ((56243/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_24 : ((749659/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos74c k)
      = (∑ k ∈ Finset.Icc 11 23, cos74c k) + cos74c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_23
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 24 - ((-90327/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_25 : ((1594619/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos74c k)
      = (∑ k ∈ Finset.Icc 11 24, cos74c k) + cos74c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_24
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 25 - ((169/200 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_26 : ((900381/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos74c k)
      = (∑ k ∈ Finset.Icc 11 25, cos74c k) + cos74c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_25
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 26 - ((-347099/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_27 : ((1306729/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos74c k)
      = (∑ k ∈ Finset.Icc 11 26, cos74c k) + cos74c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_26
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 27 - ((101597/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_28 : ((669287/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos74c k)
      = (∑ k ∈ Finset.Icc 11 27, cos74c k) + cos74c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_27
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 28 - ((6377/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_29 : ((793253/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos74c k)
      = (∑ k ∈ Finset.Icc 11 28, cos74c k) + cos74c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_28
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 29 - ((-545281/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_30 : ((1728689/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos74c k)
      = (∑ k ∈ Finset.Icc 11 29, cos74c k) + cos74c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_29
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 30 - ((233869/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_31 : ((790639/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos74c k)
      = (∑ k ∈ Finset.Icc 11 30, cos74c k) + cos74c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_30
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 31 - ((-93801/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_32 : ((601303/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos74c k)
      = (∑ k ∈ Finset.Icc 11 31, cos74c k) + cos74c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_31
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 32 - ((412007/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_33 : ((407089/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos74c k)
      = (∑ k ∈ Finset.Icc 11 32, cos74c k) + cos74c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_32
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 33 - ((42579/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_34 : ((12959/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos74c k)
      = (∑ k ∈ Finset.Icc 11 33, cos74c k) + cos74c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_33
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 34 - ((-490183/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_35 : ((1346031/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos74c k)
      = (∑ k ∈ Finset.Icc 11 34, cos74c k) + cos74c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_34
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 35 - ((698121/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_36 : ((1626359/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos74c k)
      = (∑ k ∈ Finset.Icc 11 35, cos74c k) + cos74c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_35
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 36 - ((17523/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_37 : ((641169/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos74c k)
      = (∑ k ∈ Finset.Icc 11 36, cos74c k) + cos74c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_36
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 37 - ((-19703/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_38 : ((237027/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos74c k)
      = (∑ k ∈ Finset.Icc 11 37, cos74c k) + cos74c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_37
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 38 - ((272003/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_39 : ((223207/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos74c k)
      = (∑ k ∈ Finset.Icc 11 38, cos74c k) + cos74c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_38
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 39 - ((600561/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_40 : ((210839/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos74c k)
      = (∑ k ∈ Finset.Icc 11 39, cos74c k) + cos74c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_39
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 40 - ((-47113/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_41 : ((379197/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos74c k)
      = (∑ k ∈ Finset.Icc 11 40, cos74c k) + cos74c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_40
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 41 - ((-42461/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_42 : ((7001/4000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos74c k)
      = (∑ k ∈ Finset.Icc 11 41, cos74c k) + cos74c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_41
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 42 - ((123987/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_43 : ((45523/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos74c k)
      = (∑ k ∈ Finset.Icc 11 42, cos74c k) + cos74c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_42
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 43 - ((-146737/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_44 : ((547017/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos74c k)
      = (∑ k ∈ Finset.Icc 11 43, cos74c k) + cos74c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_43
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 44 - ((-909679/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_45 : ((41771/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos74c k)
      = (∑ k ∈ Finset.Icc 11 44, cos74c k) + cos74c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_44
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 45 - ((248649/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_46 : ((376563/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos74c k)
      = (∑ k ∈ Finset.Icc 11 45, cos74c k) + cos74c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_45
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 46 - ((41929/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_47 : ((1320787/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos74c k)
      = (∑ k ∈ Finset.Icc 11 46, cos74c k) + cos74c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_46
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 47 - ((-140497/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_48 : ((121613/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos74c k)
      = (∑ k ∈ Finset.Icc 11 47, cos74c k) + cos74c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_47
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 48 - ((-166859/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_49 : ((249917/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos74c k)
      = (∑ k ∈ Finset.Icc 11 48, cos74c k) + cos74c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_48
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 49 - ((64157/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_50 : ((378853/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos74c k)
      = (∑ k ∈ Finset.Icc 11 49, cos74c k) + cos74c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_49
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 50 - ((894637/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_51 : ((1544033/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos74c k)
      = (∑ k ∈ Finset.Icc 11 50, cos74c k) + cos74c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_50
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 51 - ((-21887/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_52 : ((284479/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos74c k)
      = (∑ k ∈ Finset.Icc 11 51, cos74c k) + cos74c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_51
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 52 - ((-195007/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_53 : ((126313/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos74c k)
      = (∑ k ∈ Finset.Icc 11 52, cos74c k) + cos74c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_52
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 53 - ((62647/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_54 : ((202967/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos74c k)
      = (∑ k ∈ Finset.Icc 11 53, cos74c k) + cos74c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_53
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 54 - ((992211/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_55 : ((488789/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos74c k)
      = (∑ k ∈ Finset.Icc 11 54, cos74c k) + cos74c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_54
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 55 - ((16573/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_56 : ((558037/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos74c k)
      = (∑ k ∈ Finset.Icc 11 55, cos74c k) + cos74c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_55
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 56 - ((-419521/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_57 : ((186931/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos74c k)
      = (∑ k ∈ Finset.Icc 11 56, cos74c k) + cos74c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_56
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 57 - ((-185543/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_58 : ((202351/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos74c k)
      = (∑ k ∈ Finset.Icc 11 57, cos74c k) + cos74c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_57
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 58 - ((217791/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_59 : ((224861/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos74c k)
      = (∑ k ∈ Finset.Icc 11 58, cos74c k) + cos74c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_58
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 59 - ((247381/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_60 : ((396007/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos74c k)
      = (∑ k ∈ Finset.Icc 11 59, cos74c k) + cos74c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_59
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 60 - ((181187/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_61 : ((558549/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos74c k)
      = (∑ k ∈ Finset.Icc 11 60, cos74c k) + cos74c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_60
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 61 - ((-862897/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_62 : ((83847/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos74c k)
      = (∑ k ∈ Finset.Icc 11 61, cos74c k) + cos74c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_61
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 62 - ((-78167/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_63 : ((618123/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos74c k)
      = (∑ k ∈ Finset.Icc 11 62, cos74c k) + cos74c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_62
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 63 - ((11311/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_64 : ((1611043/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos74c k)
      = (∑ k ∈ Finset.Icc 11 63, cos74c k) + cos74c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_63
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 64 - ((3103/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_65 : ((2127041/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos74c k)
      = (∑ k ∈ Finset.Icc 11 64, cos74c k) + cos74c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_64
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 65 - ((258019/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_66 : ((1572657/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos74c k)
      = (∑ k ∈ Finset.Icc 11 65, cos74c k) + cos74c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_65
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 66 - ((-69293/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_67 : ((581001/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos74c k)
      = (∑ k ∈ Finset.Icc 11 66, cos74c k) + cos74c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_66
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 67 - ((-15494/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_68 : ((242859/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos74c k)
      = (∑ k ∈ Finset.Icc 11 67, cos74c k) + cos74c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_67
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 68 - ((-169051/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_69 : ((57107/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos74c k)
      = (∑ k ∈ Finset.Icc 11 68, cos74c k) + cos74c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_68
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 69 - ((670893/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_70 : ((1887479/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos74c k)
      = (∑ k ∈ Finset.Icc 11 69, cos74c k) + cos74c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_69
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 70 - ((973807/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_71 : ((2175069/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos74c k)
      = (∑ k ∈ Finset.Icc 11 70, cos74c k) + cos74c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_70
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 71 - ((28763/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_72 : ((1498359/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos74c k)
      = (∑ k ∈ Finset.Icc 11 71, cos74c k) + cos74c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_71
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 72 - ((-67667/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_73 : ((516913/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos74c k)
      = (∑ k ∈ Finset.Icc 11 72, cos74c k) + cos74c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_72
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 73 - ((-490703/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_74 : ((154477/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos74c k)
      = (∑ k ∈ Finset.Icc 11 73, cos74c k) + cos74c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_73
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 74 - ((-90599/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_75 : ((737477/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos74c k)
      = (∑ k ∈ Finset.Icc 11 74, cos74c k) + cos74c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_74
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 75 - ((1822/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_76 : ((1736931/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos74c k)
      = (∑ k ∈ Finset.Icc 11 75, cos74c k) + cos74c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_75
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 76 - ((499747/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_77 : ((569477/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos74c k)
      = (∑ k ∈ Finset.Icc 11 76, cos74c k) + cos74c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_76
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 77 - ((541017/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_78 : ((475993/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos74c k)
      = (∑ k ∈ Finset.Icc 11 77, cos74c k) + cos74c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_77
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 78 - ((-46737/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_79 : ((933771/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos74c k)
      = (∑ k ∈ Finset.Icc 11 78, cos74c k) + cos74c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_78
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 79 - ((-970161/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_80 : ((159899/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos74c k)
      = (∑ k ∈ Finset.Icc 11 79, cos74c k) + cos74c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_79
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 80 - ((-96729/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_81 : ((777/4000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos74c k)
      = (∑ k ∈ Finset.Icc 11 80, cos74c k) + cos74c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_80
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 81 - ((34391/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_82 : ((250793/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos74c k)
      = (∑ k ∈ Finset.Icc 11 81, cos74c k) + cos74c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_81
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 82 - ((404481/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_83 : ((491821/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos74c k)
      = (∑ k ∈ Finset.Icc 11 82, cos74c k) + cos74c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_82
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 83 - ((120519/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_84 : ((2371339/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos74c k)
      = (∑ k ∈ Finset.Icc 11 83, cos74c k) + cos74c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_83
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 84 - ((80819/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_85 : ((963783/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos74c k)
      = (∑ k ∈ Finset.Icc 11 84, cos74c k) + cos74c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_84
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 85 - ((-443733/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_86 : ((957517/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos74c k)
      = (∑ k ∈ Finset.Icc 11 85, cos74c k) + cos74c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_85
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 86 - ((-970009/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_87 : ((137813/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos74c k)
      = (∑ k ∈ Finset.Icc 11 86, cos74c k) + cos74c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_86
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 87 - ((-51229/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_88 : ((11463/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos74c k)
      = (∑ k ∈ Finset.Icc 11 87, cos74c k) + cos74c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_87
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 88 - ((-114847/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_89 : ((10673/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos74c k)
      = (∑ k ∈ Finset.Icc 11 88, cos74c k) + cos74c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_88
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 89 - ((330093/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_90 : ((168277/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos74c k)
      = (∑ k ∈ Finset.Icc 11 89, cos74c k) + cos74c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_89
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 90 - ((499869/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_91 : ((238317/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos74c k)
      = (∑ k ∈ Finset.Icc 11 90, cos74c k) + cos74c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_90
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 91 - ((17511/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_92 : ((2350399/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos74c k)
      = (∑ k ∈ Finset.Icc 11 91, cos74c k) + cos74c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_91
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 92 - ((-32731/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_93 : ((805289/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos74c k)
      = (∑ k ∈ Finset.Icc 11 92, cos74c k) + cos74c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_92
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 93 - ((-739781/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_94 : ((611963/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos74c k)
      = (∑ k ∈ Finset.Icc 11 93, cos74c k) + cos74c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_93
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 94 - ((-39943/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_95 : ((-727/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos74c k)
      = (∑ k ∈ Finset.Icc 11 94, cos74c k) + cos74c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_94
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 95 - ((-670083/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_96 : ((-2207/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos74c k)
      = (∑ k ∈ Finset.Icc 11 95, cos74c k) + cos74c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_95
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 96 - ((1267/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_97 : ((704797/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos74c k)
      = (∑ k ∈ Finset.Icc 11 96, cos74c k) + cos74c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_96
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 97 - ((722493/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_98 : ((1704747/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos74c k)
      = (∑ k ∈ Finset.Icc 11 97, cos74c k) + cos74c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_97
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 98 - ((99999/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_99 : ((2438531/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos74c k)
      = (∑ k ∈ Finset.Icc 11 98, cos74c k) + cos74c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_98
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 99 - ((11466/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum74_100 : ((503723/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos74c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos74c k)
      = (∑ k ∈ Finset.Icc 11 99, cos74c k) + cos74c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos74c
    simpa using h
  have hprev := psum74_99
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos74c 100 - ((20031/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos74_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

/-- **The Abel floor at `t = 74`.** -/
theorem psum74_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 100 →
    ((-727/12500 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos74c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum74_11
  · exact le_trans (by norm_num) psum74_12
  · exact le_trans (by norm_num) psum74_13
  · exact le_trans (by norm_num) psum74_14
  · exact le_trans (by norm_num) psum74_15
  · exact le_trans (by norm_num) psum74_16
  · exact le_trans (by norm_num) psum74_17
  · exact le_trans (by norm_num) psum74_18
  · exact le_trans (by norm_num) psum74_19
  · exact le_trans (by norm_num) psum74_20
  · exact le_trans (by norm_num) psum74_21
  · exact le_trans (by norm_num) psum74_22
  · exact le_trans (by norm_num) psum74_23
  · exact le_trans (by norm_num) psum74_24
  · exact le_trans (by norm_num) psum74_25
  · exact le_trans (by norm_num) psum74_26
  · exact le_trans (by norm_num) psum74_27
  · exact le_trans (by norm_num) psum74_28
  · exact le_trans (by norm_num) psum74_29
  · exact le_trans (by norm_num) psum74_30
  · exact le_trans (by norm_num) psum74_31
  · exact le_trans (by norm_num) psum74_32
  · exact le_trans (by norm_num) psum74_33
  · exact le_trans (by norm_num) psum74_34
  · exact le_trans (by norm_num) psum74_35
  · exact le_trans (by norm_num) psum74_36
  · exact le_trans (by norm_num) psum74_37
  · exact le_trans (by norm_num) psum74_38
  · exact le_trans (by norm_num) psum74_39
  · exact le_trans (by norm_num) psum74_40
  · exact le_trans (by norm_num) psum74_41
  · exact le_trans (by norm_num) psum74_42
  · exact le_trans (by norm_num) psum74_43
  · exact le_trans (by norm_num) psum74_44
  · exact le_trans (by norm_num) psum74_45
  · exact le_trans (by norm_num) psum74_46
  · exact le_trans (by norm_num) psum74_47
  · exact le_trans (by norm_num) psum74_48
  · exact le_trans (by norm_num) psum74_49
  · exact le_trans (by norm_num) psum74_50
  · exact le_trans (by norm_num) psum74_51
  · exact le_trans (by norm_num) psum74_52
  · exact le_trans (by norm_num) psum74_53
  · exact le_trans (by norm_num) psum74_54
  · exact le_trans (by norm_num) psum74_55
  · exact le_trans (by norm_num) psum74_56
  · exact le_trans (by norm_num) psum74_57
  · exact le_trans (by norm_num) psum74_58
  · exact le_trans (by norm_num) psum74_59
  · exact le_trans (by norm_num) psum74_60
  · exact le_trans (by norm_num) psum74_61
  · exact le_trans (by norm_num) psum74_62
  · exact le_trans (by norm_num) psum74_63
  · exact le_trans (by norm_num) psum74_64
  · exact le_trans (by norm_num) psum74_65
  · exact le_trans (by norm_num) psum74_66
  · exact le_trans (by norm_num) psum74_67
  · exact le_trans (by norm_num) psum74_68
  · exact le_trans (by norm_num) psum74_69
  · exact le_trans (by norm_num) psum74_70
  · exact le_trans (by norm_num) psum74_71
  · exact le_trans (by norm_num) psum74_72
  · exact le_trans (by norm_num) psum74_73
  · exact le_trans (by norm_num) psum74_74
  · exact le_trans (by norm_num) psum74_75
  · exact le_trans (by norm_num) psum74_76
  · exact le_trans (by norm_num) psum74_77
  · exact le_trans (by norm_num) psum74_78
  · exact le_trans (by norm_num) psum74_79
  · exact le_trans (by norm_num) psum74_80
  · exact le_trans (by norm_num) psum74_81
  · exact le_trans (by norm_num) psum74_82
  · exact le_trans (by norm_num) psum74_83
  · exact le_trans (by norm_num) psum74_84
  · exact le_trans (by norm_num) psum74_85
  · exact le_trans (by norm_num) psum74_86
  · exact le_trans (by norm_num) psum74_87
  · exact le_trans (by norm_num) psum74_88
  · exact le_trans (by norm_num) psum74_89
  · exact le_trans (by norm_num) psum74_90
  · exact le_trans (by norm_num) psum74_91
  · exact le_trans (by norm_num) psum74_92
  · exact le_trans (by norm_num) psum74_93
  · exact le_trans (by norm_num) psum74_94
  · exact le_trans (by norm_num) psum74_95
  · exact le_trans (by norm_num) psum74_96
  · exact le_trans (by norm_num) psum74_97
  · exact le_trans (by norm_num) psum74_98
  · exact le_trans (by norm_num) psum74_99
  · exact le_trans (by norm_num) psum74_100

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum74_floor
#print axioms CriticalLinePhasor.DVP.psum74_100
end AxiomAudit
