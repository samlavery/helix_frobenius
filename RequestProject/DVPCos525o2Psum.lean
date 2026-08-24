import RequestProject.DVPCos525o2Table

/-!
# The cosine partial-sum floor, `t = 525/2`
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 525/2` segment certificate. -/
def cos525o2c (n : ℕ) : ℝ := Real.cos (((525:ℕ):ℝ) * (Real.log n / 2))

theorem psum525o2_11 : ((427549/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos525o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 11 - ((427589/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum525o2_12 : ((823843/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos525o2c k) + cos525o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_11
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 12 - ((198167/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_13 : ((1365471/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos525o2c k) + cos525o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_12
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 13 - ((135417/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_14 : ((667031/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos525o2c k) + cos525o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_13
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 14 - ((-31369/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_15 : ((247999/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos525o2c k) + cos525o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_14
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 15 - ((64997/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_16 : ((1242949/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos525o2c k) + cos525o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_15
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 16 - ((250973/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_17 : ((1817617/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos525o2c k) + cos525o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_16
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 17 - ((-668241/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_18 : ((461383/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos525o2c k) + cos525o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_17
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 18 - ((5591/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_19 : ((1421007/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos525o2c k) + cos525o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_18
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 19 - ((498261/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_20 : ((3397707/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos525o2c k) + cos525o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_19
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 20 - ((555733/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_21 : ((3738861/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos525o2c k) + cos525o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_20
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 21 - ((170597/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_22 : ((35083/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos525o2c k) + cos525o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_21
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 22 - ((323277/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_23 : ((1346221/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos525o2c k) + cos525o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_22
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 23 - ((999549/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_24 : ((5530609/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos525o2c k) + cos525o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_23
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 24 - ((29153/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_25 : ((4539469/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos525o2c k) + cos525o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_24
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 25 - ((-9911/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_26 : ((5279821/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos525o2c k) + cos525o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_25
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 26 - ((92549/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_27 : ((2467689/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos525o2c k) + cos525o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_26
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 27 - ((-344403/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_28 : ((5163179/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos525o2c k) + cos525o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_27
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 28 - ((227841/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_29 : ((1183583/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos525o2c k) + cos525o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_28
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 29 - ((-428807/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_30 : ((2779251/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos525o2c k) + cos525o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_29
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 30 - ((82421/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_31 : ((4581579/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos525o2c k) + cos525o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_30
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 31 - ((-976883/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_32 : ((193723/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos525o2c k) + cos525o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_31
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 32 - ((8173/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_33 : ((357889/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos525o2c k) + cos525o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_32
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 33 - ((883189/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_34 : ((1318189/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos525o2c k) + cos525o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_33
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 34 - ((-113357/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_35 : ((4298111/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos525o2c k) + cos525o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_34
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 35 - ((-194921/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_36 : ((2033453/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos525o2c k) + cos525o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_35
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 36 - ((-46233/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_37 : ((469237/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos525o2c k) + cos525o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_36
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 37 - ((19547/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_38 : ((1135313/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos525o2c k) + cos525o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_37
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 38 - ((196847/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_39 : ((6613271/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos525o2c k) + cos525o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_38
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 39 - ((468373/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_40 : ((7364827/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos525o2c k) + cos525o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_39
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 40 - ((187899/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_41 : ((159429/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos525o2c k) + cos525o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_40
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 41 - ((606663/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_42 : ((8543803/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos525o2c k) + cos525o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_41
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 42 - ((572393/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_43 : ((4600011/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos525o2c k) + cos525o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_42
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 43 - ((656259/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_44 : ((2505407/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos525o2c k) + cos525o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_43
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 44 - ((410823/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_45 : ((1374619/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos525o2c k) + cos525o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_44
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 45 - ((243841/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_46 : ((2390957/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos525o2c k) + cos525o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_45
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 46 - ((957873/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_47 : ((12553319/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos525o2c k) + cos525o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_46
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 47 - ((299287/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_48 : ((1554823/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos525o2c k) + cos525o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_47
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 48 - ((-22939/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_49 : ((725309/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos525o2c k) + cos525o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_48
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 49 - ((-521/625 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_50 : ((1068181/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos525o2c k) + cos525o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_49
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 50 - ((-461547/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_51 : ((10590849/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos525o2c k) + cos525o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_50
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 51 - ((-90921/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_52 : ((5739843/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos525o2c k) + cos525o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_51
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 52 - ((888877/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_53 : ((486849/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos525o2c k) + cos525o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_52
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 53 - ((691579/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_54 : ((2319199/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos525o2c k) + cos525o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_53
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 54 - ((-57519/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_55 : ((5361261/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos525o2c k) + cos525o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_54
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 55 - ((-873433/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_56 : ((699631/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos525o2c k) + cos525o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_55
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 56 - ((235807/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_57 : ((12042709/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos525o2c k) + cos525o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_56
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 57 - ((848653/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_58 : ((712193/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos525o2c k) + cos525o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_57
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 58 - ((-647581/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_59 : ((431873/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos525o2c k) + cos525o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_58
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 59 - ((-598223/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_60 : ((11739287/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos525o2c k) + cos525o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_59
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 60 - ((471251/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_61 : ((5853281/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos525o2c k) + cos525o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_60
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 61 - ((-6537/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_62 : ((10818007/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos525o2c k) + cos525o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_61
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 62 - ((-177703/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_63 : ((5826717/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos525o2c k) + cos525o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_62
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 63 - ((835467/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_64 : ((2914187/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos525o2c k) + cos525o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_63
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 64 - ((1677/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_65 : ((86833/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos525o2c k) + cos525o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_64
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 65 - ((-802583/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_66 : ((2957111/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos525o2c k) + cos525o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_65
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 66 - ((974359/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_67 : ((11315987/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos525o2c k) + cos525o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_66
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 67 - ((-512417/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_68 : ((11108099/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos525o2c k) + cos525o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_67
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 68 - ((-25981/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_69 : ((2378273/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos525o2c k) + cos525o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_68
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 69 - ((391653/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_70 : ((10891951/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos525o2c k) + cos525o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_69
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 70 - ((-499687/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_71 : ((367071/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos525o2c k) + cos525o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_70
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 71 - ((854361/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_72 : ((704477/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos525o2c k) + cos525o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_71
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 72 - ((-2373/5000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_73 : ((1410869/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos525o2c k) + cos525o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_72
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 73 - ((48/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_74 : ((584483/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos525o2c k) + cos525o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_73
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 74 - ((100687/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_75 : ((2194943/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos525o2c k) + cos525o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_74
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 75 - ((-142981/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_76 : ((11879837/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos525o2c k) + cos525o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_75
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 76 - ((452581/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_77 : ((10890907/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos525o2c k) + cos525o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_76
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 77 - ((-98889/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_78 : ((11886229/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos525o2c k) + cos525o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_77
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 78 - ((497681/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_79 : ((5465241/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos525o2c k) + cos525o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_78
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 79 - ((-955707/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_80 : ((11826901/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos525o2c k) + cos525o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_79
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 80 - ((896459/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_81 : ((10989521/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos525o2c k) + cos525o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_80
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 81 - ((-41867/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_82 : ((11780877/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos525o2c k) + cos525o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_81
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 82 - ((197849/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_83 : ((1376837/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos525o2c k) + cos525o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_82
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 83 - ((-766141/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_84 : ((1472427/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos525o2c k) + cos525o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_83
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 84 - ((19119/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_85 : ((2748127/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos525o2c k) + cos525o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_84
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 85 - ((-196717/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_86 : ((1477669/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos525o2c k) + cos525o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_85
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 86 - ((207221/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_87 : ((10937491/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos525o2c k) + cos525o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_86
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 87 - ((-883821/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_88 : ((2375687/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos525o2c k) + cos525o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_87
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 88 - ((117623/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_89 : ((1361597/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos525o2c k) + cos525o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_88
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 89 - ((-985619/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_90 : ((11891983/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos525o2c k) + cos525o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_89
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 90 - ((999247/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_91 : ((2186167/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos525o2c k) + cos525o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_90
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 91 - ((-240277/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_92 : ((2356399/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos525o2c k) + cos525o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_91
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 92 - ((532/625 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_93 : ((347709/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos525o2c k) + cos525o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_92
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 93 - ((-655267/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_94 : ((2874499/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos525o2c k) + cos525o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_93
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 94 - ((92837/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_95 : ((1435161/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos525o2c k) + cos525o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_94
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 95 - ((-4167/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_96 : ((2778463/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos525o2c k) + cos525o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_95
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 96 - ((-91849/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_97 : ((1182947/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos525o2c k) + cos525o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_96
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 97 - ((357829/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_98 : ((10881451/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos525o2c k) + cos525o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_97
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 98 - ((-947979/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_99 : ((11869787/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos525o2c k) + cos525o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_98
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 99 - ((123547/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_100 : ((11077313/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos525o2c k) + cos525o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_99
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 100 - ((-396217/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_101 : ((2863249/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos525o2c k) + cos525o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_100
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 101 - ((375723/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_102 : ((11622323/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos525o2c k) + cos525o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_101
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 102 - ((169367/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_103 : ((1367507/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos525o2c k) + cos525o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_102
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 103 - ((-682227/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_104 : ((11917067/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos525o2c k) + cos525o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_103
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 104 - ((977051/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_105 : ((11001891/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos525o2c k) + cos525o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_104
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 105 - ((-14299/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_106 : ((179428/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos525o2c k) + cos525o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_105
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 106 - ((481541/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_107 : ((2914207/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos525o2c k) + cos525o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_106
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 107 - ((43369/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_108 : ((136123/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos525o2c k) + cos525o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_107
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 108 - ((-191737/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_109 : ((475579/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos525o2c k) + cos525o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_108
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 109 - ((39987/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_110 : ((55857/5000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos525o2c k) + cos525o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_109
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 110 - ((-143607/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_111 : ((5603167/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos525o2c k) + cos525o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_110
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 111 - ((17487/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_112 : ((11889653/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos525o2c k) + cos525o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_111
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 112 - ((683359/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_113 : ((2177933/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos525o2c k) + cos525o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_112
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 113 - ((-249987/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_114 : ((11572871/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos525o2c k) + cos525o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_113
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 114 - ((341623/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_115 : ((5834739/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos525o2c k) + cos525o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_114
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 115 - ((96647/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_116 : ((1084701/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos525o2c k) + cos525o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_115
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 116 - ((-205607/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_117 : ((2951783/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos525o2c k) + cos525o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_116
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 117 - ((480081/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_118 : ((11436127/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos525o2c k) + cos525o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_117
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 118 - ((-74193/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_119 : ((10916507/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos525o2c k) + cos525o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_118
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 119 - ((-25979/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_120 : ((11913307/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos525o2c k) + cos525o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_119
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 120 - ((24921/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_121 : ((11278921/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos525o2c k) + cos525o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_120
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 121 - ((-317173/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_122 : ((1098917/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos525o2c k) + cos525o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_121
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 122 - ((-289711/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_123 : ((1493837/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos525o2c k) + cos525o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_122
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 123 - ((480783/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_124 : ((2242159/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos525o2c k) + cos525o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_123
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 124 - ((-739861/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_125 : ((2202363/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos525o2c k) + cos525o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_124
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 125 - ((-9947/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_126 : ((2990207/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos525o2c k) + cos525o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_125
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 126 - ((949053/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_127 : ((11226327/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos525o2c k) + cos525o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_126
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 127 - ((-734461/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_128 : ((2194251/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos525o2c k) + cos525o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_127
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 128 - ((-31879/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_129 : ((2987093/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos525o2c k) + cos525o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_128
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 129 - ((977157/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_130 : ((11327049/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos525o2c k) + cos525o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_129
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 130 - ((-621283/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_131 : ((170052/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos525o2c k) + cos525o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_130
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 131 - ((-443681/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_132 : ((118827/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos525o2c k) + cos525o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_131
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 132 - ((249853/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_133 : ((719713/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos525o2c k) + cos525o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_132
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 133 - ((-91813/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_134 : ((10798539/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos525o2c k) + cos525o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_133
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 134 - ((-716829/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_135 : ((11712253/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos525o2c k) + cos525o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_134
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 135 - ((456877/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_136 : ((2941019/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos525o2c k) + cos525o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_135
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 136 - ((51863/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_137 : ((10808823/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos525o2c k) + cos525o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_136
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 137 - ((-955213/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_138 : ((570247/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos525o2c k) + cos525o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_137
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 138 - ((596157/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_139 : ((2993941/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos525o2c k) + cos525o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_138
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 139 - ((35679/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_140 : ((2203879/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos525o2c k) + cos525o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_139
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 140 - ((-956329/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_141 : ((11020253/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos525o2c k) + cos525o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_140
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 141 - ((449/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_142 : ((11979807/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos525o2c k) + cos525o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_141
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 142 - ((479797/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_143 : ((5725747/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos525o2c k) + cos525o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_142
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 143 - ((-528273/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_144 : ((2153121/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos525o2c k) + cos525o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_143
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 144 - ((-685849/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_145 : ((5819171/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos525o2c k) + cos525o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_144
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 145 - ((872777/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_146 : ((11911383/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos525o2c k) + cos525o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_145
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 146 - ((273081/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_147 : ((1364111/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos525o2c k) + cos525o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_146
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 147 - ((-199691/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_148 : ((11065531/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos525o2c k) + cos525o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_147
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 148 - ((152683/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_149 : ((12004799/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos525o2c k) + cos525o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_148
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 149 - ((234827/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_150 : ((5747361/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos525o2c k) + cos525o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_149
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 150 - ((-510037/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_151 : ((10735433/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos525o2c k) + cos525o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_150
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 151 - ((-759249/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_152 : ((11500061/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos525o2c k) + cos525o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_151
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 152 - ((191167/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_153 : ((6011247/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos525o2c k) + cos525o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_152
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 153 - ((522473/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_154 : ((11105507/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos525o2c k) + cos525o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_153
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 154 - ((-916947/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_155 : ((2706749/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos525o2c k) + cos525o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_154
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 155 - ((-278471/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_156 : ((11813393/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos525o2c k) + cos525o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_155
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 156 - ((986437/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_157 : ((37099/3125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos525o2c k) + cos525o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_156
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 157 - ((58327/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_158 : ((10872343/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos525o2c k) + cos525o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_157
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 158 - ((-999297/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_159 : ((10994871/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos525o2c k) + cos525o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_158
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 159 - ((15321/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_160 : ((5987661/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos525o2c k) + cos525o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_159
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 160 - ((980491/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_161 : ((732233/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos525o2c k) + cos525o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_160
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 161 - ((-129777/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_162 : ((2691391/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos525o2c k) + cos525o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_161
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 162 - ((-237531/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_163 : ((11119451/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos525o2c k) + cos525o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_162
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 163 - ((353927/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_164 : ((150523/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos525o2c k) + cos525o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_163
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 164 - ((922429/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_165 : ((11632749/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos525o2c k) + cos525o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_164
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 165 - ((-409051/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_166 : ((5363283/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos525o2c k) + cos525o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_165
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 166 - ((-906143/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_167 : ((44619/4000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos525o2c k) + cos525o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_166
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 167 - ((6691/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_168 : ((6029969/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos525o2c k) + cos525o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_167
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 168 - ((226307/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_169 : ((5823347/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos525o2c k) + cos525o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_168
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 169 - ((-103301/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_170 : ((10727097/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos525o2c k) + cos525o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_169
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 170 - ((-919557/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_171 : ((1109113/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos525o2c k) + cos525o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_170
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 171 - ((364073/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_172 : ((2407267/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos525o2c k) + cos525o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_171
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 172 - ((189049/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_173 : ((11756679/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos525o2c k) + cos525o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_172
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 173 - ((-4369/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_174 : ((2695493/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos525o2c k) + cos525o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_173
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 174 - ((-974667/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_175 : ((1367543/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos525o2c k) + cos525o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_174
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 175 - ((39603/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_176 : ((11936777/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos525o2c k) + cos525o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_175
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 176 - ((996473/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_177 : ((9549/800 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos525o2c k) + cos525o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_176
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 177 - ((-487/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_178 : ((10940387/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos525o2c k) + cos525o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_177
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 178 - ((-995823/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_179 : ((167967/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos525o2c k) + cos525o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_178
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 179 - ((-190459/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_180 : ((11705173/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos525o2c k) + cos525o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_179
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 180 - ((38213/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_181 : ((484389/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos525o2c k) + cos525o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_180
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 181 - ((25287/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_182 : ((11252521/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos525o2c k) + cos525o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_181
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 182 - ((-214291/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_183 : ((5314383/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos525o2c k) + cos525o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_182
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 183 - ((-124743/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_184 : ((2263099/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos525o2c k) + cos525o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_183
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 184 - ((686769/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_185 : ((3033917/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos525o2c k) + cos525o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_184
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 185 - ((820213/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_186 : ((11697691/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos525o2c k) + cos525o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_185
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 186 - ((-437937/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_187 : ((1342427/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos525o2c k) + cos525o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_186
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 187 - ((-191647/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_188 : ((135729/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos525o2c k) + cos525o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_187
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 188 - ((3717/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_189 : ((11856541/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos525o2c k) + cos525o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_188
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 189 - ((998261/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_190 : ((3024659/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos525o2c k) + cos525o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_189
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 190 - ((48427/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_191 : ((5596369/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos525o2c k) + cos525o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_190
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 191 - ((-452929/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_192 : ((2649389/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos525o2c k) + cos525o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_191
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 192 - ((-297571/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_193 : ((1407693/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos525o2c k) + cos525o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_192
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 193 - ((166007/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_194 : ((1516659/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos525o2c k) + cos525o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_193
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 194 - ((108971/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_195 : ((370203/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos525o2c k) + cos525o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_194
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 195 - ((-17921/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_196 : ((10848423/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos525o2c k) + cos525o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_195
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 196 - ((-998033/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_197 : ((533853/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos525o2c k) + cos525o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_196
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 197 - ((-171323/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_198 : ((5796299/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos525o2c k) + cos525o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_197
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 198 - ((457789/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_199 : ((1525929/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos525o2c k) + cos525o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_198
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 199 - ((307437/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_200 : ((11599379/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos525o2c k) + cos525o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_199
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 200 - ((-608013/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_201 : ((5337597/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos525o2c k) + cos525o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_200
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 201 - ((-184829/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_202 : ((10798753/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos525o2c k) + cos525o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_201
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 202 - ((123599/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_203 : ((5893699/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos525o2c k) + cos525o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_202
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 203 - ((197737/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_204 : ((1525693/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos525o2c k) + cos525o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_203
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 204 - ((209093/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_205 : ((2863197/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos525o2c k) + cos525o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_204
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 205 - ((-188179/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_206 : ((5302417/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos525o2c k) + cos525o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_205
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 206 - ((-423957/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_207 : ((1357631/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos525o2c k) + cos525o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_206
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 207 - ((128127/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_208 : ((11859923/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos525o2c k) + cos525o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_207
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 208 - ((199783/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_209 : ((152633/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos525o2c k) + cos525o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_208
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 209 - ((350757/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_210 : ((5715317/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos525o2c k) + cos525o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_209
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 210 - ((-389983/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_211 : ((10589151/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos525o2c k) + cos525o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_210
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 211 - ((-841443/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_212 : ((5413979/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos525o2c k) + cos525o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_211
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 212 - ((238847/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_213 : ((11823473/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos525o2c k) + cos525o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_212
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 213 - ((199111/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_214 : ((612269/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos525o2c k) + cos525o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_213
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 214 - ((421947/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_215 : ((11536267/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos525o2c k) + cos525o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_214
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 215 - ((-709073/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_216 : ((2657391/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos525o2c k) + cos525o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_215
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 216 - ((-906663/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_217 : ((2676651/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos525o2c k) + cos525o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_216
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 217 - ((1927/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_218 : ((5832867/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos525o2c k) + cos525o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_217
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 218 - ((95917/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_219 : ((1227577/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos525o2c k) + cos525o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_218
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 219 - ((152519/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_220 : ((1470227/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos525o2c k) + cos525o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_219
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 220 - ((-256957/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_221 : ((10774459/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos525o2c k) + cos525o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_220
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 221 - ((-987317/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_222 : ((5275033/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos525o2c k) + cos525o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_221
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 222 - ((-224353/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_223 : ((11365473/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos525o2c k) + cos525o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_222
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 223 - ((815447/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_224 : ((12214167/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos525o2c k) + cos525o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_223
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 224 - ((424367/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_225 : ((12059063/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos525o2c k) + cos525o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_224
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 225 - ((-19383/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_226 : ((11090367/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos525o2c k) + cos525o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_225
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 226 - ((-60541/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_227 : ((10474937/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos525o2c k) + cos525o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_226
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 227 - ((-61539/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_228 : ((5473187/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos525o2c k) + cos525o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_227
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 228 - ((471477/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_229 : ((2985989/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos525o2c k) + cos525o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_228
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 229 - ((498811/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_230 : ((12294347/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos525o2c k) + cos525o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_229
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 230 - ((350431/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_231 : ((579523/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos525o2c k) + cos525o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_230
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 231 - ((-703847/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_232 : ((2662243/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos525o2c k) + cos525o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_231
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 232 - ((-117681/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_233 : ((2637807/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos525o2c k) + cos525o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_232
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 233 - ((-12213/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_234 : ((11406601/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos525o2c k) + cos525o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_233
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 234 - ((855413/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_235 : ((12245777/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos525o2c k) + cos525o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_234
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 235 - ((52451/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_236 : ((6063601/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos525o2c k) + cos525o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_235
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 236 - ((-23707/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_237 : ((5592547/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos525o2c k) + cos525o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_236
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 237 - ((-235517/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_238 : ((2615607/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos525o2c k) + cos525o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_237
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 238 - ((-361313/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_239 : ((2150251/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos525o2c k) + cos525o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_238
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 239 - ((288867/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_240 : ((11734751/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos525o2c k) + cos525o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_239
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 240 - ((61471/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_241 : ((12348643/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos525o2c k) + cos525o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_240
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 241 - ((153483/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_242 : ((11935437/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos525o2c k) + cos525o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_241
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 242 - ((-206583/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_243 : ((10937343/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos525o2c k) + cos525o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_242
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 243 - ((-499027/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_244 : ((416409/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos525o2c k) + cos525o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_243
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 244 - ((-263539/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_245 : ((5452861/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos525o2c k) + cos525o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_244
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 245 - ((495537/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_246 : ((11905539/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos525o2c k) + cos525o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_245
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 246 - ((999857/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_247 : ((618761/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos525o2c k) + cos525o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_246
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 247 - ((469721/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_248 : ((184909/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos525o2c k) + cos525o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_247
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 248 - ((-135251/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_249 : ((10835769/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos525o2c k) + cos525o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_248
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 249 - ((-998367/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum525o2_250 : ((2597607/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos525o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos525o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos525o2c k) + cos525o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos525o2c
    simpa using h
  have hprev := psum525o2_249
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos525o2c 250 - ((-445301/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos525o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 3200000 in
/-- **The Abel floor at `t = 525/2`.** -/
theorem psum525o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 250 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos525o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum525o2_11
  · exact le_trans (by norm_num) psum525o2_12
  · exact le_trans (by norm_num) psum525o2_13
  · exact le_trans (by norm_num) psum525o2_14
  · exact le_trans (by norm_num) psum525o2_15
  · exact le_trans (by norm_num) psum525o2_16
  · exact le_trans (by norm_num) psum525o2_17
  · exact le_trans (by norm_num) psum525o2_18
  · exact le_trans (by norm_num) psum525o2_19
  · exact le_trans (by norm_num) psum525o2_20
  · exact le_trans (by norm_num) psum525o2_21
  · exact le_trans (by norm_num) psum525o2_22
  · exact le_trans (by norm_num) psum525o2_23
  · exact le_trans (by norm_num) psum525o2_24
  · exact le_trans (by norm_num) psum525o2_25
  · exact le_trans (by norm_num) psum525o2_26
  · exact le_trans (by norm_num) psum525o2_27
  · exact le_trans (by norm_num) psum525o2_28
  · exact le_trans (by norm_num) psum525o2_29
  · exact le_trans (by norm_num) psum525o2_30
  · exact le_trans (by norm_num) psum525o2_31
  · exact le_trans (by norm_num) psum525o2_32
  · exact le_trans (by norm_num) psum525o2_33
  · exact le_trans (by norm_num) psum525o2_34
  · exact le_trans (by norm_num) psum525o2_35
  · exact le_trans (by norm_num) psum525o2_36
  · exact le_trans (by norm_num) psum525o2_37
  · exact le_trans (by norm_num) psum525o2_38
  · exact le_trans (by norm_num) psum525o2_39
  · exact le_trans (by norm_num) psum525o2_40
  · exact le_trans (by norm_num) psum525o2_41
  · exact le_trans (by norm_num) psum525o2_42
  · exact le_trans (by norm_num) psum525o2_43
  · exact le_trans (by norm_num) psum525o2_44
  · exact le_trans (by norm_num) psum525o2_45
  · exact le_trans (by norm_num) psum525o2_46
  · exact le_trans (by norm_num) psum525o2_47
  · exact le_trans (by norm_num) psum525o2_48
  · exact le_trans (by norm_num) psum525o2_49
  · exact le_trans (by norm_num) psum525o2_50
  · exact le_trans (by norm_num) psum525o2_51
  · exact le_trans (by norm_num) psum525o2_52
  · exact le_trans (by norm_num) psum525o2_53
  · exact le_trans (by norm_num) psum525o2_54
  · exact le_trans (by norm_num) psum525o2_55
  · exact le_trans (by norm_num) psum525o2_56
  · exact le_trans (by norm_num) psum525o2_57
  · exact le_trans (by norm_num) psum525o2_58
  · exact le_trans (by norm_num) psum525o2_59
  · exact le_trans (by norm_num) psum525o2_60
  · exact le_trans (by norm_num) psum525o2_61
  · exact le_trans (by norm_num) psum525o2_62
  · exact le_trans (by norm_num) psum525o2_63
  · exact le_trans (by norm_num) psum525o2_64
  · exact le_trans (by norm_num) psum525o2_65
  · exact le_trans (by norm_num) psum525o2_66
  · exact le_trans (by norm_num) psum525o2_67
  · exact le_trans (by norm_num) psum525o2_68
  · exact le_trans (by norm_num) psum525o2_69
  · exact le_trans (by norm_num) psum525o2_70
  · exact le_trans (by norm_num) psum525o2_71
  · exact le_trans (by norm_num) psum525o2_72
  · exact le_trans (by norm_num) psum525o2_73
  · exact le_trans (by norm_num) psum525o2_74
  · exact le_trans (by norm_num) psum525o2_75
  · exact le_trans (by norm_num) psum525o2_76
  · exact le_trans (by norm_num) psum525o2_77
  · exact le_trans (by norm_num) psum525o2_78
  · exact le_trans (by norm_num) psum525o2_79
  · exact le_trans (by norm_num) psum525o2_80
  · exact le_trans (by norm_num) psum525o2_81
  · exact le_trans (by norm_num) psum525o2_82
  · exact le_trans (by norm_num) psum525o2_83
  · exact le_trans (by norm_num) psum525o2_84
  · exact le_trans (by norm_num) psum525o2_85
  · exact le_trans (by norm_num) psum525o2_86
  · exact le_trans (by norm_num) psum525o2_87
  · exact le_trans (by norm_num) psum525o2_88
  · exact le_trans (by norm_num) psum525o2_89
  · exact le_trans (by norm_num) psum525o2_90
  · exact le_trans (by norm_num) psum525o2_91
  · exact le_trans (by norm_num) psum525o2_92
  · exact le_trans (by norm_num) psum525o2_93
  · exact le_trans (by norm_num) psum525o2_94
  · exact le_trans (by norm_num) psum525o2_95
  · exact le_trans (by norm_num) psum525o2_96
  · exact le_trans (by norm_num) psum525o2_97
  · exact le_trans (by norm_num) psum525o2_98
  · exact le_trans (by norm_num) psum525o2_99
  · exact le_trans (by norm_num) psum525o2_100
  · exact le_trans (by norm_num) psum525o2_101
  · exact le_trans (by norm_num) psum525o2_102
  · exact le_trans (by norm_num) psum525o2_103
  · exact le_trans (by norm_num) psum525o2_104
  · exact le_trans (by norm_num) psum525o2_105
  · exact le_trans (by norm_num) psum525o2_106
  · exact le_trans (by norm_num) psum525o2_107
  · exact le_trans (by norm_num) psum525o2_108
  · exact le_trans (by norm_num) psum525o2_109
  · exact le_trans (by norm_num) psum525o2_110
  · exact le_trans (by norm_num) psum525o2_111
  · exact le_trans (by norm_num) psum525o2_112
  · exact le_trans (by norm_num) psum525o2_113
  · exact le_trans (by norm_num) psum525o2_114
  · exact le_trans (by norm_num) psum525o2_115
  · exact le_trans (by norm_num) psum525o2_116
  · exact le_trans (by norm_num) psum525o2_117
  · exact le_trans (by norm_num) psum525o2_118
  · exact le_trans (by norm_num) psum525o2_119
  · exact le_trans (by norm_num) psum525o2_120
  · exact le_trans (by norm_num) psum525o2_121
  · exact le_trans (by norm_num) psum525o2_122
  · exact le_trans (by norm_num) psum525o2_123
  · exact le_trans (by norm_num) psum525o2_124
  · exact le_trans (by norm_num) psum525o2_125
  · exact le_trans (by norm_num) psum525o2_126
  · exact le_trans (by norm_num) psum525o2_127
  · exact le_trans (by norm_num) psum525o2_128
  · exact le_trans (by norm_num) psum525o2_129
  · exact le_trans (by norm_num) psum525o2_130
  · exact le_trans (by norm_num) psum525o2_131
  · exact le_trans (by norm_num) psum525o2_132
  · exact le_trans (by norm_num) psum525o2_133
  · exact le_trans (by norm_num) psum525o2_134
  · exact le_trans (by norm_num) psum525o2_135
  · exact le_trans (by norm_num) psum525o2_136
  · exact le_trans (by norm_num) psum525o2_137
  · exact le_trans (by norm_num) psum525o2_138
  · exact le_trans (by norm_num) psum525o2_139
  · exact le_trans (by norm_num) psum525o2_140
  · exact le_trans (by norm_num) psum525o2_141
  · exact le_trans (by norm_num) psum525o2_142
  · exact le_trans (by norm_num) psum525o2_143
  · exact le_trans (by norm_num) psum525o2_144
  · exact le_trans (by norm_num) psum525o2_145
  · exact le_trans (by norm_num) psum525o2_146
  · exact le_trans (by norm_num) psum525o2_147
  · exact le_trans (by norm_num) psum525o2_148
  · exact le_trans (by norm_num) psum525o2_149
  · exact le_trans (by norm_num) psum525o2_150
  · exact le_trans (by norm_num) psum525o2_151
  · exact le_trans (by norm_num) psum525o2_152
  · exact le_trans (by norm_num) psum525o2_153
  · exact le_trans (by norm_num) psum525o2_154
  · exact le_trans (by norm_num) psum525o2_155
  · exact le_trans (by norm_num) psum525o2_156
  · exact le_trans (by norm_num) psum525o2_157
  · exact le_trans (by norm_num) psum525o2_158
  · exact le_trans (by norm_num) psum525o2_159
  · exact le_trans (by norm_num) psum525o2_160
  · exact le_trans (by norm_num) psum525o2_161
  · exact le_trans (by norm_num) psum525o2_162
  · exact le_trans (by norm_num) psum525o2_163
  · exact le_trans (by norm_num) psum525o2_164
  · exact le_trans (by norm_num) psum525o2_165
  · exact le_trans (by norm_num) psum525o2_166
  · exact le_trans (by norm_num) psum525o2_167
  · exact le_trans (by norm_num) psum525o2_168
  · exact le_trans (by norm_num) psum525o2_169
  · exact le_trans (by norm_num) psum525o2_170
  · exact le_trans (by norm_num) psum525o2_171
  · exact le_trans (by norm_num) psum525o2_172
  · exact le_trans (by norm_num) psum525o2_173
  · exact le_trans (by norm_num) psum525o2_174
  · exact le_trans (by norm_num) psum525o2_175
  · exact le_trans (by norm_num) psum525o2_176
  · exact le_trans (by norm_num) psum525o2_177
  · exact le_trans (by norm_num) psum525o2_178
  · exact le_trans (by norm_num) psum525o2_179
  · exact le_trans (by norm_num) psum525o2_180
  · exact le_trans (by norm_num) psum525o2_181
  · exact le_trans (by norm_num) psum525o2_182
  · exact le_trans (by norm_num) psum525o2_183
  · exact le_trans (by norm_num) psum525o2_184
  · exact le_trans (by norm_num) psum525o2_185
  · exact le_trans (by norm_num) psum525o2_186
  · exact le_trans (by norm_num) psum525o2_187
  · exact le_trans (by norm_num) psum525o2_188
  · exact le_trans (by norm_num) psum525o2_189
  · exact le_trans (by norm_num) psum525o2_190
  · exact le_trans (by norm_num) psum525o2_191
  · exact le_trans (by norm_num) psum525o2_192
  · exact le_trans (by norm_num) psum525o2_193
  · exact le_trans (by norm_num) psum525o2_194
  · exact le_trans (by norm_num) psum525o2_195
  · exact le_trans (by norm_num) psum525o2_196
  · exact le_trans (by norm_num) psum525o2_197
  · exact le_trans (by norm_num) psum525o2_198
  · exact le_trans (by norm_num) psum525o2_199
  · exact le_trans (by norm_num) psum525o2_200
  · exact le_trans (by norm_num) psum525o2_201
  · exact le_trans (by norm_num) psum525o2_202
  · exact le_trans (by norm_num) psum525o2_203
  · exact le_trans (by norm_num) psum525o2_204
  · exact le_trans (by norm_num) psum525o2_205
  · exact le_trans (by norm_num) psum525o2_206
  · exact le_trans (by norm_num) psum525o2_207
  · exact le_trans (by norm_num) psum525o2_208
  · exact le_trans (by norm_num) psum525o2_209
  · exact le_trans (by norm_num) psum525o2_210
  · exact le_trans (by norm_num) psum525o2_211
  · exact le_trans (by norm_num) psum525o2_212
  · exact le_trans (by norm_num) psum525o2_213
  · exact le_trans (by norm_num) psum525o2_214
  · exact le_trans (by norm_num) psum525o2_215
  · exact le_trans (by norm_num) psum525o2_216
  · exact le_trans (by norm_num) psum525o2_217
  · exact le_trans (by norm_num) psum525o2_218
  · exact le_trans (by norm_num) psum525o2_219
  · exact le_trans (by norm_num) psum525o2_220
  · exact le_trans (by norm_num) psum525o2_221
  · exact le_trans (by norm_num) psum525o2_222
  · exact le_trans (by norm_num) psum525o2_223
  · exact le_trans (by norm_num) psum525o2_224
  · exact le_trans (by norm_num) psum525o2_225
  · exact le_trans (by norm_num) psum525o2_226
  · exact le_trans (by norm_num) psum525o2_227
  · exact le_trans (by norm_num) psum525o2_228
  · exact le_trans (by norm_num) psum525o2_229
  · exact le_trans (by norm_num) psum525o2_230
  · exact le_trans (by norm_num) psum525o2_231
  · exact le_trans (by norm_num) psum525o2_232
  · exact le_trans (by norm_num) psum525o2_233
  · exact le_trans (by norm_num) psum525o2_234
  · exact le_trans (by norm_num) psum525o2_235
  · exact le_trans (by norm_num) psum525o2_236
  · exact le_trans (by norm_num) psum525o2_237
  · exact le_trans (by norm_num) psum525o2_238
  · exact le_trans (by norm_num) psum525o2_239
  · exact le_trans (by norm_num) psum525o2_240
  · exact le_trans (by norm_num) psum525o2_241
  · exact le_trans (by norm_num) psum525o2_242
  · exact le_trans (by norm_num) psum525o2_243
  · exact le_trans (by norm_num) psum525o2_244
  · exact le_trans (by norm_num) psum525o2_245
  · exact le_trans (by norm_num) psum525o2_246
  · exact le_trans (by norm_num) psum525o2_247
  · exact le_trans (by norm_num) psum525o2_248
  · exact le_trans (by norm_num) psum525o2_249
  · exact le_trans (by norm_num) psum525o2_250

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum525o2_floor
#print axioms CriticalLinePhasor.DVP.psum525o2_250
end AxiomAudit
