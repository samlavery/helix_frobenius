import RequestProject.DVPCos671o2Table

/-!
# The cosine partial-sum floor, `t = 671/2` (N = 500)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 671/2` segment certificate. -/
def cos671o2c (n : ℕ) : ℝ := Real.cos (((671:ℕ):ℝ) * (Real.log n / 2))

theorem psum671o2_11 : ((969761/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos671o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 11 - ((969861/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum671o2_12 : ((574109/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos671o2c k) + cos671o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_11
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 12 - ((-12361/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_13 : ((30829/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos671o2c k) + cos671o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_12
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 13 - ((967441/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_14 : ((30081/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos671o2c k) + cos671o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_13
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 14 - ((86513/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_15 : ((319739/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos671o2c k) + cos671o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_14
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 15 - ((-161537/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_16 : ((639059/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos671o2c k) + cos671o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_15
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 16 - ((957641/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_17 : ((586601/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos671o2c k) + cos671o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_16
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 17 - ((-52433/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_18 : ((1833551/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos671o2c k) + cos671o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_17
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 18 - ((-512753/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_19 : ((250529/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos671o2c k) + cos671o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_18
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 19 - ((170781/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_20 : ((2975117/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos671o2c k) + cos671o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_19
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 20 - ((194197/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_21 : ((2061793/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos671o2c k) + cos671o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_20
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 21 - ((-114153/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_22 : ((301119/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos671o2c k) + cos671o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_21
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 22 - ((949497/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_23 : ((2121897/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos671o2c k) + cos671o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_22
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 23 - ((-889193/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_24 : ((1794313/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos671o2c k) + cos671o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_23
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 24 - ((-81871/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_25 : ((313577/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos671o2c k) + cos671o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_24
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 25 - ((714403/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_26 : ((698369/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos671o2c k) + cos671o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_25
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 26 - ((983329/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_27 : ((1121983/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos671o2c k) + cos671o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_26
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 27 - ((996187/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_28 : ((5387251/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos671o2c k) + cos671o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_27
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 28 - ((899419/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_29 : ((713331/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos671o2c k) + cos671o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_28
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 29 - ((319497/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_30 : ((309001/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos671o2c k) + cos671o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_29
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 30 - ((-190633/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_31 : ((429283/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos671o2c k) + cos671o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_30
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 31 - ((-325543/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_32 : ((653351/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos671o2c k) + cos671o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_31
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 32 - ((467039/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_33 : ((984983/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos671o2c k) + cos671o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_32
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 33 - ((-301793/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_34 : ((46443/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos671o2c k) + cos671o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_33
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 34 - ((-56103/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_35 : ((2598141/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos671o2c k) + cos671o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_34
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 35 - ((276041/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_36 : ((4622153/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos671o2c k) + cos671o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_35
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 36 - ((-574029/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_37 : ((4992049/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos671o2c k) + cos671o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_36
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 37 - ((92499/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_38 : ((2545191/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos671o2c k) + cos671o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_37
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 38 - ((98433/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_39 : ((4366967/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos671o2c k) + cos671o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_38
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 39 - ((-144663/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_40 : ((5352713/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos671o2c k) + cos671o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_39
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 40 - ((492923/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_41 : ((2546831/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos671o2c k) + cos671o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_40
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 41 - ((-258951/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_42 : ((2106251/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos671o2c k) + cos671o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_41
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 42 - ((-44053/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_43 : ((2360347/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos671o2c k) + cos671o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_42
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 43 - ((127073/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_44 : ((2822333/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos671o2c k) + cos671o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_43
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 44 - ((115509/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_45 : ((2783403/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos671o2c k) + cos671o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_44
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 45 - ((-243/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_46 : ((4646513/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos671o2c k) + cos671o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_45
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 46 - ((-920193/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_47 : ((118237/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos671o2c k) + cos671o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_46
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 47 - ((-862829/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_48 : ((1762907/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos671o2c k) + cos671o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_47
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 48 - ((-25767/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_49 : ((1945503/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos671o2c k) + cos671o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_48
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 49 - ((91323/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_50 : ((4654461/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos671o2c k) + cos671o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_49
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 50 - ((152711/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_51 : ((1119329/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos671o2c k) + cos671o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_50
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 51 - ((235571/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_52 : ((6590521/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos671o2c k) + cos671o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_51
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 52 - ((124247/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_53 : ((3795209/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos671o2c k) + cos671o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_52
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 53 - ((999997/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_54 : ((1718043/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos671o2c k) + cos671o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_53
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 54 - ((999897/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_55 : ((9580137/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos671o2c k) + cos671o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_54
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 55 - ((495011/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_56 : ((5254469/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos671o2c k) + cos671o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_55
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 56 - ((928901/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_57 : ((562889/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos671o2c k) + cos671o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_56
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 57 - ((374471/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_58 : ((5822733/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos671o2c k) + cos671o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_57
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 58 - ((193893/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_59 : ((11496139/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos671o2c k) + cos671o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_58
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 59 - ((-149227/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_60 : ((10782743/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos671o2c k) + cos671o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_59
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 60 - ((-44581/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_61 : ((9783403/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos671o2c k) + cos671o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_60
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 61 - ((-24981/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_62 : ((2269649/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos671o2c k) + cos671o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_61
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 62 - ((-704707/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_63 : ((1842229/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos671o2c k) + cos671o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_62
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 63 - ((132649/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_64 : ((5058297/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos671o2c k) + cos671o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_63
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 64 - ((905549/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_65 : ((5458277/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos671o2c k) + cos671o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_64
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 65 - ((40003/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_66 : ((2671257/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos671o2c k) + cos671o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_65
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 66 - ((-115713/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_67 : ((2422463/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos671o2c k) + cos671o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_66
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 67 - ((-248769/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_68 : ((186799/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos671o2c k) + cos671o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_67
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 68 - ((-174901/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_69 : ((10196081/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos671o2c k) + cos671o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_68
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 69 - ((856231/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_70 : ((2701857/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos671o2c k) + cos671o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_69
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 70 - ((611447/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_71 : ((10045349/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos671o2c k) + cos671o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_70
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 71 - ((-761979/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_72 : ((2353251/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos671o2c k) + cos671o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_71
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 72 - ((-126449/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_73 : ((10238403/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos671o2c k) + cos671o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_72
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 73 - ((825499/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_74 : ((2668767/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos671o2c k) + cos671o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_73
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 74 - ((87353/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_75 : ((4852181/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos671o2c k) + cos671o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_74
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 75 - ((-485303/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_76 : ((9729823/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos671o2c k) + cos671o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_75
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 76 - ((25561/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_77 : ((10668317/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos671o2c k) + cos671o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_76
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 77 - ((469297/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_78 : ((4998607/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos671o2c k) + cos671o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_77
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 78 - ((-671003/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_79 : ((9610663/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos671o2c k) + cos671o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_78
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 79 - ((-386451/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_80 : ((5303007/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos671o2c k) + cos671o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_79
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 80 - ((995451/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_81 : ((1000867/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos671o2c k) + cos671o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_80
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 81 - ((-149311/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_82 : ((4839917/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos671o2c k) + cos671o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_81
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 82 - ((-10273/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_83 : ((664491/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos671o2c k) + cos671o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_82
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 83 - ((476061/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_84 : ((2446887/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos671o2c k) + cos671o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_83
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 84 - ((-52763/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_85 : ((9962757/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos671o2c k) + cos671o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_84
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 85 - ((175309/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_86 : ((5266201/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos671o2c k) + cos671o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_85
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 86 - ((113949/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_87 : ((9558071/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos671o2c k) + cos671o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_86
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 87 - ((-974231/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_88 : ((2612923/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos671o2c k) + cos671o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_87
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 88 - ((893721/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_89 : ((2502767/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos671o2c k) + cos671o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_88
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 89 - ((-110131/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_90 : ((154073/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos671o2c k) + cos671o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_89
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 90 - ((-18787/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_91 : ((10517321/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos671o2c k) + cos671o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_90
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 91 - ((656749/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_92 : ((9570917/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos671o2c k) + cos671o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_91
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 92 - ((-14786/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_93 : ((10558631/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos671o2c k) + cos671o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_92
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 93 - ((493907/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_94 : ((1946973/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos671o2c k) + cos671o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_93
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 94 - ((-411833/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_95 : ((410609/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos671o2c k) + cos671o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_94
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 95 - ((26523/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_96 : ((10078609/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos671o2c k) + cos671o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_95
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 96 - ((-46629/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_97 : ((9931531/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos671o2c k) + cos671o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_96
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 97 - ((-73489/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_98 : ((10363671/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos671o2c k) + cos671o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_97
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 98 - ((5403/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_99 : ((971059/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos671o2c k) + cos671o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_98
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 99 - ((-652981/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_100 : ((5259553/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos671o2c k) + cos671o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_99
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 100 - ((101077/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_101 : ((4805487/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos671o2c k) + cos671o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_100
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 101 - ((-14188/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_102 : ((2643769/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos671o2c k) + cos671o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_101
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 102 - ((482101/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_103 : ((9584319/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos671o2c k) + cos671o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_102
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 103 - ((-990657/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_104 : ((10583541/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos671o2c k) + cos671o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_103
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 104 - ((499661/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_105 : ((4791979/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos671o2c k) + cos671o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_104
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 105 - ((-999483/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_106 : ((10581363/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos671o2c k) + cos671o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_105
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 106 - ((199501/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_107 : ((9584409/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos671o2c k) + cos671o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_106
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 107 - ((-498427/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_108 : ((5291293/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos671o2c k) + cos671o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_107
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 108 - ((998277/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_109 : ((9582529/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos671o2c k) + cos671o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_108
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 109 - ((-999957/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_110 : ((5290047/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos671o2c k) + cos671o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_109
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 110 - ((199533/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_111 : ((9595043/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos671o2c k) + cos671o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_110
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 111 - ((-984951/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_112 : ((10548389/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos671o2c k) + cos671o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_111
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 112 - ((476723/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_113 : ((4827383/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos671o2c k) + cos671o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_112
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 113 - ((-893523/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_114 : ((10449961/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos671o2c k) + cos671o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_113
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 114 - ((159059/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_115 : ((4899751/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos671o2c k) + cos671o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_114
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 115 - ((-650359/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_116 : ((10253379/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos671o2c k) + cos671o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_115
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 116 - ((453977/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_117 : ((156958/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos671o2c k) + cos671o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_116
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 117 - ((-207967/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_118 : ((996853/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos671o2c k) + cos671o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_117
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 118 - ((-38341/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_119 : ((2069193/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos671o2c k) + cos671o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_118
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 119 - ((75507/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_120 : ((9685609/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos671o2c k) + cos671o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_119
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 120 - ((-20633/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_121 : ((10566761/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos671o2c k) + cos671o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_120
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 121 - ((220313/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_122 : ((957293/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos671o2c k) + cos671o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_121
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 122 - ((-993731/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_123 : ((2632713/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos671o2c k) + cos671o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_122
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 123 - ((479011/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_124 : ((1955231/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos671o2c k) + cos671o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_123
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 124 - ((-754597/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_125 : ((10173059/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos671o2c k) + cos671o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_124
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 125 - ((99251/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_126 : ((2046587/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos671o2c k) + cos671o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_125
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 126 - ((7497/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_127 : ((9710623/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos671o2c k) + cos671o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_126
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 127 - ((-130553/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_128 : ((10582703/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos671o2c k) + cos671o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_127
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 128 - ((43609/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_129 : ((9582793/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos671o2c k) + cos671o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_128
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 129 - ((-99981/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_130 : ((10424393/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos671o2c k) + cos671o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_129
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 130 - ((8417/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_131 : ((10007663/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos671o2c k) + cos671o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_130
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 131 - ((-41663/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_132 : ((9847737/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos671o2c k) + cos671o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_131
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 132 - ((-79913/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_133 : ((2635947/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos671o2c k) + cos671o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_132
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 133 - ((696151/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_134 : ((4779247/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos671o2c k) + cos671o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_133
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 134 - ((-492597/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_135 : ((2089549/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos671o2c k) + cos671o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_134
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 135 - ((889351/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_136 : ((10030451/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos671o2c k) + cos671o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_135
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 136 - ((-208597/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_137 : ((9779721/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos671o2c k) + cos671o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_136
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 137 - ((-25063/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_138 : ((1324487/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos671o2c k) + cos671o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_137
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 138 - ((32651/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_139 : ((9601129/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos671o2c k) + cos671o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_138
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 139 - ((-994667/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_140 : ((5134291/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos671o2c k) + cos671o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_139
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 140 - ((667553/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_141 : ((2572817/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos671o2c k) + cos671o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_140
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 141 - ((11393/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_142 : ((9578471/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos671o2c k) + cos671o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_141
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 142 - ((-712697/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_143 : ((2644581/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos671o2c k) + cos671o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_142
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 143 - ((999953/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_144 : ((9891159/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos671o2c k) + cos671o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_143
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 144 - ((-137413/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_145 : ((9828777/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos671o2c k) + cos671o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_144
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 145 - ((-31141/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_146 : ((2122159/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos671o2c k) + cos671o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_145
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 146 - ((391059/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_147 : ((9626631/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos671o2c k) + cos671o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_146
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 147 - ((-15376/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_148 : ((10127769/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos671o2c k) + cos671o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_147
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 148 - ((250619/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_149 : ((10477389/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos671o2c k) + cos671o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_148
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 149 - ((8743/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_150 : ((9526821/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos671o2c k) + cos671o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_149
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 150 - ((-237617/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_151 : ((2070831/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos671o2c k) + cos671o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_150
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 151 - ((413717/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_152 : ((10306607/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos671o2c k) + cos671o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_151
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 152 - ((-5931/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_153 : ((9526849/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos671o2c k) + cos671o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_152
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 153 - ((-389829/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_154 : ((655501/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos671o2c k) + cos671o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_153
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 154 - ((961267/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_155 : ((2542983/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos671o2c k) + cos671o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_154
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 155 - ((-19749/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_156 : ((9556717/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos671o2c k) + cos671o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_155
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 156 - ((-123023/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_157 : ((1055261/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos671o2c k) + cos671o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_156
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 157 - ((995993/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_158 : ((10099793/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos671o2c k) + cos671o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_157
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 158 - ((-452717/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_159 : ((9572711/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos671o2c k) + cos671o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_158
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 159 - ((-263491/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_160 : ((264309/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos671o2c k) + cos671o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_159
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 160 - ((999749/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_161 : ((5047671/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos671o2c k) + cos671o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_160
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 161 - ((-238459/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_162 : ((9558111/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos671o2c k) + cos671o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_161
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 162 - ((-537131/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_163 : ((10555333/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos671o2c k) + cos671o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_162
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 163 - ((498661/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_164 : ((158726/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos671o2c k) + cos671o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_163
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 164 - ((-396769/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_165 : ((380747/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos671o2c k) + cos671o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_164
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 165 - ((-639689/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_166 : ((10490457/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos671o2c k) + cos671o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_165
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 166 - ((485941/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_167 : ((10285271/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos671o2c k) + cos671o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_166
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 167 - ((-102543/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_168 : ((4741157/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos671o2c k) + cos671o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_167
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 168 - ((-802857/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_169 : ((5177053/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos671o2c k) + cos671o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_168
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 169 - ((217973/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_170 : ((10457013/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos671o2c k) + cos671o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_169
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 170 - ((103007/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_171 : ((9499749/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos671o2c k) + cos671o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_170
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 171 - ((-239291/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_172 : ((10127839/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos671o2c k) + cos671o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_171
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 172 - ((62819/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_173 : ((10622397/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos671o2c k) + cos671o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_172
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 173 - ((247329/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_174 : ((9634211/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos671o2c k) + cos671o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_173
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 174 - ((-494043/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_175 : ((9830171/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos671o2c k) + cos671o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_174
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 175 - ((9803/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_176 : ((10688693/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos671o2c k) + cos671o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_175
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 176 - ((429311/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_177 : ((9925361/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos671o2c k) + cos671o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_176
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 177 - ((-23851/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_178 : ((4775707/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos671o2c k) + cos671o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_177
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 178 - ((-373847/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_179 : ((10548549/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos671o2c k) + cos671o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_178
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 179 - ((199447/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_180 : ((5163209/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos671o2c k) + cos671o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_179
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 180 - ((-222031/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_181 : ((1181809/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos671o2c k) + cos671o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_180
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 181 - ((-435923/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_182 : ((5082191/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos671o2c k) + cos671o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_181
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 182 - ((71001/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_183 : ((2663923/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos671o2c k) + cos671o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_182
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 183 - ((49141/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_184 : ((9688223/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos671o2c k) + cos671o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_183
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 184 - ((-967369/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_185 : ((4839803/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos671o2c k) + cos671o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_184
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 185 - ((-8517/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_186 : ((2663333/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos671o2c k) + cos671o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_185
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 186 - ((486913/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_187 : ((5105783/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos671o2c k) + cos671o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_186
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 187 - ((-220833/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_188 : ((2357843/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos671o2c k) + cos671o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_187
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 188 - ((-390047/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_189 : ((318913/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos671o2c k) + cos671o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_188
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 189 - ((96743/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_190 : ((10672309/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos671o2c k) + cos671o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_189
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 190 - ((467193/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_191 : ((9715621/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos671o2c k) + cos671o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_190
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 191 - ((-239147/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_192 : ((9601187/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos671o2c k) + cos671o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_191
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 192 - ((-57167/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_193 : ((2649859/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos671o2c k) + cos671o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_192
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 193 - ((998349/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_194 : ((5190289/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos671o2c k) + cos671o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_193
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 194 - ((-109379/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_195 : ((1889971/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos671o2c k) + cos671o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_194
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 195 - ((-930623/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_196 : ((9946639/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos671o2c k) + cos671o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_195
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 196 - ((124221/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_197 : ((1073861/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos671o2c k) + cos671o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_196
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 197 - ((792071/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_198 : ((10032009/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos671o2c k) + cos671o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_197
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 198 - ((-706501/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_199 : ((9413381/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos671o2c k) + cos671o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_198
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 199 - ((-19329/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_200 : ((10262669/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos671o2c k) + cos671o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_199
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 200 - ((212347/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_201 : ((5350309/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos671o2c k) + cos671o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_200
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 201 - ((438049/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_202 : ((9764353/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos671o2c k) + cos671o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_201
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 202 - ((-187233/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_203 : ((1898881/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos671o2c k) + cos671o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_202
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 203 - ((-33731/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_204 : ((5237639/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos671o2c k) + cos671o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_203
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 204 - ((980973/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_205 : ((5300217/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos671o2c k) + cos671o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_204
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 205 - ((15657/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_206 : ((9602367/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos671o2c k) + cos671o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_205
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 206 - ((-997967/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_207 : ((9592391/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos671o2c k) + cos671o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_206
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 207 - ((-2469/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_208 : ((2647909/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos671o2c k) + cos671o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_207
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 208 - ((199869/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_209 : ((10517073/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos671o2c k) + cos671o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_208
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 209 - ((-74463/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_210 : ((9522499/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos671o2c k) + cos671o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_209
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 210 - ((-497237/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_211 : ((603141/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos671o2c k) + cos671o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_210
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 211 - ((127857/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_212 : ((212797/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos671o2c k) + cos671o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_211
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 212 - ((494847/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_213 : ((10488609/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos671o2c k) + cos671o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_212
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 213 - ((-151141/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_214 : ((148439/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos671o2c k) + cos671o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_213
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 214 - ((-988413/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_215 : ((241129/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos671o2c k) + cos671o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_214
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 215 - ((36291/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_216 : ((2127279/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos671o2c k) + cos671o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_215
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 216 - ((198267/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_217 : ((10525939/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos671o2c k) + cos671o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_216
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 217 - ((-27589/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_218 : ((381169/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos671o2c k) + cos671o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_217
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 218 - ((-498307/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_219 : ((2394027/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos671o2c k) + cos671o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_218
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 219 - ((46983/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_220 : ((10575997/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos671o2c k) + cos671o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_219
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 220 - ((999989/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_221 : ((2124089/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos671o2c k) + cos671o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_220
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 221 - ((11137/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_222 : ((2406353/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos671o2c k) + cos671o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_221
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 222 - ((-994933/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_223 : ((4731203/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos671o2c k) + cos671o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_222
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 223 - ((-81453/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_224 : ((5217607/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos671o2c k) + cos671o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_223
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 224 - ((243227/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_225 : ((5369919/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos671o2c k) + cos671o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_224
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 225 - ((76181/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_226 : ((9815841/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos671o2c k) + cos671o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_225
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 226 - ((-923897/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_227 : ((9352011/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos671o2c k) + cos671o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_226
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 227 - ((-46373/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_228 : ((10189319/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos671o2c k) + cos671o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_227
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 228 - ((26169/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_229 : ((169041/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos671o2c k) + cos671o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_228
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 229 - ((125881/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_230 : ((10114473/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos671o2c k) + cos671o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_229
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 230 - ((-704051/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_231 : ((1865593/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos671o2c k) + cos671o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_230
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 231 - ((-98301/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_232 : ((2461411/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos671o2c k) + cos671o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_231
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 232 - ((517779/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_233 : ((168126/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos671o2c k) + cos671o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_232
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 233 - ((22863/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_234 : ((5240591/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos671o2c k) + cos671o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_233
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 234 - ((-139391/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_235 : ((9491209/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos671o2c k) + cos671o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_234
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 235 - ((-989873/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_236 : ((9487381/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos671o2c k) + cos671o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_235
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 236 - ((-233/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_237 : ((10475149/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos671o2c k) + cos671o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_236
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 237 - ((246967/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_238 : ((10784013/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos671o2c k) + cos671o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_237
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 238 - ((77241/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_239 : ((123701/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos671o2c k) + cos671o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_238
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 239 - ((-887833/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_240 : ((9292283/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos671o2c k) + cos671o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_239
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 240 - ((-603697/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_241 : ((4985767/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos671o2c k) + cos671o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_240
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 241 - ((679351/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_242 : ((10815851/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos671o2c k) + cos671o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_241
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 242 - ((844417/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_243 : ((2089333/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos671o2c k) + cos671o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_242
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 243 - ((-184543/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_244 : ((236591/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos671o2c k) + cos671o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_243
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 244 - ((-39317/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_245 : ((4724991/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos671o2c k) + cos671o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_244
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 245 - ((-6779/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_246 : ((10426269/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos671o2c k) + cos671o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_245
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 246 - ((976387/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_247 : ((10840753/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos671o2c k) + cos671o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_246
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 247 - ((51823/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_248 : ((10040189/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos671o2c k) + cos671o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_247
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 248 - ((-50029/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_249 : ((1160001/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos671o2c k) + cos671o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_248
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 249 - ((-760081/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_250 : ((4871411/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos671o2c k) + cos671o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_249
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 250 - ((231457/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_251 : ((2677921/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 251, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 251, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 250, cos671o2c k) + cos671o2c 251 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 250) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_250
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 251 - ((484481/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_251).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_252 : ((53493/5000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 252, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 252, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 251, cos671o2c k) + cos671o2c 252 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 251) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_251
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 252 - ((-1623/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_252).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_253 : ((2431157/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 253, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 253, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 252, cos671o2c k) + cos671o2c 253 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 252) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_252
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 253 - ((-60867/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_253).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_254 : ((9265933/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 254, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 254, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 253, cos671o2c k) + cos671o2c 254 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 253) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_253
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 254 - ((-91719/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_254).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_255 : ((10011721/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 255, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 255, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 254, cos671o2c k) + cos671o2c 255 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 254) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_254
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 255 - ((23309/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_255).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_256 : ((1355723/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 256, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 256, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 255, cos671o2c k) + cos671o2c 256 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 255) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_255
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 256 - ((834163/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_256).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_257 : ((10529819/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 257, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 257, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 256, cos671o2c k) + cos671o2c 257 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 256) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_256
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 257 - ((-63173/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_257).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_258 : ((9531149/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 258, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 258, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 257, cos671o2c k) + cos671o2c 258 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 257) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_257
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 258 - ((-99857/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_258).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_259 : ((291043/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 259, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 259, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 258, cos671o2c k) + cos671o2c 259 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 258) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_258
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 259 - ((-217673/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_259).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_260 : ((10192129/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 260, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 260, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 259, cos671o2c k) + cos671o2c 260 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 259) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_259
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 260 - ((878853/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_260).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_261 : ((5447733/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 261, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 261, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 260, cos671o2c k) + cos671o2c 261 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 260) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_260
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 261 - ((703437/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_261).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_262 : ((10413517/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 262, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 262, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 261, cos671o2c k) + cos671o2c 262 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 261) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_261
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 262 - ((-481849/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_262).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_263 : ((4717699/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 263, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 263, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 262, cos671o2c k) + cos671o2c 263 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 262) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_262
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 263 - ((-978019/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_263).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_264 : ((2336981/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 264, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 264, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 263, cos671o2c k) + cos671o2c 264 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 263) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_263
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 264 - ((-43687/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_264).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_265 : ((10272787/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 265, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 265, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 264, cos671o2c k) + cos671o2c 265 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 264) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_264
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 265 - ((924963/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_265).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_266 : ((10914601/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 266, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 266, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 265, cos671o2c k) + cos671o2c 266 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 265) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_265
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 266 - ((320957/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_266).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_267 : ((10381703/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 267, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 267, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 266, cos671o2c k) + cos671o2c 267 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 266) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_266
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 267 - ((-266399/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_267).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_268 : ((470577/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 268, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 268, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 267, cos671o2c k) + cos671o2c 268 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 267) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_267
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 268 - ((-970063/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_268).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_269 : ((9335561/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 269, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 269, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 268, cos671o2c k) + cos671o2c 269 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 268) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_268
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 269 - ((-75879/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_269).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_270 : ((10255803/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 270, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 270, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 269, cos671o2c k) + cos671o2c 270 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 269) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_269
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 270 - ((460171/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_270).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_271 : ((5462153/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 271, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 271, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 270, cos671o2c k) + cos671o2c 271 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 270) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_270
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 271 - ((668603/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_271).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_272 : ((10441813/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 272, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 272, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 271, cos671o2c k) + cos671o2c 272 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 271) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_271
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 272 - ((-482393/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_272).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_273 : ((4727547/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 273, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 273, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 272, cos671o2c k) + cos671o2c 273 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 272) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_272
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 273 - ((-986619/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_273).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_274 : ((2318917/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 274, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 274, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 273, cos671o2c k) + cos671o2c 274 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 273) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_273
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 274 - ((-89663/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_274).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_275 : ((633683/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 275, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 275, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 274, cos671o2c k) + cos671o2c 275 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 274) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_274
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 275 - ((2698/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_275).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_276 : ((5455389/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 276, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 276, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 275, cos671o2c k) + cos671o2c 276 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 275) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_275
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 276 - ((15439/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_276).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_277 : ((10585217/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 277, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 277, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 276, cos671o2c k) + cos671o2c 277 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 276) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_276
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 277 - ((-325461/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_277).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_278 : ((1198197/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 278, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 278, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 277, cos671o2c k) + cos671o2c 278 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 277) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_277
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 278 - ((-999541/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_278).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_279 : ((459967/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 279, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 279, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 278, cos671o2c k) + cos671o2c 279 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 278) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_278
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 279 - ((-48267/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_279).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_280 : ((495967/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 280, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 280, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 279, cos671o2c k) + cos671o2c 280 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 279) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_279
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 280 - ((7201/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_280).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_281 : ((1353567/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 281, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 281, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 280, cos671o2c k) + cos671o2c 281 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 280) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_280
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 281 - ((56831/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_281).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_282 : ((2155643/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 282, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 282, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 281, cos671o2c k) + cos671o2c 282 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 281) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_281
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 282 - ((-50221/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_282).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_283 : ((9833033/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 283, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 283, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 282, cos671o2c k) + cos671o2c 283 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 282) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_282
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 283 - ((-472541/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_283).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_284 : ((9173319/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 284, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 284, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 283, cos671o2c k) + cos671o2c 284 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 283) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_283
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 284 - ((-329807/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_284).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_285 : ((480811/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 285, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 285, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 284, cos671o2c k) + cos671o2c 285 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 284) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_284
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 285 - ((443001/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_285).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_286 : ((10614117/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 286, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 286, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 285, cos671o2c k) + cos671o2c 286 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 285) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_285
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 286 - ((997997/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_286).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_287 : ((10944169/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 287, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 287, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 286, cos671o2c k) + cos671o2c 287 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 286) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_286
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 287 - ((41269/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_287).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_288 : ((10205819/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 288, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 288, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 287, cos671o2c k) + cos671o2c 288 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 287) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_287
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 288 - ((-2953/4000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_288).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_289 : ((9293687/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 289, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 289, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 288, cos671o2c k) + cos671o2c 289 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 288) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_288
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 289 - ((-28501/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_289).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_290 : ((4652147/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 290, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 290, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 289, cos671o2c k) + cos671o2c 290 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 289) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_289
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 290 - ((10707/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_290).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_291 : ((10223219/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 291, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 291, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 290, cos671o2c k) + cos671o2c 291 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 290) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_290
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 291 - ((36761/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_291).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_292 : ((5478843/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 292, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 292, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 291, cos671o2c k) + cos671o2c 292 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 291) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_291
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 292 - ((734567/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_292).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_293 : ((10641141/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 293, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 293, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 292, cos671o2c k) + cos671o2c 293 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 292) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_292
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 293 - ((-63289/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_293).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_294 : ((4823313/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 294, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 294, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 293, cos671o2c k) + cos671o2c 294 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 293) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_293
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 294 - ((-198883/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_294).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_295 : ((9134701/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 295, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 295, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 294, cos671o2c k) + cos671o2c 295 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 294) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_294
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 295 - ((-20473/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_295).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_296 : ((242441/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 296, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 296, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 295, cos671o2c k) + cos671o2c 296 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 295) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_295
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 296 - ((563039/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_296).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_297 : ((10684957/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 297, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 297, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 296, cos671o2c k) + cos671o2c 297 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 296) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_296
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 297 - ((987417/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_297).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_298 : ((10965321/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 298, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 298, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 297, cos671o2c k) + cos671o2c 298 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 297) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_297
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 298 - ((17529/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_298).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_299 : ((10220791/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 299, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 299, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 298, cos671o2c k) + cos671o2c 299 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 298) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_298
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 299 - ((-74443/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_299).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_300 : ((1859087/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 300, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 300, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 299, cos671o2c k) + cos671o2c 300 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 299) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_299
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 300 - ((-115657/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_300).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_301 : ((2307537/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 301, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 301, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 300, cos671o2c k) + cos671o2c 301 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 300) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_300
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 301 - ((-65187/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_301).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_302 : ((10096251/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 302, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 302, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 301, cos671o2c k) + cos671o2c 302 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 301) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_301
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 302 - ((866203/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_302).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_303 : ((683087/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 303, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 303, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 302, cos671o2c k) + cos671o2c 303 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 302) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_302
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 303 - ((833241/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_303).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_304 : ((168892/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 304, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 304, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 303, cos671o2c k) + cos671o2c 304 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 303) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_303
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 304 - ((-30051/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_304).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_305 : ((9869109/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 305, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 305, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 304, cos671o2c k) + cos671o2c 305 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 304) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_304
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 305 - ((-939879/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_305).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_306 : ((57107/6250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 306, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 306, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 305, cos671o2c k) + cos671o2c 306 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 305) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_305
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 306 - ((-731889/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_306).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_307 : ((1881427/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 307, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 307, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 306, cos671o2c k) + cos671o2c 307 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 306) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_306
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 307 - ((54023/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_307).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_308 : ((10385843/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 308, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 308, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 307, cos671o2c k) + cos671o2c 308 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 307) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_307
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 308 - ((122351/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_308).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_309 : ((11021903/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 309, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 309, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 308, cos671o2c k) + cos671o2c 309 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 308) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_308
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 309 - ((1988/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_309).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_310 : ((5318733/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 310, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 310, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 309, cos671o2c k) + cos671o2c 310 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 309) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_309
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 310 - ((-384337/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_310).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_311 : ((2410487/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 311, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 311, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 310, cos671o2c k) + cos671o2c 311 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 310) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_310
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 311 - ((-497709/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_311).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_312 : ((9085873/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 312, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 312, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 311, cos671o2c k) + cos671o2c 312 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 311) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_311
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 312 - ((-22239/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_312).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_313 : ((9551153/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 313, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 313, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 312, cos671o2c k) + cos671o2c 313 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 312) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_312
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 313 - ((23269/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_313).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_314 : ((2637729/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 314, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 314, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 313, cos671o2c k) + cos671o2c 314 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 313) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_313
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 314 - ((999863/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_314).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_315 : ((11048183/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 315, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 315, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 314, cos671o2c k) + cos671o2c 315 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 314) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_314
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 315 - ((497367/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_315).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_316 : ((5265757/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 316, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 316, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 315, cos671o2c k) + cos671o2c 316 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 315) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_315
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 316 - ((-516569/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_316).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_317 : ((1191491/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 317, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 317, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 316, cos671o2c k) + cos671o2c 317 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 316) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_316
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 317 - ((-499743/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_317).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_318 : ((9068231/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 318, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 318, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 317, cos671o2c k) + cos671o2c 318 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 317) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_317
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 318 - ((-463597/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_318).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_319 : ((9608901/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 319, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 319, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 318, cos671o2c k) + cos671o2c 319 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 318) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_318
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 319 - ((54077/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_319).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_320 : ((10607521/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 320, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 320, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 319, cos671o2c k) + cos671o2c 320 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 319) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_319
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 320 - ((3121/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_320).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_321 : ((2212661/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 321, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 321, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 320, cos671o2c k) + cos671o2c 321 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 320) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_320
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 321 - ((113971/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_321).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_322 : ((5261713/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 322, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 322, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 321, cos671o2c k) + cos671o2c 322 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 321) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_321
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 322 - ((-539779/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_322).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_323 : ((4762057/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 323, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 323, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 322, cos671o2c k) + cos671o2c 323 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 322) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_322
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 323 - ((-249803/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_323).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_324 : ((452493/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 324, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 324, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 323, cos671o2c k) + cos671o2c 324 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 323) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_323
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 324 - ((-237077/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_324).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_325 : ((2390947/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 325, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 325, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 324, cos671o2c k) + cos671o2c 325 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 324) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_324
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 325 - ((128507/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_325).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_326 : ((1320461/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 326, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 326, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 325, cos671o2c k) + cos671o2c 326 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 325) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_325
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 326 - ((1 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_326).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_327 : ((11080659/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 327, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 327, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 326, cos671o2c k) + cos671o2c 327 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 326) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_326
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 327 - ((517071/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_327).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_328 : ((663617/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 328, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 328, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 327, cos671o2c k) + cos671o2c 328 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 327) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_327
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 328 - ((-462687/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_328).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_329 : ((2405029/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 329, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 329, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 328, cos671o2c k) + cos671o2c 329 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 328) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_328
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 329 - ((-124707/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_329).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_330 : ((4519057/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 330, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 330, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 329, cos671o2c k) + cos671o2c 330 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 329) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_329
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 330 - ((-290951/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_330).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_331 : ((147218/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 331, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 331, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 330, cos671o2c k) + cos671o2c 331 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 330) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_330
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 331 - ((191969/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_331).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_332 : ((416333/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 332, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 332, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 331, cos671o2c k) + cos671o2c 332 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 331) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_331
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 332 - ((986473/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_332).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_333 : ((2214489/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 333, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 333, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 332, cos671o2c k) + cos671o2c 333 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 332) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_332
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 333 - ((33211/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_333).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_334 : ((1349553/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 334, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 334, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 333, cos671o2c k) + cos671o2c 334 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 333) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_333
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 334 - ((-275921/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_334).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_335 : ((4918789/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 335, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 335, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 334, cos671o2c k) + cos671o2c 335 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 334) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_334
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 335 - ((-479373/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_335).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_336 : ((454013/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 336, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 336, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 335, cos671o2c k) + cos671o2c 336 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 335) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_335
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 336 - ((-378609/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_336).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_337 : ((4608859/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 337, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 337, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 336, cos671o2c k) + cos671o2c 337 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 336) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_336
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 337 - ((68779/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_337).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_338 : ((5061451/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 338, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 338, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 337, cos671o2c k) + cos671o2c 338 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 337) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_337
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 338 - ((226321/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_338).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_339 : ((10974059/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 339, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 339, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 338, cos671o2c k) + cos671o2c 339 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 338) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_338
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 339 - ((851257/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_339).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_340 : ((2751029/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 340, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 340, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 339, cos671o2c k) + cos671o2c 340 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 339) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_339
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 340 - ((30157/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_340).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_341 : ((1273453/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 341, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 341, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 340, cos671o2c k) + cos671o2c 341 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 340) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_340
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 341 - ((-102049/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_341).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_342 : ((4627019/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 342, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 342, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 341, cos671o2c k) + cos671o2c 342 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 341) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_341
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 342 - ((-466743/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_342).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_343 : ((2257841/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 343, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 343, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 342, cos671o2c k) + cos671o2c 343 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 342) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_342
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 343 - ((-111287/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_343).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_344 : ((194291/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 344, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 344, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 343, cos671o2c k) + cos671o2c 344 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 343) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_343
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 344 - ((341643/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_344).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_345 : ((1337801/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 345, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 345, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 344, cos671o2c k) + cos671o2c 345 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 344) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_344
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 345 - ((493979/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_345).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_346 : ((2226447/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 346, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 346, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 345, cos671o2c k) + cos671o2c 346 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 345) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_345
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 346 - ((429927/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_346).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_347 : ((425277/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 347, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 347, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 346, cos671o2c k) + cos671o2c 347 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 346) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_346
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 347 - ((-50021/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_347).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_348 : ((9635143/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 348, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 348, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 347, cos671o2c k) + cos671o2c 348 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 347) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_347
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 348 - ((-498341/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_348).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_349 : ((8998841/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 349, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 349, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 348, cos671o2c k) + cos671o2c 349 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 348) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_348
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 349 - ((-318101/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_349).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_350 : ((4632913/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 350, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 350, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 349, cos671o2c k) + cos671o2c 350 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 349) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_349
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 350 - ((53417/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_350).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_351 : ((2551851/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 351, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 351, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 350, cos671o2c k) + cos671o2c 351 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 350) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_350
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 351 - ((470839/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_351).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_352 : ((2756559/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 352, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 352, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 351, cos671o2c k) + cos671o2c 352 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 351) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_351
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 352 - ((204733/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_352).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_353 : ((11033903/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 353, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 353, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 352, cos671o2c k) + cos671o2c 353 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 352) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_352
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 353 - ((7767/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_353).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_354 : ((5112731/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 354, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 354, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 353, cos671o2c k) + cos671o2c 354 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 353) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_353
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 354 - ((-808341/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_354).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_355 : ((231879/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 355, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 355, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 354, cos671o2c k) + cos671o2c 355 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 354) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_354
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 355 - ((-475101/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_355).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_356 : ((2242471/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 356, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 356, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 355, cos671o2c k) + cos671o2c 356 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 355) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_355
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 356 - ((-38147/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_356).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_357 : ((9559699/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 357, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 357, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 356, cos671o2c k) + cos671o2c 357 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 356) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_356
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 357 - ((117983/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_357).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_358 : ((5279799/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 358, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 358, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 357, cos671o2c k) + cos671o2c 358 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 357) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_357
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 358 - ((999999/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_358).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_359 : ((11153749/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 359, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 359, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 358, cos671o2c k) + cos671o2c 359 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 358) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_358
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 359 - ((594251/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_359).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_360 : ((10861067/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 360, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 360, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 359, cos671o2c k) + cos671o2c 360 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 359) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_359
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 360 - ((-146291/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_360).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_361 : ((9919293/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 361, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 361, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 360, cos671o2c k) + cos671o2c 361 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 360) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_360
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 361 - ((-470837/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_361).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_362 : ((9085407/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 362, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 362, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 361, cos671o2c k) + cos671o2c 362 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 361) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_361
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 362 - ((-416893/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_362).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_363 : ((2256231/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 363, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 363, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 362, cos671o2c k) + cos671o2c 363 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 362) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_362
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 363 - ((-60383/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_363).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_364 : ((4892161/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 364, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 364, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 363, cos671o2c k) + cos671o2c 364 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 363) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_363
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 364 - ((379749/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_364).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_365 : ((5380897/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 365, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 365, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 364, cos671o2c k) + cos671o2c 365 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 364) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_364
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 365 - ((244393/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_365).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_366 : ((1398531/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 366, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 366, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 365, cos671o2c k) + cos671o2c 366 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 365) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_365
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 366 - ((213277/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_366).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_367 : ((10731047/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 367, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 367, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 366, cos671o2c k) + cos671o2c 367 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 366) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_366
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 367 - ((-457101/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_367).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_368 : ((9747669/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 368, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 368, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 367, cos671o2c k) + cos671o2c 368 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 367) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_367
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 368 - ((-491639/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_368).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_369 : ((1800121/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 369, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 369, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 368, cos671o2c k) + cos671o2c 369 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 368) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_368
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 369 - ((-186741/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_369).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_370 : ((9064973/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 370, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 370, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 369, cos671o2c k) + cos671o2c 370 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 369) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_369
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 370 - ((16117/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_370).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_371 : ((4944887/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 371, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 371, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 370, cos671o2c k) + cos671o2c 371 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 370) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_370
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 371 - ((824901/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_371).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_372 : ((10844319/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 372, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 372, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 371, cos671o2c k) + cos671o2c 372 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 371) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_371
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 372 - ((190929/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_372).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_373 : ((11203767/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 373, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 373, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 372, cos671o2c k) + cos671o2c 373 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 372) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_372
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 373 - ((89887/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_373).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_374 : ((2139549/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 374, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 374, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 373, cos671o2c k) + cos671o2c 374 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 373) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_373
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 374 - ((-252961/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_374).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_375 : ((9708061/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 375, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 375, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 374, cos671o2c k) + cos671o2c 375 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 374) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_374
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 375 - ((-61849/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_375).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_376 : ((4487799/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 376, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 376, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 375, cos671o2c k) + cos671o2c 376 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 375) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_375
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 376 - ((-732363/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_376).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_377 : ((1130593/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 377, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 377, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 376, cos671o2c k) + cos671o2c 377 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 376) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_376
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 377 - ((34623/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_377).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_378 : ((9862711/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 378, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 378, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 377, cos671o2c k) + cos671o2c 378 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 377) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_377
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 378 - ((818067/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_378).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_379 : ((10825397/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 379, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 379, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 378, cos671o2c k) + cos671o2c 379 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 378) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_378
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 379 - ((481393/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_379).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_380 : ((11226733/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 380, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 380, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 379, cos671o2c k) + cos671o2c 380 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 379) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_379
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 380 - ((100359/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_380).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_381 : ((10774957/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 381, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 381, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 380, cos671o2c k) + cos671o2c 381 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 380) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_380
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 381 - ((-112919/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_381).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_382 : ((4899777/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 382, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 382, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 381, cos671o2c k) + cos671o2c 382 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 381) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_381
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 382 - ((-975303/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_382).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_383 : ((1801207/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 383, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 383, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 382, cos671o2c k) + cos671o2c 383 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 382) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_382
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 383 - ((-793419/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_383).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_384 : ((8964391/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 384, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 384, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 383, cos671o2c k) + cos671o2c 384 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 383) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_383
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 384 - ((-5193/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_384).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_385 : ((1940581/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 385, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 385, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 384, cos671o2c k) + cos671o2c 385 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 384) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_384
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 385 - ((369307/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_385).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_386 : ((5347151/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 386, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 386, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 385, cos671o2c k) + cos671o2c 386 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 385) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_385
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 386 - ((991497/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_386).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_387 : ((1123573/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 387, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 387, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 386, cos671o2c k) + cos671o2c 387 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 386) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_386
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 387 - ((67691/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_387).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_388 : ((5473129/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 388, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 388, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 387, cos671o2c k) + cos671o2c 388 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 387) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_387
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 388 - ((-72343/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_388).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_389 : ((5015249/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 389, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 389, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 388, cos671o2c k) + cos671o2c 389 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 388) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_388
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 389 - ((-45783/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_389).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_390 : ((9128959/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 390, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 390, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 389, cos671o2c k) + cos671o2c 390 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 389) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_389
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 390 - ((-901439/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_390).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_391 : ((8867979/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 391, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 391, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 390, cos671o2c k) + cos671o2c 391 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 390) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_390
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 391 - ((-3261/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_391).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_392 : ((4713379/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 392, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 392, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 391, cos671o2c k) + cos671o2c 392 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 391) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_391
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 392 - ((558879/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_392).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_393 : ((5209553/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 393, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 393, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 392, cos671o2c k) + cos671o2c 393 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 392) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_392
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 393 - ((15507/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_393).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_394 : ((11164427/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 394, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 394, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 393, cos671o2c k) + cos671o2c 394 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 393) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_393
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 394 - ((745421/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_394).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_395 : ((11155067/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 395, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 395, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 394, cos671o2c k) + cos671o2c 395 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 394) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_394
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 395 - ((-463/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_395).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_396 : ((10398711/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 396, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 396, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 395, cos671o2c k) + cos671o2c 396 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 395) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_395
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 396 - ((-23633/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_396).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_397 : ((940743/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 397, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 397, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 396, cos671o2c k) + cos671o2c 397 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 396) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_396
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 397 - ((-991181/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_397).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_398 : ((8847783/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 398, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 398, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 397, cos671o2c k) + cos671o2c 398 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 397) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_397
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 398 - ((-559547/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_398).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_399 : ((9093211/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 399, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 399, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 398, cos671o2c k) + cos671o2c 399 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 398) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_398
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 399 - ((30691/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_399).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_400 : ((1247343/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 400, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 400, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 399, cos671o2c k) + cos671o2c 400 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 399) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_399
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 400 - ((885633/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_400).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_401 : ((10916371/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 401, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 401, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 400, cos671o2c k) + cos671o2c 401 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 400) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_400
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 401 - ((937727/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_401).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_402 : ((11287593/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 402, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 402, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 401, cos671o2c k) + cos671o2c 402 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 401) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_401
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 402 - ((185661/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_402).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_403 : ((5424861/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 403, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 403, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 402, cos671o2c k) + cos671o2c 403 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 402) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_402
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 403 - ((-437771/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_403).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_404 : ((9890301/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 404, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 404, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 403, cos671o2c k) + cos671o2c 404 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 403) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_403
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 404 - ((-959321/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_404).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_405 : ((9034149/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 405, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 405, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 404, cos671o2c k) + cos671o2c 405 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 404) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_404
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 405 - ((-214013/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_405).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_406 : ((4417589/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 406, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 406, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 405, cos671o2c k) + cos671o2c 406 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 405) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_405
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 406 - ((-198871/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_406).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_407 : ((2355069/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 407, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 407, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 406, cos671o2c k) + cos671o2c 407 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 406) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_406
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 407 - ((292599/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_407).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_408 : ((104127/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 408, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 408, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 407, cos671o2c k) + cos671o2c 408 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 407) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_407
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 408 - ((248131/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_408).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_409 : ((11178119/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 409, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 409, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 408, cos671o2c k) + cos671o2c 409 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 408) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_408
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 409 - ((765519/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_409).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_410 : ((11230551/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 410, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 410, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 409, cos671o2c k) + cos671o2c 410 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 409) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_409
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 410 - ((13133/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_410).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_411 : ((10538091/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 411, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 411, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 410, cos671o2c k) + cos671o2c 411 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 410) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_410
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 411 - ((-17309/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_411).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_412 : ((4769017/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 412, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 412, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 411, cos671o2c k) + cos671o2c 412 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 411) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_411
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 412 - ((-999957/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_412).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_413 : ((8857599/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 413, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 413, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 412, cos671o2c k) + cos671o2c 413 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 412) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_412
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 413 - ((-136067/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_413).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_414 : ((8920611/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 414, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 414, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 413, cos671o2c k) + cos671o2c 414 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 413) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_413
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 414 - ((7889/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_414).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_415 : ((4843251/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 415, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 415, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 414, cos671o2c k) + cos671o2c 415 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 414) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_414
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 415 - ((765991/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_415).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_416 : ((5340221/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 416, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 416, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 415, cos671o2c k) + cos671o2c 416 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 415) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_415
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 416 - ((24851/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_416).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_417 : ((2822579/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 417, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 417, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 416, cos671o2c k) + cos671o2c 417 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 416) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_416
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 417 - ((304987/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_417).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_418 : ((1114319/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 418, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 418, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 417, cos671o2c k) + cos671o2c 418 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 417) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_417
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 418 - ((-73513/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_418).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_419 : ((5165059/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 419, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 419, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 418, cos671o2c k) + cos671o2c 419 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 418) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_418
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 419 - ((-203243/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_419).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_420 : ((1869171/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 420, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 420, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 419, cos671o2c k) + cos671o2c 420 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 419) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_419
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 420 - ((-984163/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_420).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_421 : ((1098183/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 421, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 421, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 420, cos671o2c k) + cos671o2c 421 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 420) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_420
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 421 - ((-560291/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_421).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_422 : ((4492623/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 422, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 422, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 421, cos671o2c k) + cos671o2c 422 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 421) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_421
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 422 - ((99941/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_422).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_423 : ((9824067/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 423, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 423, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 422, cos671o2c k) + cos671o2c 423 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 422) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_422
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 423 - ((838921/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_423).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_424 : ((432023/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 424, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 424, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 423, cos671o2c k) + cos671o2c 424 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 423) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_423
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 424 - ((30519/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_424).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_425 : ((11334827/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 425, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 425, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 424, cos671o2c k) + cos671o2c 425 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 424) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_424
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 425 - ((33397/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_425).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_426 : ((11111863/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 426, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 426, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 425, cos671o2c k) + cos671o2c 426 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 425) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_425
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 426 - ((-13929/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_426).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_427 : ((2566047/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 427, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 427, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 426, cos671o2c k) + cos671o2c 427 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 426) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_426
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 427 - ((-33903/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_427).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_428 : ((290293/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 428, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 428, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 427, cos671o2c k) + cos671o2c 428 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 427) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_427
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 428 - ((-121839/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_428).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_429 : ((8756027/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 429, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 429, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 428, cos671o2c k) + cos671o2c 429 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 428) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_428
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 429 - ((-533249/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_429).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_430 : ((280403/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 430, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 430, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 429, cos671o2c k) + cos671o2c 430 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 429) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_429
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 430 - ((216969/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_430).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_431 : ((9813189/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 431, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 431, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 430, cos671o2c k) + cos671o2c 431 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 430) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_430
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 431 - ((840393/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_431).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_432 : ((2698051/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 432, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 432, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 431, cos671o2c k) + cos671o2c 432 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 431) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_431
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 432 - ((195823/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_432).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_433 : ((11348731/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 433, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 433, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 432, cos671o2c k) + cos671o2c 433 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 432) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_432
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 433 - ((556627/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_433).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_434 : ((223321/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 434, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 434, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 433, cos671o2c k) + cos671o2c 434 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 433) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_433
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 434 - ((-182581/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_434).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_435 : ((2069839/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 435, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 435, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 434, cos671o2c k) + cos671o2c 435 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 434) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_434
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 435 - ((-163351/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_435).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_436 : ((585071/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 436, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 436, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 435, cos671o2c k) + cos671o2c 436 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 435) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_435
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 436 - ((-987959/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_436).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_437 : ((1751671/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 437, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 437, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 436, cos671o2c k) + cos671o2c 437 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 436) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_436
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 437 - ((-602681/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_437).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_438 : ((2219499/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 438, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 438, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 437, cos671o2c k) + cos671o2c 438 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 437) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_437
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 438 - ((119741/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_438).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_439 : ((4825949/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 439, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 439, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 438, cos671o2c k) + cos671o2c 439 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 438) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_438
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 439 - ((387001/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_439).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_440 : ((10648781/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 440, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 440, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 439, cos671o2c k) + cos671o2c 440 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 439) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_439
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 440 - ((996983/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_440).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_441 : ((1414581/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 441, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 441, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 440, cos671o2c k) + cos671o2c 441 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 440) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_440
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 441 - ((667967/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_441).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_442 : ((5644059/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 442, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 442, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 441, cos671o2c k) + cos671o2c 442 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 441) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_441
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 442 - ((-2843/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_442).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_443 : ((10580041/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 443, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 443, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 442, cos671o2c k) + cos671o2c 443 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 442) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_442
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 443 - ((-707977/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_443).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_444 : ((2395081/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 444, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 444, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 443, cos671o2c k) + cos671o2c 444 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 443) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_443
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 444 - ((-999617/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_444).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_445 : ((4416557/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 445, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 445, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 444, cos671o2c k) + cos671o2c 445 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 444) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_444
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 445 - ((-74711/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_445).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_446 : ((2185633/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 446, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 446, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 445, cos671o2c k) + cos671o2c 446 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 445) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_445
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 446 - ((-45241/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_446).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_447 : ((2339041/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 447, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 447, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 446, cos671o2c k) + cos671o2c 447 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 446) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_446
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 447 - ((153433/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_447).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_448 : ((10343247/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 448, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 448, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 447, cos671o2c k) + cos671o2c 448 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 447) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_447
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 448 - ((987183/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_448).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_449 : ((5587667/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 449, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 449, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 448, cos671o2c k) + cos671o2c 449 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 448) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_448
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 449 - ((832187/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_449).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_450 : ((2281937/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 450, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 450, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 449, cos671o2c k) + cos671o2c 450 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 449) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_449
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 450 - ((234451/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_450).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_451 : ((2730769/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 451, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 451, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 450, cos671o2c k) + cos671o2c 451 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 450) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_450
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 451 - ((-486509/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_451).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_452 : ((2493407/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 452, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 452, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 451, cos671o2c k) + cos671o2c 452 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 451) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_451
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 452 - ((-237337/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_452).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_453 : ((453059/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 453, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 453, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 452, cos671o2c k) + cos671o2c 453 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 452) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_452
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 453 - ((-228087/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_453).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_454 : ((10829/1250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 454, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 454, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 453, cos671o2c k) + cos671o2c 454 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 453) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_453
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 454 - ((-9947/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_454).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_455 : ((8986193/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 455, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 455, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 454, cos671o2c k) + cos671o2c 455 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 454) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_454
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 455 - ((323093/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_455).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_456 : ((9861149/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 456, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 456, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 455, cos671o2c k) + cos671o2c 456 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 455) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_455
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 456 - ((54691/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_456).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_457 : ((10834791/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 457, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 457, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 456, cos671o2c k) + cos671o2c 457 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 456) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_456
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 457 - ((486871/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_457).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_458 : ((11405747/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 458, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 458, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 457, cos671o2c k) + cos671o2c 458 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 457) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_457
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 458 - ((35691/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_458).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_459 : ((11281997/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 459, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 459, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 458, cos671o2c k) + cos671o2c 459 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 458) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_458
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 459 - ((-2473/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_459).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_460 : ((10527929/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 460, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 460, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 459, cos671o2c k) + cos671o2c 460 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 459) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_459
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 460 - ((-47123/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_460).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_461 : ((9527899/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 461, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 461, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 460, cos671o2c k) + cos671o2c 461 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 460) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_460
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 461 - ((-99993/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_461).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_462 : ((1757707/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 462, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 462, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 461, cos671o2c k) + cos671o2c 462 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 461) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_461
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 462 - ((-11551/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_462).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_463 : ((8682077/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 463, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 463, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 462, cos671o2c k) + cos671o2c 463 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 462) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_462
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 463 - ((-53179/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_463).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_464 : ((4630399/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 464, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 464, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 463, cos671o2c k) + cos671o2c 464 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 463) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_463
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 464 - ((578821/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_464).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_465 : ((5117043/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 465, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 465, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 464, cos671o2c k) + cos671o2c 465 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 464) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_464
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 465 - ((243347/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_465).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_466 : ((1389569/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 466, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 466, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 465, cos671o2c k) + cos671o2c 466 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 465) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_465
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 466 - ((441283/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_466).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_467 : ((11470703/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 467, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 467, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 466, cos671o2c k) + cos671o2c 467 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 466) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_466
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 467 - ((354251/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_467).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_468 : ((2780631/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 468, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 468, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 467, cos671o2c k) + cos671o2c 468 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 467) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_467
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 468 - ((-348079/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_468).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_469 : ((2048887/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 469, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 469, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 468, cos671o2c k) + cos671o2c 469 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 468) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_468
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 469 - ((-877989/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_469).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_470 : ((9267451/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 470, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 470, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 469, cos671o2c k) + cos671o2c 470 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 469) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_469
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 470 - ((-244221/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_470).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_471 : ((8668317/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 471, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 471, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 470, cos671o2c k) + cos671o2c 471 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 470) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_470
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 471 - ((-299517/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_471).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_472 : ((873743/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 472, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 472, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 471, cos671o2c k) + cos671o2c 472 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 471) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_471
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 472 - ((69213/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_472).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_473 : ((4720063/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 473, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 473, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 472, cos671o2c k) + cos671o2c 473 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 472) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_472
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 473 - ((175699/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_473).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_474 : ((652287/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 474, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 474, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 473, cos671o2c k) + cos671o2c 474 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 473) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_473
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 474 - ((498283/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_474).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_475 : ((11247943/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 475, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 475, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 474, cos671o2c k) + cos671o2c 475 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 474) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_474
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 475 - ((811451/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_475).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_476 : ((2871647/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 476, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 476, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 475, cos671o2c k) + cos671o2c 476 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 475) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_475
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 476 - ((47749/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_476).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_477 : ((1379981/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 477, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 477, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 476, cos671o2c k) + cos671o2c 477 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 476) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_476
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 477 - ((-5583/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_477).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_478 : ((5060353/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 478, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 478, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 477, cos671o2c k) + cos671o2c 478 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 477) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_477
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 478 - ((-459521/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_478).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_479 : ((1145511/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 479, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 479, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 478, cos671o2c k) + cos671o2c 479 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 478) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_478
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 479 - ((-478259/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_479).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_480 : ((2155017/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 480, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 480, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 479, cos671o2c k) + cos671o2c 480 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 479) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_479
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 480 - ((-6799/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_480).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_481 : ((1748553/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 481, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 481, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 480, cos671o2c k) + cos671o2c 481 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 480) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_480
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 481 - ((122797/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_481).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_482 : ((9473747/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 482, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 482, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 481, cos671o2c k) + cos671o2c 482 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 481) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_481
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 482 - ((365541/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_482).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_483 : ((1309013/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 483, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 483, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 482, cos671o2c k) + cos671o2c 483 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 482) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_482
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 483 - ((998457/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_483).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_484 : ((2255017/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 484, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 484, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 483, cos671o2c k) + cos671o2c 484 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 483) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_483
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 484 - ((803081/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_484).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_485 : ((1439087/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 485, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 485, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 484, cos671o2c k) + cos671o2c 485 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 484) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_484
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 485 - ((237711/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_485).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_486 : ((11076681/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 486, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 486, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 485, cos671o2c k) + cos671o2c 486 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 485) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_485
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 486 - ((-87183/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_486).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_487 : ((5083833/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 487, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 487, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 486, cos671o2c k) + cos671o2c 487 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 486) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_486
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 487 - ((-181783/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_487).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_488 : ((9200687/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 488, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 488, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 487, cos671o2c k) + cos671o2c 488 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 487) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_487
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 488 - ((-966879/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_488).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_489 : ((8614729/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 489, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 489, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 488, cos671o2c k) + cos671o2c 489 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 488) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_488
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 489 - ((-292929/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_489).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_490 : ((8674049/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 490, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 490, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 489, cos671o2c k) + cos671o2c 490 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 489) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_489
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 490 - ((2971/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_490).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_491 : ((9350797/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 491, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 491, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 490, cos671o2c k) + cos671o2c 491 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 490) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_490
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 491 - ((42303/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_491).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_492 : ((2585061/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 492, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 492, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 491, cos671o2c k) + cos671o2c 492 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 491) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_491
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 492 - ((989547/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_492).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_493 : ((2239931/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 493, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 493, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 492, cos671o2c k) + cos671o2c 493 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 492) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_492
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 493 - ((859511/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_493).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_494 : ((2309327/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 494, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 494, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 493, cos671o2c k) + cos671o2c 494 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 493) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_493
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 494 - ((8677/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_494).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_495 : ((5614091/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 495, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 495, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 494, cos671o2c k) + cos671o2c 495 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 494) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_494
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 495 - ((-318353/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_495).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_496 : ((5193009/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 496, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 496, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 495, cos671o2c k) + cos671o2c 496 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 495) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_495
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 496 - ((-52629/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_496).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_497 : ((4695767/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 497, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 497, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 496, cos671o2c k) + cos671o2c 497 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 496) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_496
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 497 - ((-62149/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_497).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_498 : ((8680793/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 498, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 498, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 497, cos671o2c k) + cos671o2c 498 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 497) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_497
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 498 - ((-710641/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_498).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_499 : ((4281783/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 499, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 499, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 498, cos671o2c k) + cos671o2c 499 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 498) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_498
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 499 - ((-117127/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_499).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum671o2_500 : ((9089793/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 500, cos671o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 500, cos671o2c k)
      = (∑ k ∈ Finset.Icc 11 499, cos671o2c k) + cos671o2c 500 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 499) (by norm_num) cos671o2c
    simpa using h
  have hprev := psum671o2_499
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos671o2c 500 - ((526327/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos671o2_br_500).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 16384 in
theorem psum671o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 500 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos671o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum671o2_11
  · exact le_trans (by norm_num) psum671o2_12
  · exact le_trans (by norm_num) psum671o2_13
  · exact le_trans (by norm_num) psum671o2_14
  · exact le_trans (by norm_num) psum671o2_15
  · exact le_trans (by norm_num) psum671o2_16
  · exact le_trans (by norm_num) psum671o2_17
  · exact le_trans (by norm_num) psum671o2_18
  · exact le_trans (by norm_num) psum671o2_19
  · exact le_trans (by norm_num) psum671o2_20
  · exact le_trans (by norm_num) psum671o2_21
  · exact le_trans (by norm_num) psum671o2_22
  · exact le_trans (by norm_num) psum671o2_23
  · exact le_trans (by norm_num) psum671o2_24
  · exact le_trans (by norm_num) psum671o2_25
  · exact le_trans (by norm_num) psum671o2_26
  · exact le_trans (by norm_num) psum671o2_27
  · exact le_trans (by norm_num) psum671o2_28
  · exact le_trans (by norm_num) psum671o2_29
  · exact le_trans (by norm_num) psum671o2_30
  · exact le_trans (by norm_num) psum671o2_31
  · exact le_trans (by norm_num) psum671o2_32
  · exact le_trans (by norm_num) psum671o2_33
  · exact le_trans (by norm_num) psum671o2_34
  · exact le_trans (by norm_num) psum671o2_35
  · exact le_trans (by norm_num) psum671o2_36
  · exact le_trans (by norm_num) psum671o2_37
  · exact le_trans (by norm_num) psum671o2_38
  · exact le_trans (by norm_num) psum671o2_39
  · exact le_trans (by norm_num) psum671o2_40
  · exact le_trans (by norm_num) psum671o2_41
  · exact le_trans (by norm_num) psum671o2_42
  · exact le_trans (by norm_num) psum671o2_43
  · exact le_trans (by norm_num) psum671o2_44
  · exact le_trans (by norm_num) psum671o2_45
  · exact le_trans (by norm_num) psum671o2_46
  · exact le_trans (by norm_num) psum671o2_47
  · exact le_trans (by norm_num) psum671o2_48
  · exact le_trans (by norm_num) psum671o2_49
  · exact le_trans (by norm_num) psum671o2_50
  · exact le_trans (by norm_num) psum671o2_51
  · exact le_trans (by norm_num) psum671o2_52
  · exact le_trans (by norm_num) psum671o2_53
  · exact le_trans (by norm_num) psum671o2_54
  · exact le_trans (by norm_num) psum671o2_55
  · exact le_trans (by norm_num) psum671o2_56
  · exact le_trans (by norm_num) psum671o2_57
  · exact le_trans (by norm_num) psum671o2_58
  · exact le_trans (by norm_num) psum671o2_59
  · exact le_trans (by norm_num) psum671o2_60
  · exact le_trans (by norm_num) psum671o2_61
  · exact le_trans (by norm_num) psum671o2_62
  · exact le_trans (by norm_num) psum671o2_63
  · exact le_trans (by norm_num) psum671o2_64
  · exact le_trans (by norm_num) psum671o2_65
  · exact le_trans (by norm_num) psum671o2_66
  · exact le_trans (by norm_num) psum671o2_67
  · exact le_trans (by norm_num) psum671o2_68
  · exact le_trans (by norm_num) psum671o2_69
  · exact le_trans (by norm_num) psum671o2_70
  · exact le_trans (by norm_num) psum671o2_71
  · exact le_trans (by norm_num) psum671o2_72
  · exact le_trans (by norm_num) psum671o2_73
  · exact le_trans (by norm_num) psum671o2_74
  · exact le_trans (by norm_num) psum671o2_75
  · exact le_trans (by norm_num) psum671o2_76
  · exact le_trans (by norm_num) psum671o2_77
  · exact le_trans (by norm_num) psum671o2_78
  · exact le_trans (by norm_num) psum671o2_79
  · exact le_trans (by norm_num) psum671o2_80
  · exact le_trans (by norm_num) psum671o2_81
  · exact le_trans (by norm_num) psum671o2_82
  · exact le_trans (by norm_num) psum671o2_83
  · exact le_trans (by norm_num) psum671o2_84
  · exact le_trans (by norm_num) psum671o2_85
  · exact le_trans (by norm_num) psum671o2_86
  · exact le_trans (by norm_num) psum671o2_87
  · exact le_trans (by norm_num) psum671o2_88
  · exact le_trans (by norm_num) psum671o2_89
  · exact le_trans (by norm_num) psum671o2_90
  · exact le_trans (by norm_num) psum671o2_91
  · exact le_trans (by norm_num) psum671o2_92
  · exact le_trans (by norm_num) psum671o2_93
  · exact le_trans (by norm_num) psum671o2_94
  · exact le_trans (by norm_num) psum671o2_95
  · exact le_trans (by norm_num) psum671o2_96
  · exact le_trans (by norm_num) psum671o2_97
  · exact le_trans (by norm_num) psum671o2_98
  · exact le_trans (by norm_num) psum671o2_99
  · exact le_trans (by norm_num) psum671o2_100
  · exact le_trans (by norm_num) psum671o2_101
  · exact le_trans (by norm_num) psum671o2_102
  · exact le_trans (by norm_num) psum671o2_103
  · exact le_trans (by norm_num) psum671o2_104
  · exact le_trans (by norm_num) psum671o2_105
  · exact le_trans (by norm_num) psum671o2_106
  · exact le_trans (by norm_num) psum671o2_107
  · exact le_trans (by norm_num) psum671o2_108
  · exact le_trans (by norm_num) psum671o2_109
  · exact le_trans (by norm_num) psum671o2_110
  · exact le_trans (by norm_num) psum671o2_111
  · exact le_trans (by norm_num) psum671o2_112
  · exact le_trans (by norm_num) psum671o2_113
  · exact le_trans (by norm_num) psum671o2_114
  · exact le_trans (by norm_num) psum671o2_115
  · exact le_trans (by norm_num) psum671o2_116
  · exact le_trans (by norm_num) psum671o2_117
  · exact le_trans (by norm_num) psum671o2_118
  · exact le_trans (by norm_num) psum671o2_119
  · exact le_trans (by norm_num) psum671o2_120
  · exact le_trans (by norm_num) psum671o2_121
  · exact le_trans (by norm_num) psum671o2_122
  · exact le_trans (by norm_num) psum671o2_123
  · exact le_trans (by norm_num) psum671o2_124
  · exact le_trans (by norm_num) psum671o2_125
  · exact le_trans (by norm_num) psum671o2_126
  · exact le_trans (by norm_num) psum671o2_127
  · exact le_trans (by norm_num) psum671o2_128
  · exact le_trans (by norm_num) psum671o2_129
  · exact le_trans (by norm_num) psum671o2_130
  · exact le_trans (by norm_num) psum671o2_131
  · exact le_trans (by norm_num) psum671o2_132
  · exact le_trans (by norm_num) psum671o2_133
  · exact le_trans (by norm_num) psum671o2_134
  · exact le_trans (by norm_num) psum671o2_135
  · exact le_trans (by norm_num) psum671o2_136
  · exact le_trans (by norm_num) psum671o2_137
  · exact le_trans (by norm_num) psum671o2_138
  · exact le_trans (by norm_num) psum671o2_139
  · exact le_trans (by norm_num) psum671o2_140
  · exact le_trans (by norm_num) psum671o2_141
  · exact le_trans (by norm_num) psum671o2_142
  · exact le_trans (by norm_num) psum671o2_143
  · exact le_trans (by norm_num) psum671o2_144
  · exact le_trans (by norm_num) psum671o2_145
  · exact le_trans (by norm_num) psum671o2_146
  · exact le_trans (by norm_num) psum671o2_147
  · exact le_trans (by norm_num) psum671o2_148
  · exact le_trans (by norm_num) psum671o2_149
  · exact le_trans (by norm_num) psum671o2_150
  · exact le_trans (by norm_num) psum671o2_151
  · exact le_trans (by norm_num) psum671o2_152
  · exact le_trans (by norm_num) psum671o2_153
  · exact le_trans (by norm_num) psum671o2_154
  · exact le_trans (by norm_num) psum671o2_155
  · exact le_trans (by norm_num) psum671o2_156
  · exact le_trans (by norm_num) psum671o2_157
  · exact le_trans (by norm_num) psum671o2_158
  · exact le_trans (by norm_num) psum671o2_159
  · exact le_trans (by norm_num) psum671o2_160
  · exact le_trans (by norm_num) psum671o2_161
  · exact le_trans (by norm_num) psum671o2_162
  · exact le_trans (by norm_num) psum671o2_163
  · exact le_trans (by norm_num) psum671o2_164
  · exact le_trans (by norm_num) psum671o2_165
  · exact le_trans (by norm_num) psum671o2_166
  · exact le_trans (by norm_num) psum671o2_167
  · exact le_trans (by norm_num) psum671o2_168
  · exact le_trans (by norm_num) psum671o2_169
  · exact le_trans (by norm_num) psum671o2_170
  · exact le_trans (by norm_num) psum671o2_171
  · exact le_trans (by norm_num) psum671o2_172
  · exact le_trans (by norm_num) psum671o2_173
  · exact le_trans (by norm_num) psum671o2_174
  · exact le_trans (by norm_num) psum671o2_175
  · exact le_trans (by norm_num) psum671o2_176
  · exact le_trans (by norm_num) psum671o2_177
  · exact le_trans (by norm_num) psum671o2_178
  · exact le_trans (by norm_num) psum671o2_179
  · exact le_trans (by norm_num) psum671o2_180
  · exact le_trans (by norm_num) psum671o2_181
  · exact le_trans (by norm_num) psum671o2_182
  · exact le_trans (by norm_num) psum671o2_183
  · exact le_trans (by norm_num) psum671o2_184
  · exact le_trans (by norm_num) psum671o2_185
  · exact le_trans (by norm_num) psum671o2_186
  · exact le_trans (by norm_num) psum671o2_187
  · exact le_trans (by norm_num) psum671o2_188
  · exact le_trans (by norm_num) psum671o2_189
  · exact le_trans (by norm_num) psum671o2_190
  · exact le_trans (by norm_num) psum671o2_191
  · exact le_trans (by norm_num) psum671o2_192
  · exact le_trans (by norm_num) psum671o2_193
  · exact le_trans (by norm_num) psum671o2_194
  · exact le_trans (by norm_num) psum671o2_195
  · exact le_trans (by norm_num) psum671o2_196
  · exact le_trans (by norm_num) psum671o2_197
  · exact le_trans (by norm_num) psum671o2_198
  · exact le_trans (by norm_num) psum671o2_199
  · exact le_trans (by norm_num) psum671o2_200
  · exact le_trans (by norm_num) psum671o2_201
  · exact le_trans (by norm_num) psum671o2_202
  · exact le_trans (by norm_num) psum671o2_203
  · exact le_trans (by norm_num) psum671o2_204
  · exact le_trans (by norm_num) psum671o2_205
  · exact le_trans (by norm_num) psum671o2_206
  · exact le_trans (by norm_num) psum671o2_207
  · exact le_trans (by norm_num) psum671o2_208
  · exact le_trans (by norm_num) psum671o2_209
  · exact le_trans (by norm_num) psum671o2_210
  · exact le_trans (by norm_num) psum671o2_211
  · exact le_trans (by norm_num) psum671o2_212
  · exact le_trans (by norm_num) psum671o2_213
  · exact le_trans (by norm_num) psum671o2_214
  · exact le_trans (by norm_num) psum671o2_215
  · exact le_trans (by norm_num) psum671o2_216
  · exact le_trans (by norm_num) psum671o2_217
  · exact le_trans (by norm_num) psum671o2_218
  · exact le_trans (by norm_num) psum671o2_219
  · exact le_trans (by norm_num) psum671o2_220
  · exact le_trans (by norm_num) psum671o2_221
  · exact le_trans (by norm_num) psum671o2_222
  · exact le_trans (by norm_num) psum671o2_223
  · exact le_trans (by norm_num) psum671o2_224
  · exact le_trans (by norm_num) psum671o2_225
  · exact le_trans (by norm_num) psum671o2_226
  · exact le_trans (by norm_num) psum671o2_227
  · exact le_trans (by norm_num) psum671o2_228
  · exact le_trans (by norm_num) psum671o2_229
  · exact le_trans (by norm_num) psum671o2_230
  · exact le_trans (by norm_num) psum671o2_231
  · exact le_trans (by norm_num) psum671o2_232
  · exact le_trans (by norm_num) psum671o2_233
  · exact le_trans (by norm_num) psum671o2_234
  · exact le_trans (by norm_num) psum671o2_235
  · exact le_trans (by norm_num) psum671o2_236
  · exact le_trans (by norm_num) psum671o2_237
  · exact le_trans (by norm_num) psum671o2_238
  · exact le_trans (by norm_num) psum671o2_239
  · exact le_trans (by norm_num) psum671o2_240
  · exact le_trans (by norm_num) psum671o2_241
  · exact le_trans (by norm_num) psum671o2_242
  · exact le_trans (by norm_num) psum671o2_243
  · exact le_trans (by norm_num) psum671o2_244
  · exact le_trans (by norm_num) psum671o2_245
  · exact le_trans (by norm_num) psum671o2_246
  · exact le_trans (by norm_num) psum671o2_247
  · exact le_trans (by norm_num) psum671o2_248
  · exact le_trans (by norm_num) psum671o2_249
  · exact le_trans (by norm_num) psum671o2_250
  · exact le_trans (by norm_num) psum671o2_251
  · exact le_trans (by norm_num) psum671o2_252
  · exact le_trans (by norm_num) psum671o2_253
  · exact le_trans (by norm_num) psum671o2_254
  · exact le_trans (by norm_num) psum671o2_255
  · exact le_trans (by norm_num) psum671o2_256
  · exact le_trans (by norm_num) psum671o2_257
  · exact le_trans (by norm_num) psum671o2_258
  · exact le_trans (by norm_num) psum671o2_259
  · exact le_trans (by norm_num) psum671o2_260
  · exact le_trans (by norm_num) psum671o2_261
  · exact le_trans (by norm_num) psum671o2_262
  · exact le_trans (by norm_num) psum671o2_263
  · exact le_trans (by norm_num) psum671o2_264
  · exact le_trans (by norm_num) psum671o2_265
  · exact le_trans (by norm_num) psum671o2_266
  · exact le_trans (by norm_num) psum671o2_267
  · exact le_trans (by norm_num) psum671o2_268
  · exact le_trans (by norm_num) psum671o2_269
  · exact le_trans (by norm_num) psum671o2_270
  · exact le_trans (by norm_num) psum671o2_271
  · exact le_trans (by norm_num) psum671o2_272
  · exact le_trans (by norm_num) psum671o2_273
  · exact le_trans (by norm_num) psum671o2_274
  · exact le_trans (by norm_num) psum671o2_275
  · exact le_trans (by norm_num) psum671o2_276
  · exact le_trans (by norm_num) psum671o2_277
  · exact le_trans (by norm_num) psum671o2_278
  · exact le_trans (by norm_num) psum671o2_279
  · exact le_trans (by norm_num) psum671o2_280
  · exact le_trans (by norm_num) psum671o2_281
  · exact le_trans (by norm_num) psum671o2_282
  · exact le_trans (by norm_num) psum671o2_283
  · exact le_trans (by norm_num) psum671o2_284
  · exact le_trans (by norm_num) psum671o2_285
  · exact le_trans (by norm_num) psum671o2_286
  · exact le_trans (by norm_num) psum671o2_287
  · exact le_trans (by norm_num) psum671o2_288
  · exact le_trans (by norm_num) psum671o2_289
  · exact le_trans (by norm_num) psum671o2_290
  · exact le_trans (by norm_num) psum671o2_291
  · exact le_trans (by norm_num) psum671o2_292
  · exact le_trans (by norm_num) psum671o2_293
  · exact le_trans (by norm_num) psum671o2_294
  · exact le_trans (by norm_num) psum671o2_295
  · exact le_trans (by norm_num) psum671o2_296
  · exact le_trans (by norm_num) psum671o2_297
  · exact le_trans (by norm_num) psum671o2_298
  · exact le_trans (by norm_num) psum671o2_299
  · exact le_trans (by norm_num) psum671o2_300
  · exact le_trans (by norm_num) psum671o2_301
  · exact le_trans (by norm_num) psum671o2_302
  · exact le_trans (by norm_num) psum671o2_303
  · exact le_trans (by norm_num) psum671o2_304
  · exact le_trans (by norm_num) psum671o2_305
  · exact le_trans (by norm_num) psum671o2_306
  · exact le_trans (by norm_num) psum671o2_307
  · exact le_trans (by norm_num) psum671o2_308
  · exact le_trans (by norm_num) psum671o2_309
  · exact le_trans (by norm_num) psum671o2_310
  · exact le_trans (by norm_num) psum671o2_311
  · exact le_trans (by norm_num) psum671o2_312
  · exact le_trans (by norm_num) psum671o2_313
  · exact le_trans (by norm_num) psum671o2_314
  · exact le_trans (by norm_num) psum671o2_315
  · exact le_trans (by norm_num) psum671o2_316
  · exact le_trans (by norm_num) psum671o2_317
  · exact le_trans (by norm_num) psum671o2_318
  · exact le_trans (by norm_num) psum671o2_319
  · exact le_trans (by norm_num) psum671o2_320
  · exact le_trans (by norm_num) psum671o2_321
  · exact le_trans (by norm_num) psum671o2_322
  · exact le_trans (by norm_num) psum671o2_323
  · exact le_trans (by norm_num) psum671o2_324
  · exact le_trans (by norm_num) psum671o2_325
  · exact le_trans (by norm_num) psum671o2_326
  · exact le_trans (by norm_num) psum671o2_327
  · exact le_trans (by norm_num) psum671o2_328
  · exact le_trans (by norm_num) psum671o2_329
  · exact le_trans (by norm_num) psum671o2_330
  · exact le_trans (by norm_num) psum671o2_331
  · exact le_trans (by norm_num) psum671o2_332
  · exact le_trans (by norm_num) psum671o2_333
  · exact le_trans (by norm_num) psum671o2_334
  · exact le_trans (by norm_num) psum671o2_335
  · exact le_trans (by norm_num) psum671o2_336
  · exact le_trans (by norm_num) psum671o2_337
  · exact le_trans (by norm_num) psum671o2_338
  · exact le_trans (by norm_num) psum671o2_339
  · exact le_trans (by norm_num) psum671o2_340
  · exact le_trans (by norm_num) psum671o2_341
  · exact le_trans (by norm_num) psum671o2_342
  · exact le_trans (by norm_num) psum671o2_343
  · exact le_trans (by norm_num) psum671o2_344
  · exact le_trans (by norm_num) psum671o2_345
  · exact le_trans (by norm_num) psum671o2_346
  · exact le_trans (by norm_num) psum671o2_347
  · exact le_trans (by norm_num) psum671o2_348
  · exact le_trans (by norm_num) psum671o2_349
  · exact le_trans (by norm_num) psum671o2_350
  · exact le_trans (by norm_num) psum671o2_351
  · exact le_trans (by norm_num) psum671o2_352
  · exact le_trans (by norm_num) psum671o2_353
  · exact le_trans (by norm_num) psum671o2_354
  · exact le_trans (by norm_num) psum671o2_355
  · exact le_trans (by norm_num) psum671o2_356
  · exact le_trans (by norm_num) psum671o2_357
  · exact le_trans (by norm_num) psum671o2_358
  · exact le_trans (by norm_num) psum671o2_359
  · exact le_trans (by norm_num) psum671o2_360
  · exact le_trans (by norm_num) psum671o2_361
  · exact le_trans (by norm_num) psum671o2_362
  · exact le_trans (by norm_num) psum671o2_363
  · exact le_trans (by norm_num) psum671o2_364
  · exact le_trans (by norm_num) psum671o2_365
  · exact le_trans (by norm_num) psum671o2_366
  · exact le_trans (by norm_num) psum671o2_367
  · exact le_trans (by norm_num) psum671o2_368
  · exact le_trans (by norm_num) psum671o2_369
  · exact le_trans (by norm_num) psum671o2_370
  · exact le_trans (by norm_num) psum671o2_371
  · exact le_trans (by norm_num) psum671o2_372
  · exact le_trans (by norm_num) psum671o2_373
  · exact le_trans (by norm_num) psum671o2_374
  · exact le_trans (by norm_num) psum671o2_375
  · exact le_trans (by norm_num) psum671o2_376
  · exact le_trans (by norm_num) psum671o2_377
  · exact le_trans (by norm_num) psum671o2_378
  · exact le_trans (by norm_num) psum671o2_379
  · exact le_trans (by norm_num) psum671o2_380
  · exact le_trans (by norm_num) psum671o2_381
  · exact le_trans (by norm_num) psum671o2_382
  · exact le_trans (by norm_num) psum671o2_383
  · exact le_trans (by norm_num) psum671o2_384
  · exact le_trans (by norm_num) psum671o2_385
  · exact le_trans (by norm_num) psum671o2_386
  · exact le_trans (by norm_num) psum671o2_387
  · exact le_trans (by norm_num) psum671o2_388
  · exact le_trans (by norm_num) psum671o2_389
  · exact le_trans (by norm_num) psum671o2_390
  · exact le_trans (by norm_num) psum671o2_391
  · exact le_trans (by norm_num) psum671o2_392
  · exact le_trans (by norm_num) psum671o2_393
  · exact le_trans (by norm_num) psum671o2_394
  · exact le_trans (by norm_num) psum671o2_395
  · exact le_trans (by norm_num) psum671o2_396
  · exact le_trans (by norm_num) psum671o2_397
  · exact le_trans (by norm_num) psum671o2_398
  · exact le_trans (by norm_num) psum671o2_399
  · exact le_trans (by norm_num) psum671o2_400
  · exact le_trans (by norm_num) psum671o2_401
  · exact le_trans (by norm_num) psum671o2_402
  · exact le_trans (by norm_num) psum671o2_403
  · exact le_trans (by norm_num) psum671o2_404
  · exact le_trans (by norm_num) psum671o2_405
  · exact le_trans (by norm_num) psum671o2_406
  · exact le_trans (by norm_num) psum671o2_407
  · exact le_trans (by norm_num) psum671o2_408
  · exact le_trans (by norm_num) psum671o2_409
  · exact le_trans (by norm_num) psum671o2_410
  · exact le_trans (by norm_num) psum671o2_411
  · exact le_trans (by norm_num) psum671o2_412
  · exact le_trans (by norm_num) psum671o2_413
  · exact le_trans (by norm_num) psum671o2_414
  · exact le_trans (by norm_num) psum671o2_415
  · exact le_trans (by norm_num) psum671o2_416
  · exact le_trans (by norm_num) psum671o2_417
  · exact le_trans (by norm_num) psum671o2_418
  · exact le_trans (by norm_num) psum671o2_419
  · exact le_trans (by norm_num) psum671o2_420
  · exact le_trans (by norm_num) psum671o2_421
  · exact le_trans (by norm_num) psum671o2_422
  · exact le_trans (by norm_num) psum671o2_423
  · exact le_trans (by norm_num) psum671o2_424
  · exact le_trans (by norm_num) psum671o2_425
  · exact le_trans (by norm_num) psum671o2_426
  · exact le_trans (by norm_num) psum671o2_427
  · exact le_trans (by norm_num) psum671o2_428
  · exact le_trans (by norm_num) psum671o2_429
  · exact le_trans (by norm_num) psum671o2_430
  · exact le_trans (by norm_num) psum671o2_431
  · exact le_trans (by norm_num) psum671o2_432
  · exact le_trans (by norm_num) psum671o2_433
  · exact le_trans (by norm_num) psum671o2_434
  · exact le_trans (by norm_num) psum671o2_435
  · exact le_trans (by norm_num) psum671o2_436
  · exact le_trans (by norm_num) psum671o2_437
  · exact le_trans (by norm_num) psum671o2_438
  · exact le_trans (by norm_num) psum671o2_439
  · exact le_trans (by norm_num) psum671o2_440
  · exact le_trans (by norm_num) psum671o2_441
  · exact le_trans (by norm_num) psum671o2_442
  · exact le_trans (by norm_num) psum671o2_443
  · exact le_trans (by norm_num) psum671o2_444
  · exact le_trans (by norm_num) psum671o2_445
  · exact le_trans (by norm_num) psum671o2_446
  · exact le_trans (by norm_num) psum671o2_447
  · exact le_trans (by norm_num) psum671o2_448
  · exact le_trans (by norm_num) psum671o2_449
  · exact le_trans (by norm_num) psum671o2_450
  · exact le_trans (by norm_num) psum671o2_451
  · exact le_trans (by norm_num) psum671o2_452
  · exact le_trans (by norm_num) psum671o2_453
  · exact le_trans (by norm_num) psum671o2_454
  · exact le_trans (by norm_num) psum671o2_455
  · exact le_trans (by norm_num) psum671o2_456
  · exact le_trans (by norm_num) psum671o2_457
  · exact le_trans (by norm_num) psum671o2_458
  · exact le_trans (by norm_num) psum671o2_459
  · exact le_trans (by norm_num) psum671o2_460
  · exact le_trans (by norm_num) psum671o2_461
  · exact le_trans (by norm_num) psum671o2_462
  · exact le_trans (by norm_num) psum671o2_463
  · exact le_trans (by norm_num) psum671o2_464
  · exact le_trans (by norm_num) psum671o2_465
  · exact le_trans (by norm_num) psum671o2_466
  · exact le_trans (by norm_num) psum671o2_467
  · exact le_trans (by norm_num) psum671o2_468
  · exact le_trans (by norm_num) psum671o2_469
  · exact le_trans (by norm_num) psum671o2_470
  · exact le_trans (by norm_num) psum671o2_471
  · exact le_trans (by norm_num) psum671o2_472
  · exact le_trans (by norm_num) psum671o2_473
  · exact le_trans (by norm_num) psum671o2_474
  · exact le_trans (by norm_num) psum671o2_475
  · exact le_trans (by norm_num) psum671o2_476
  · exact le_trans (by norm_num) psum671o2_477
  · exact le_trans (by norm_num) psum671o2_478
  · exact le_trans (by norm_num) psum671o2_479
  · exact le_trans (by norm_num) psum671o2_480
  · exact le_trans (by norm_num) psum671o2_481
  · exact le_trans (by norm_num) psum671o2_482
  · exact le_trans (by norm_num) psum671o2_483
  · exact le_trans (by norm_num) psum671o2_484
  · exact le_trans (by norm_num) psum671o2_485
  · exact le_trans (by norm_num) psum671o2_486
  · exact le_trans (by norm_num) psum671o2_487
  · exact le_trans (by norm_num) psum671o2_488
  · exact le_trans (by norm_num) psum671o2_489
  · exact le_trans (by norm_num) psum671o2_490
  · exact le_trans (by norm_num) psum671o2_491
  · exact le_trans (by norm_num) psum671o2_492
  · exact le_trans (by norm_num) psum671o2_493
  · exact le_trans (by norm_num) psum671o2_494
  · exact le_trans (by norm_num) psum671o2_495
  · exact le_trans (by norm_num) psum671o2_496
  · exact le_trans (by norm_num) psum671o2_497
  · exact le_trans (by norm_num) psum671o2_498
  · exact le_trans (by norm_num) psum671o2_499
  · exact le_trans (by norm_num) psum671o2_500

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum671o2_floor
#print axioms CriticalLinePhasor.DVP.psum671o2_500
end AxiomAudit
