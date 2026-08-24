import RequestProject.DVPCos561o2Table

/-!
# The cosine partial-sum floor, `t = 561/2`
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 561/2` segment certificate. -/
def cos561o2c (n : ℕ) : ℝ := Real.cos (((561:ℕ):ℝ) * (Real.log n / 2))

theorem psum561o2_11 : ((476331/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos561o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 11 - ((476351/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum561o2_12 : ((1866827/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos561o2c k) + cos561o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_11
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 12 - ((182841/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_13 : ((108467/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos561o2c k) + cos561o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_12
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 13 - ((-999051/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_14 : ((1266779/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos561o2c k) + cos561o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_13
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 14 - ((399083/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_15 : ((2058367/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos561o2c k) + cos561o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_14
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 15 - ((197907/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_16 : ((444903/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos561o2c k) + cos561o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_15
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 16 - ((41547/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_17 : ((1230151/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos561o2c k) + cos561o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_16
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 17 - ((-248581/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_18 : ((2206363/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos561o2c k) + cos561o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_17
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 18 - ((244063/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_19 : ((1258271/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos561o2c k) + cos561o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_18
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 19 - ((-237013/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_20 : ((1185157/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos561o2c k) + cos561o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_19
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 20 - ((-36537/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_21 : ((1025307/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos561o2c k) + cos561o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_20
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 21 - ((865497/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_22 : ((609937/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos561o2c k) + cos561o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_21
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 22 - ((999111/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_23 : ((252493/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos561o2c k) + cos561o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_22
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 23 - ((990243/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_24 : ((1189751/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos561o2c k) + cos561o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_23
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 24 - ((179789/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_25 : ((139089/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos561o2c k) + cos561o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_24
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 25 - ((-77029/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_26 : ((1748839/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos561o2c k) + cos561o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_25
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 26 - ((-95313/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_27 : ((4154613/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos561o2c k) + cos561o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_26
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 27 - ((26279/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_28 : ((42141/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos561o2c k) + cos561o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_27
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 28 - ((59527/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_29 : ((75083/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos561o2c k) + cos561o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_28
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 29 - ((-45991/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_30 : ((4287401/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos561o2c k) + cos561o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_29
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 30 - ((533291/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_31 : ((989583/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos561o2c k) + cos561o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_30
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 31 - ((-329029/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_32 : ((471917/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos561o2c k) + cos561o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_31
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 32 - ((-45739/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_33 : ((4604307/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos561o2c k) + cos561o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_32
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 33 - ((829011/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_34 : ((370713/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos561o2c k) + cos561o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_33
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 34 - ((-897137/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_35 : ((3527529/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos561o2c k) + cos561o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_34
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 35 - ((-179561/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_36 : ((4518713/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos561o2c k) + cos561o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_35
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 36 - ((123903/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_37 : ((601911/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos561o2c k) + cos561o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_36
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 37 - ((59323/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_38 : ((252147/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos561o2c k) + cos561o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_37
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 38 - ((-24403/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_39 : ((1543851/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos561o2c k) + cos561o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_38
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 39 - ((-94661/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_40 : ((2676167/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos561o2c k) + cos561o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_39
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 40 - ((-82299/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_41 : ((45209/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos561o2c k) + cos561o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_40
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 41 - ((217249/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_42 : ((706773/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos561o2c k) + cos561o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_41
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 42 - ((640529/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_43 : ((4381881/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos561o2c k) + cos561o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_42
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 43 - ((106007/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_44 : ((5305559/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos561o2c k) + cos561o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_43
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 44 - ((461859/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_45 : ((779609/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos561o2c k) + cos561o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_44
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 45 - ((931353/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_46 : ((7118793/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos561o2c k) + cos561o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_45
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 46 - ((881961/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_47 : ((3928119/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos561o2c k) + cos561o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_46
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 47 - ((147497/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_48 : ((8292633/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos561o2c k) + cos561o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_47
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 48 - ((87287/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_49 : ((1030593/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos561o2c k) + cos561o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_48
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 49 - ((-47849/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_50 : ((7628301/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos561o2c k) + cos561o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_49
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 50 - ((-616403/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_51 : ((3322037/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos561o2c k) + cos561o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_50
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 51 - ((-984187/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_52 : ((2926511/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos561o2c k) + cos561o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_51
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 52 - ((-197753/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_53 : ((2940341/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos561o2c k) + cos561o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_52
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 53 - ((277/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_54 : ((3378381/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos561o2c k) + cos561o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_53
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 54 - ((21903/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_55 : ((7562847/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos561o2c k) + cos561o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_54
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 55 - ((6449/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_56 : ((7275493/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos561o2c k) + cos561o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_55
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 56 - ((-143657/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_57 : ((784527/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos561o2c k) + cos561o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_56
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 57 - ((-999237/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_58 : ((3074789/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos561o2c k) + cos561o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_57
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 58 - ((-63299/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_59 : ((7127667/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos561o2c k) + cos561o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_58
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 59 - ((978129/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_60 : ((1467517/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos561o2c k) + cos561o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_59
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 60 - ((104979/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_61 : ((3173363/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos561o2c k) + cos561o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_60
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 61 - ((-990819/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_62 : ((6362393/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos561o2c k) + cos561o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_61
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 62 - ((15707/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_63 : ((1466739/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos561o2c k) + cos561o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_62
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 63 - ((485671/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_64 : ((1364767/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos561o2c k) + cos561o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_63
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 64 - ((-25491/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_65 : ((6200961/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos561o2c k) + cos561o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_64
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 65 - ((-311417/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_66 : ((7171661/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos561o2c k) + cos561o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_65
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 66 - ((48537/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_67 : ((6922519/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos561o2c k) + cos561o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_66
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 67 - ((-124551/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_68 : ((62319/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos561o2c k) + cos561o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_67
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 68 - ((-690579/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_69 : ((1444277/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos561o2c k) + cos561o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_68
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 69 - ((39581/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_70 : ((6714523/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos561o2c k) + cos561o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_69
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 70 - ((-253411/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_71 : ((6413529/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos561o2c k) + cos561o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_70
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 71 - ((-150477/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_72 : ((1824711/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos561o2c k) + cos561o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_71
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 72 - ((177071/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_73 : ((3164199/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos561o2c k) + cos561o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_72
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 73 - ((-485203/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_74 : ((3467619/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos561o2c k) + cos561o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_73
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 74 - ((3793/6250 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_75 : ((345333/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos561o2c k) + cos561o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_74
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 75 - ((-14269/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_76 : ((6388079/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos561o2c k) + cos561o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_75
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 76 - ((-518541/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_77 : ((1816343/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos561o2c k) + cos561o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_76
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 77 - ((877333/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_78 : ((626559/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos561o2c k) + cos561o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_77
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 78 - ((-499871/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_79 : ((3591537/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos561o2c k) + cos561o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_78
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 79 - ((229381/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_80 : ((6483283/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos561o2c k) + cos561o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_79
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 80 - ((-699751/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_81 : ((6902049/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos561o2c k) + cos561o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_80
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 81 - ((209403/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_82 : ((105788/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos561o2c k) + cos561o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_81
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 82 - ((-131577/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_83 : ((6644229/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos561o2c k) + cos561o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_82
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 83 - ((-126163/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_84 : ((139633/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos561o2c k) + cos561o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_83
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 84 - ((337461/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_85 : ((405177/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos561o2c k) + cos561o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_84
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 85 - ((-249389/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_86 : ((3548477/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos561o2c k) + cos561o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_85
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 86 - ((307081/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_87 : ((6406137/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos561o2c k) + cos561o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_86
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 87 - ((-690777/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_88 : ((1785453/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos561o2c k) + cos561o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_87
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 88 - ((147143/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_89 : ((3193719/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos561o2c k) + cos561o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_88
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 89 - ((-377167/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_90 : ((7136799/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos561o2c k) + cos561o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_89
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 90 - ((749401/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_91 : ((801987/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos561o2c k) + cos561o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_90
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 91 - ((-720863/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_92 : ((7082019/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos561o2c k) + cos561o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_91
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 92 - ((666163/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_93 : ((6501011/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos561o2c k) + cos561o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_92
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 93 - ((-72621/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_94 : ((1740323/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos561o2c k) + cos561o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_93
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 94 - ((460321/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_95 : ((3330459/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos561o2c k) + cos561o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_94
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 95 - ((-150167/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_96 : ((3380679/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos561o2c k) + cos561o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_95
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 96 - ((314/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_97 : ((6895093/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos561o2c k) + cos561o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_96
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 97 - ((5351/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_98 : ((40667/6250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos561o2c k) + cos561o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_97
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 98 - ((-388333/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_99 : ((7145271/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos561o2c k) + cos561o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_98
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 99 - ((638591/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_100 : ((6295671/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos561o2c k) + cos561o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_99
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 100 - ((-21239/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_101 : ((7274663/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos561o2c k) + cos561o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_100
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 101 - ((122379/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_102 : ((628953/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos561o2c k) + cos561o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_101
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 102 - ((-985093/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_103 : ((1781777/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos561o2c k) + cos561o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_102
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 103 - ((418809/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_104 : ((659463/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos561o2c k) + cos561o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_103
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 104 - ((-266219/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_105 : ((6698533/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos561o2c k) + cos561o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_104
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 105 - ((103943/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_106 : ((3534097/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos561o2c k) + cos561o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_105
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 106 - ((369701/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_107 : ((393333/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos561o2c k) + cos561o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_106
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 107 - ((-387413/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_108 : ((1456349/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos561o2c k) + cos561o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_107
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 108 - ((988457/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_109 : ((6362307/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos561o2c k) + cos561o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_108
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 109 - ((-459699/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_110 : ((864477/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos561o2c k) + cos561o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_109
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 110 - ((553549/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_111 : ((6932251/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos561o2c k) + cos561o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_110
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 111 - ((659/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_112 : ((6333111/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos561o2c k) + cos561o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_111
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 112 - ((-5991/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_113 : ((7294073/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos561o2c k) + cos561o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_112
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 113 - ((480501/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_114 : ((3184567/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos561o2c k) + cos561o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_113
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 114 - ((-924899/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_115 : ((6838819/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos561o2c k) + cos561o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_114
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 115 - ((18789/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_116 : ((3530477/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos561o2c k) + cos561o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_115
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 116 - ((8887/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_117 : ((6242939/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos561o2c k) + cos561o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_116
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 117 - ((-32719/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_118 : ((1446583/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos561o2c k) + cos561o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_117
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 118 - ((15469/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_119 : ((3311913/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos561o2c k) + cos561o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_118
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 119 - ((-609049/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_120 : ((3242407/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos561o2c k) + cos561o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_119
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 120 - ((-34743/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_121 : ((456253/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos561o2c k) + cos561o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_120
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 121 - ((407637/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_122 : ((1264621/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos561o2c k) + cos561o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_121
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 122 - ((-976903/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_123 : ((850713/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos561o2c k) + cos561o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_122
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 123 - ((482639/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_124 : ((3582083/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos561o2c k) + cos561o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_123
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 124 - ((179251/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_125 : ((6213507/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos561o2c k) + cos561o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_124
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 125 - ((-950619/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_126 : ((1408777/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos561o2c k) + cos561o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_125
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 126 - ((415209/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_127 : ((6988229/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos561o2c k) + cos561o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_126
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 127 - ((-869/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_128 : ((1242737/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos561o2c k) + cos561o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_127
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 128 - ((-96813/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_129 : ((717639/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos561o2c k) + cos561o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_128
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 129 - ((192549/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_130 : ((137209/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos561o2c k) + cos561o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_129
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 130 - ((-3159/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_131 : ((6238841/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos561o2c k) + cos561o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_130
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 131 - ((-621569/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_132 : ((3616463/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos561o2c k) + cos561o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_131
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 132 - ((7953/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_133 : ((6808989/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos561o2c k) + cos561o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_132
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 133 - ((-423897/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_134 : ((3121031/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos561o2c k) + cos561o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_133
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 134 - ((-566887/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_135 : ((7238151/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos561o2c k) + cos561o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_134
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 135 - ((996129/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_136 : ((6838303/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos561o2c k) + cos561o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_135
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 136 - ((-6247/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_137 : ((19416/3125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos561o2c k) + cos561o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_136
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 137 - ((-625143/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_138 : ((7191913/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos561o2c k) + cos561o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_137
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 138 - ((978833/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_139 : ((173651/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos561o2c k) + cos561o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_138
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 139 - ((-245833/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_140 : ((6173703/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos561o2c k) + cos561o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_139
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 140 - ((-772297/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_141 : ((56569/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos561o2c k) + cos561o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_140
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 141 - ((448731/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_142 : ((7116331/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos561o2c k) + cos561o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_141
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 142 - ((22623/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_143 : ((6177737/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos561o2c k) + cos561o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_142
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 143 - ((-469277/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_144 : ((6849229/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos561o2c k) + cos561o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_143
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 144 - ((167883/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_145 : ((7296823/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos561o2c k) + cos561o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_144
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 145 - ((223817/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_146 : ((6302509/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos561o2c k) + cos561o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_145
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 146 - ((-497137/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_147 : ((1307413/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos561o2c k) + cos561o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_146
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 147 - ((58649/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_148 : ((3690079/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos561o2c k) + cos561o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_147
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 148 - ((843133/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_149 : ((6605677/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos561o2c k) + cos561o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_148
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 149 - ((-774441/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_150 : ((3117579/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos561o2c k) + cos561o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_149
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 150 - ((-370479/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_151 : ((3615689/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos561o2c k) + cos561o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_150
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 151 - ((49813/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_152 : ((7038367/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos561o2c k) + cos561o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_151
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 152 - ((-192971/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_153 : ((767937/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos561o2c k) + cos561o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_152
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 153 - ((-894831/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_154 : ((680233/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos561o2c k) + cos561o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_153
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 154 - ((329437/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_155 : ((7372479/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos561o2c k) + cos561o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_154
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 155 - ((570189/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_156 : ((6441443/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos561o2c k) + cos561o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_155
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 156 - ((-232749/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_157 : ((6289867/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos561o2c k) + cos561o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_156
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 157 - ((-9471/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_158 : ((455509/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos561o2c k) + cos561o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_157
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 158 - ((998317/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_159 : ((1758489/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos561o2c k) + cos561o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_158
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 159 - ((-63537/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_160 : ((383201/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos561o2c k) + cos561o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_159
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 160 - ((-9027/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_161 : ((1342711/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos561o2c k) + cos561o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_160
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 161 - ((582379/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_162 : ((927373/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos561o2c k) + cos561o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_161
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 162 - ((705469/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_163 : ((6609571/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos561o2c k) + cos561o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_162
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 163 - ((-809373/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_164 : ((6145169/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos561o2c k) + cos561o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_163
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 164 - ((-232181/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_165 : ((3542499/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos561o2c k) + cos561o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_164
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 165 - ((939869/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_166 : ((182689/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos561o2c k) + cos561o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_165
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 166 - ((111301/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_167 : ((3156813/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos561o2c k) + cos561o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_166
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 167 - ((-496947/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_168 : ((1261367/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos561o2c k) + cos561o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_167
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 168 - ((-6751/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_169 : ((7302999/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos561o2c k) + cos561o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_168
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 169 - ((249051/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_170 : ((7132561/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos561o2c k) + cos561o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_169
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 170 - ((-85199/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_171 : ((6162529/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos561o2c k) + cos561o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_170
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 171 - ((-121249/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_172 : ((6467899/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos561o2c k) + cos561o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_171
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 172 - ((30541/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_173 : ((7401747/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos561o2c k) + cos561o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_172
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 173 - ((14592/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_174 : ((7001649/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos561o2c k) + cos561o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_173
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 174 - ((-200029/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_175 : ((15251/2500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos561o2c k) + cos561o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_174
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 175 - ((-901209/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_176 : ((1311671/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos561o2c k) + cos561o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_175
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 176 - ((91599/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_177 : ((929833/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos561o2c k) + cos561o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_176
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 177 - ((880349/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_178 : ((6955969/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos561o2c k) + cos561o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_177
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 178 - ((-96531/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_179 : ((380027/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos561o2c k) + cos561o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_178
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 179 - ((-875497/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_180 : ((6556481/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos561o2c k) + cos561o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_179
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 180 - ((476089/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_181 : ((3721849/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos561o2c k) + cos561o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_180
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 181 - ((887257/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_182 : ((218907/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos561o2c k) + cos561o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_181
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 182 - ((-219317/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_183 : ((609201/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos561o2c k) + cos561o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_182
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 183 - ((-456487/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_184 : ((6461123/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos561o2c k) + cos561o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_183
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 184 - ((369153/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_185 : ((462993/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos561o2c k) + cos561o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_184
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 185 - ((189361/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_186 : ((7142117/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos561o2c k) + cos561o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_185
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 186 - ((-265731/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_187 : ((6162451/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos561o2c k) + cos561o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_186
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 187 - ((-489813/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_188 : ((1572367/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos561o2c k) + cos561o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_187
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 188 - ((127057/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_189 : ((728843/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos561o2c k) + cos561o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_188
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 189 - ((499501/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_190 : ((3667143/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos561o2c k) + cos561o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_189
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 190 - ((5737/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_191 : ((793079/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos561o2c k) + cos561o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_190
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 191 - ((-494807/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_192 : ((1524223/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos561o2c k) + cos561o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_191
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 192 - ((-2477/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_193 : ((3515673/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos561o2c k) + cos561o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_192
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 193 - ((467247/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_194 : ((7497631/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos561o2c k) + cos561o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_193
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 194 - ((18653/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_195 : ((3340053/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos561o2c k) + cos561o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_194
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 195 - ((-163497/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_196 : ((5998591/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos561o2c k) + cos561o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_195
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 196 - ((-27259/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_197 : ((3312783/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos561o2c k) + cos561o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_196
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 197 - ((125403/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_198 : ((3744879/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos561o2c k) + cos561o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_197
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 198 - ((108029/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_199 : ((3564293/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos561o2c k) + cos561o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_198
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 199 - ((-90283/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_200 : ((3074711/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos561o2c k) + cos561o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_199
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 200 - ((-244781/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_201 : ((6182293/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos561o2c k) + cos561o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_200
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 201 - ((32911/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_202 : ((7171637/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos561o2c k) + cos561o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_201
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 202 - ((123673/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_203 : ((7497007/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos561o2c k) + cos561o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_202
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 203 - ((32541/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_204 : ((265243/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos561o2c k) + cos561o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_203
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 204 - ((-216473/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_205 : ((2984693/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos561o2c k) + cos561o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_204
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 205 - ((-661649/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_206 : ((6568107/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos561o2c k) + cos561o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_205
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 206 - ((598761/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_207 : ((3738619/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos561o2c k) + cos561o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_206
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 207 - ((909171/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_208 : ((3634113/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos561o2c k) + cos561o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_207
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 208 - ((-52243/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_209 : ((3134149/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos561o2c k) + cos561o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_208
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 209 - ((-62493/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_210 : ((1505983/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos561o2c k) + cos561o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_209
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 210 - ((-122163/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_211 : ((6908531/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos561o2c k) + cos561o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_210
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 211 - ((884639/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_212 : ((7575093/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos561o2c k) + cos561o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_211
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 212 - ((333301/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_213 : ((701839/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos561o2c k) + cos561o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_212
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 213 - ((-556663/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_214 : ((1214683/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos561o2c k) + cos561o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_213
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 214 - ((-188987/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_215 : ((6143613/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos561o2c k) + cos561o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_214
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 215 - ((35119/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_216 : ((890483/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos561o2c k) + cos561o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_215
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 216 - ((980291/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_217 : ((7580329/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos561o2c k) + cos561o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_216
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 217 - ((91301/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_218 : ((3426079/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos561o2c k) + cos561o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_217
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 218 - ((-728131/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_219 : ((748573/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos561o2c k) + cos561o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_218
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 219 - ((-431767/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_220 : ((3111017/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos561o2c k) + cos561o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_219
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 220 - ((23349/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_221 : ((722001/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos561o2c k) + cos561o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_220
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 221 - ((15594/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_222 : ((1515843/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos561o2c k) + cos561o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_221
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 222 - ((71849/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_223 : ((85001/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos561o2c k) + cos561o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_222
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 223 - ((-155819/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_224 : ((5962191/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos561o2c k) + cos561o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_223
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 224 - ((-837849/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_225 : ((97117/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos561o2c k) + cos561o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_224
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 225 - ((253337/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_226 : ((450809/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos561o2c k) + cos561o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_225
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 226 - ((124687/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_227 : ((7605223/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos561o2c k) + cos561o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_226
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 227 - ((392319/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_228 : ((6867377/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos561o2c k) + cos561o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_227
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 228 - ((-368903/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_229 : ((373963/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos561o2c k) + cos561o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_228
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 229 - ((-883929/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_230 : ((1224191/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos561o2c k) + cos561o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_229
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 230 - ((137587/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_231 : ((709771/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos561o2c k) + cos561o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_230
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 231 - ((195359/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_232 : ((238797/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos561o2c k) + cos561o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_231
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 232 - ((271917/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_233 : ((7051141/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos561o2c k) + cos561o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_232
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 233 - ((-590323/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_234 : ((6085217/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos561o2c k) + cos561o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_233
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 234 - ((-241471/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_235 : ((746593/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos561o2c k) + cos561o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_234
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 235 - ((-112433/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_236 : ((3426957/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos561o2c k) + cos561o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_235
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 236 - ((88121/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_237 : ((7622787/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos561o2c k) + cos561o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_236
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 237 - ((768913/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_238 : ((7323497/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos561o2c k) + cos561o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_237
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 238 - ((-1197/4000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_239 : ((253103/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos561o2c k) + cos561o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_238
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 239 - ((-497941/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_240 : ((234263/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos561o2c k) + cos561o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_239
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 240 - ((-5887/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_241 : ((3241083/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos561o2c k) + cos561o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_240
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 241 - ((625631/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_242 : ((1861697/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos561o2c k) + cos561o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_241
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 242 - ((482331/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_243 : ((3796837/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos561o2c k) + cos561o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_242
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 243 - ((73463/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_244 : ((6749741/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos561o2c k) + cos561o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_243
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 244 - ((-843893/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_245 : ((4731/800 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos561o2c k) + cos561o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_244
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 245 - ((-835951/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_246 : ((1516457/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos561o2c k) + cos561o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_245
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 246 - ((76059/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_247 : ((7026801/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos561o2c k) + cos561o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_246
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 247 - ((961013/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_248 : ((7684353/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos561o2c k) + cos561o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_247
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 248 - ((82199/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_249 : ((455291/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos561o2c k) + cos561o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_248
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 249 - ((-399657/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum561o2_250 : ((3142621/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos561o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos561o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos561o2c k) + cos561o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos561o2c
    simpa using h
  have hprev := psum561o2_249
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos561o2c 250 - ((-499687/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos561o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 3200000 in
/-- **The Abel floor at `t = 561/2`.** -/
theorem psum561o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 250 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos561o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum561o2_11
  · exact le_trans (by norm_num) psum561o2_12
  · exact le_trans (by norm_num) psum561o2_13
  · exact le_trans (by norm_num) psum561o2_14
  · exact le_trans (by norm_num) psum561o2_15
  · exact le_trans (by norm_num) psum561o2_16
  · exact le_trans (by norm_num) psum561o2_17
  · exact le_trans (by norm_num) psum561o2_18
  · exact le_trans (by norm_num) psum561o2_19
  · exact le_trans (by norm_num) psum561o2_20
  · exact le_trans (by norm_num) psum561o2_21
  · exact le_trans (by norm_num) psum561o2_22
  · exact le_trans (by norm_num) psum561o2_23
  · exact le_trans (by norm_num) psum561o2_24
  · exact le_trans (by norm_num) psum561o2_25
  · exact le_trans (by norm_num) psum561o2_26
  · exact le_trans (by norm_num) psum561o2_27
  · exact le_trans (by norm_num) psum561o2_28
  · exact le_trans (by norm_num) psum561o2_29
  · exact le_trans (by norm_num) psum561o2_30
  · exact le_trans (by norm_num) psum561o2_31
  · exact le_trans (by norm_num) psum561o2_32
  · exact le_trans (by norm_num) psum561o2_33
  · exact le_trans (by norm_num) psum561o2_34
  · exact le_trans (by norm_num) psum561o2_35
  · exact le_trans (by norm_num) psum561o2_36
  · exact le_trans (by norm_num) psum561o2_37
  · exact le_trans (by norm_num) psum561o2_38
  · exact le_trans (by norm_num) psum561o2_39
  · exact le_trans (by norm_num) psum561o2_40
  · exact le_trans (by norm_num) psum561o2_41
  · exact le_trans (by norm_num) psum561o2_42
  · exact le_trans (by norm_num) psum561o2_43
  · exact le_trans (by norm_num) psum561o2_44
  · exact le_trans (by norm_num) psum561o2_45
  · exact le_trans (by norm_num) psum561o2_46
  · exact le_trans (by norm_num) psum561o2_47
  · exact le_trans (by norm_num) psum561o2_48
  · exact le_trans (by norm_num) psum561o2_49
  · exact le_trans (by norm_num) psum561o2_50
  · exact le_trans (by norm_num) psum561o2_51
  · exact le_trans (by norm_num) psum561o2_52
  · exact le_trans (by norm_num) psum561o2_53
  · exact le_trans (by norm_num) psum561o2_54
  · exact le_trans (by norm_num) psum561o2_55
  · exact le_trans (by norm_num) psum561o2_56
  · exact le_trans (by norm_num) psum561o2_57
  · exact le_trans (by norm_num) psum561o2_58
  · exact le_trans (by norm_num) psum561o2_59
  · exact le_trans (by norm_num) psum561o2_60
  · exact le_trans (by norm_num) psum561o2_61
  · exact le_trans (by norm_num) psum561o2_62
  · exact le_trans (by norm_num) psum561o2_63
  · exact le_trans (by norm_num) psum561o2_64
  · exact le_trans (by norm_num) psum561o2_65
  · exact le_trans (by norm_num) psum561o2_66
  · exact le_trans (by norm_num) psum561o2_67
  · exact le_trans (by norm_num) psum561o2_68
  · exact le_trans (by norm_num) psum561o2_69
  · exact le_trans (by norm_num) psum561o2_70
  · exact le_trans (by norm_num) psum561o2_71
  · exact le_trans (by norm_num) psum561o2_72
  · exact le_trans (by norm_num) psum561o2_73
  · exact le_trans (by norm_num) psum561o2_74
  · exact le_trans (by norm_num) psum561o2_75
  · exact le_trans (by norm_num) psum561o2_76
  · exact le_trans (by norm_num) psum561o2_77
  · exact le_trans (by norm_num) psum561o2_78
  · exact le_trans (by norm_num) psum561o2_79
  · exact le_trans (by norm_num) psum561o2_80
  · exact le_trans (by norm_num) psum561o2_81
  · exact le_trans (by norm_num) psum561o2_82
  · exact le_trans (by norm_num) psum561o2_83
  · exact le_trans (by norm_num) psum561o2_84
  · exact le_trans (by norm_num) psum561o2_85
  · exact le_trans (by norm_num) psum561o2_86
  · exact le_trans (by norm_num) psum561o2_87
  · exact le_trans (by norm_num) psum561o2_88
  · exact le_trans (by norm_num) psum561o2_89
  · exact le_trans (by norm_num) psum561o2_90
  · exact le_trans (by norm_num) psum561o2_91
  · exact le_trans (by norm_num) psum561o2_92
  · exact le_trans (by norm_num) psum561o2_93
  · exact le_trans (by norm_num) psum561o2_94
  · exact le_trans (by norm_num) psum561o2_95
  · exact le_trans (by norm_num) psum561o2_96
  · exact le_trans (by norm_num) psum561o2_97
  · exact le_trans (by norm_num) psum561o2_98
  · exact le_trans (by norm_num) psum561o2_99
  · exact le_trans (by norm_num) psum561o2_100
  · exact le_trans (by norm_num) psum561o2_101
  · exact le_trans (by norm_num) psum561o2_102
  · exact le_trans (by norm_num) psum561o2_103
  · exact le_trans (by norm_num) psum561o2_104
  · exact le_trans (by norm_num) psum561o2_105
  · exact le_trans (by norm_num) psum561o2_106
  · exact le_trans (by norm_num) psum561o2_107
  · exact le_trans (by norm_num) psum561o2_108
  · exact le_trans (by norm_num) psum561o2_109
  · exact le_trans (by norm_num) psum561o2_110
  · exact le_trans (by norm_num) psum561o2_111
  · exact le_trans (by norm_num) psum561o2_112
  · exact le_trans (by norm_num) psum561o2_113
  · exact le_trans (by norm_num) psum561o2_114
  · exact le_trans (by norm_num) psum561o2_115
  · exact le_trans (by norm_num) psum561o2_116
  · exact le_trans (by norm_num) psum561o2_117
  · exact le_trans (by norm_num) psum561o2_118
  · exact le_trans (by norm_num) psum561o2_119
  · exact le_trans (by norm_num) psum561o2_120
  · exact le_trans (by norm_num) psum561o2_121
  · exact le_trans (by norm_num) psum561o2_122
  · exact le_trans (by norm_num) psum561o2_123
  · exact le_trans (by norm_num) psum561o2_124
  · exact le_trans (by norm_num) psum561o2_125
  · exact le_trans (by norm_num) psum561o2_126
  · exact le_trans (by norm_num) psum561o2_127
  · exact le_trans (by norm_num) psum561o2_128
  · exact le_trans (by norm_num) psum561o2_129
  · exact le_trans (by norm_num) psum561o2_130
  · exact le_trans (by norm_num) psum561o2_131
  · exact le_trans (by norm_num) psum561o2_132
  · exact le_trans (by norm_num) psum561o2_133
  · exact le_trans (by norm_num) psum561o2_134
  · exact le_trans (by norm_num) psum561o2_135
  · exact le_trans (by norm_num) psum561o2_136
  · exact le_trans (by norm_num) psum561o2_137
  · exact le_trans (by norm_num) psum561o2_138
  · exact le_trans (by norm_num) psum561o2_139
  · exact le_trans (by norm_num) psum561o2_140
  · exact le_trans (by norm_num) psum561o2_141
  · exact le_trans (by norm_num) psum561o2_142
  · exact le_trans (by norm_num) psum561o2_143
  · exact le_trans (by norm_num) psum561o2_144
  · exact le_trans (by norm_num) psum561o2_145
  · exact le_trans (by norm_num) psum561o2_146
  · exact le_trans (by norm_num) psum561o2_147
  · exact le_trans (by norm_num) psum561o2_148
  · exact le_trans (by norm_num) psum561o2_149
  · exact le_trans (by norm_num) psum561o2_150
  · exact le_trans (by norm_num) psum561o2_151
  · exact le_trans (by norm_num) psum561o2_152
  · exact le_trans (by norm_num) psum561o2_153
  · exact le_trans (by norm_num) psum561o2_154
  · exact le_trans (by norm_num) psum561o2_155
  · exact le_trans (by norm_num) psum561o2_156
  · exact le_trans (by norm_num) psum561o2_157
  · exact le_trans (by norm_num) psum561o2_158
  · exact le_trans (by norm_num) psum561o2_159
  · exact le_trans (by norm_num) psum561o2_160
  · exact le_trans (by norm_num) psum561o2_161
  · exact le_trans (by norm_num) psum561o2_162
  · exact le_trans (by norm_num) psum561o2_163
  · exact le_trans (by norm_num) psum561o2_164
  · exact le_trans (by norm_num) psum561o2_165
  · exact le_trans (by norm_num) psum561o2_166
  · exact le_trans (by norm_num) psum561o2_167
  · exact le_trans (by norm_num) psum561o2_168
  · exact le_trans (by norm_num) psum561o2_169
  · exact le_trans (by norm_num) psum561o2_170
  · exact le_trans (by norm_num) psum561o2_171
  · exact le_trans (by norm_num) psum561o2_172
  · exact le_trans (by norm_num) psum561o2_173
  · exact le_trans (by norm_num) psum561o2_174
  · exact le_trans (by norm_num) psum561o2_175
  · exact le_trans (by norm_num) psum561o2_176
  · exact le_trans (by norm_num) psum561o2_177
  · exact le_trans (by norm_num) psum561o2_178
  · exact le_trans (by norm_num) psum561o2_179
  · exact le_trans (by norm_num) psum561o2_180
  · exact le_trans (by norm_num) psum561o2_181
  · exact le_trans (by norm_num) psum561o2_182
  · exact le_trans (by norm_num) psum561o2_183
  · exact le_trans (by norm_num) psum561o2_184
  · exact le_trans (by norm_num) psum561o2_185
  · exact le_trans (by norm_num) psum561o2_186
  · exact le_trans (by norm_num) psum561o2_187
  · exact le_trans (by norm_num) psum561o2_188
  · exact le_trans (by norm_num) psum561o2_189
  · exact le_trans (by norm_num) psum561o2_190
  · exact le_trans (by norm_num) psum561o2_191
  · exact le_trans (by norm_num) psum561o2_192
  · exact le_trans (by norm_num) psum561o2_193
  · exact le_trans (by norm_num) psum561o2_194
  · exact le_trans (by norm_num) psum561o2_195
  · exact le_trans (by norm_num) psum561o2_196
  · exact le_trans (by norm_num) psum561o2_197
  · exact le_trans (by norm_num) psum561o2_198
  · exact le_trans (by norm_num) psum561o2_199
  · exact le_trans (by norm_num) psum561o2_200
  · exact le_trans (by norm_num) psum561o2_201
  · exact le_trans (by norm_num) psum561o2_202
  · exact le_trans (by norm_num) psum561o2_203
  · exact le_trans (by norm_num) psum561o2_204
  · exact le_trans (by norm_num) psum561o2_205
  · exact le_trans (by norm_num) psum561o2_206
  · exact le_trans (by norm_num) psum561o2_207
  · exact le_trans (by norm_num) psum561o2_208
  · exact le_trans (by norm_num) psum561o2_209
  · exact le_trans (by norm_num) psum561o2_210
  · exact le_trans (by norm_num) psum561o2_211
  · exact le_trans (by norm_num) psum561o2_212
  · exact le_trans (by norm_num) psum561o2_213
  · exact le_trans (by norm_num) psum561o2_214
  · exact le_trans (by norm_num) psum561o2_215
  · exact le_trans (by norm_num) psum561o2_216
  · exact le_trans (by norm_num) psum561o2_217
  · exact le_trans (by norm_num) psum561o2_218
  · exact le_trans (by norm_num) psum561o2_219
  · exact le_trans (by norm_num) psum561o2_220
  · exact le_trans (by norm_num) psum561o2_221
  · exact le_trans (by norm_num) psum561o2_222
  · exact le_trans (by norm_num) psum561o2_223
  · exact le_trans (by norm_num) psum561o2_224
  · exact le_trans (by norm_num) psum561o2_225
  · exact le_trans (by norm_num) psum561o2_226
  · exact le_trans (by norm_num) psum561o2_227
  · exact le_trans (by norm_num) psum561o2_228
  · exact le_trans (by norm_num) psum561o2_229
  · exact le_trans (by norm_num) psum561o2_230
  · exact le_trans (by norm_num) psum561o2_231
  · exact le_trans (by norm_num) psum561o2_232
  · exact le_trans (by norm_num) psum561o2_233
  · exact le_trans (by norm_num) psum561o2_234
  · exact le_trans (by norm_num) psum561o2_235
  · exact le_trans (by norm_num) psum561o2_236
  · exact le_trans (by norm_num) psum561o2_237
  · exact le_trans (by norm_num) psum561o2_238
  · exact le_trans (by norm_num) psum561o2_239
  · exact le_trans (by norm_num) psum561o2_240
  · exact le_trans (by norm_num) psum561o2_241
  · exact le_trans (by norm_num) psum561o2_242
  · exact le_trans (by norm_num) psum561o2_243
  · exact le_trans (by norm_num) psum561o2_244
  · exact le_trans (by norm_num) psum561o2_245
  · exact le_trans (by norm_num) psum561o2_246
  · exact le_trans (by norm_num) psum561o2_247
  · exact le_trans (by norm_num) psum561o2_248
  · exact le_trans (by norm_num) psum561o2_249
  · exact le_trans (by norm_num) psum561o2_250

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum561o2_floor
#print axioms CriticalLinePhasor.DVP.psum561o2_250
end AxiomAudit
