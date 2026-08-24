import RequestProject.DVPCos1142o2Table

/-!
# The cosine partial-sum floor, `t = 1142/2` (N = 1000)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 1142/2` segment certificate. -/
def cos1142o2c (n : ℕ) : ℝ := Real.cos (((1142:ℕ):ℝ) * (Real.log n / 2))

theorem psum1142o2_11 : ((1719103/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos1142o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 11 - ((1719303/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum1142o2_12 : ((6483847/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos1142o2c k) + cos1142o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_11
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 12 - ((4373179/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_13 : ((21197953/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos1142o2c k) + cos1142o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_12
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 13 - ((8231259/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_14 : ((6515467/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos1142o2c k) + cos1142o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_13
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 14 - ((972983/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_15 : ((17061399/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos1142o2c k) + cos1142o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_14
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 15 - ((806193/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_16 : ((21946291/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos1142o2c k) + cos1142o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_15
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 16 - ((305337/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_17 : ((1360483/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos1142o2c k) + cos1142o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_16
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 17 - ((-9879507/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_18 : ((29175887/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos1142o2c k) + cos1142o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_17
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 18 - ((-1208797/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_19 : ((10254749/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos1142o2c k) + cos1142o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_18
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 19 - ((-8665389/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_20 : ((20849283/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos1142o2c k) + cos1142o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_19
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 20 - ((68157/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_21 : ((16505699/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos1142o2c k) + cos1142o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_20
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 21 - ((-542823/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_22 : ((12407519/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos1142o2c k) + cos1142o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_21
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 22 - ((8310339/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_23 : ((8559899/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos1142o2c k) + cos1142o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_22
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 23 - ((4712779/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_24 : ((38123483/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos1142o2c k) + cos1142o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_23
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 24 - ((3884887/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_25 : ((7057367/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos1142o2c k) + cos1142o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_24
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 25 - ((-1978603/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_26 : ((18376127/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos1142o2c k) + cos1142o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_25
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 26 - ((4261893/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_27 : ((6702607/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos1142o2c k) + cos1142o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_26
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 27 - ((-4970413/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_28 : ((31199077/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos1142o2c k) + cos1142o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_27
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 28 - ((4389649/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_29 : ((20586361/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos1142o2c k) + cos1142o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_28
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 29 - ((1994929/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_30 : ((1548109/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos1142o2c k) + cos1142o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_29
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 30 - ((4183883/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_31 : ((5853029/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos1142o2c k) + cos1142o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_30
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 31 - ((4495901/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_32 : ((17042983/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos1142o2c k) + cos1142o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_31
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 32 - ((4821321/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_33 : ((68407707/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos1142o2c k) + cos1142o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_32
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 33 - ((9471/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_34 : ((58624353/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos1142o2c k) + cos1142o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_33
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 34 - ((-4891177/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_35 : ((4167173/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos1142o2c k) + cos1142o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_34
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 35 - ((1610283/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_36 : ((61376373/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos1142o2c k) + cos1142o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_35
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 36 - ((-1059479/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_37 : ((33598669/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos1142o2c k) + cos1142o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_36
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 37 - ((1164393/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_38 : ((29137947/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos1142o2c k) + cos1142o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_37
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 38 - ((-2230111/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_39 : ((67457999/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos1142o2c k) + cos1142o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_38
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 39 - ((1836621/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_40 : ((34166479/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos1142o2c k) + cos1142o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_39
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 40 - ((875959/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_41 : ((29205241/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos1142o2c k) + cos1142o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_40
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 41 - ((-2480369/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_42 : ((53590341/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos1142o2c k) + cos1142o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_41
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 42 - ((-4819141/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_43 : ((28587387/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos1142o2c k) + cos1142o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_42
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 43 - ((3585433/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_44 : ((2036689/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos1142o2c k) + cos1142o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_43
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 44 - ((4000137/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_45 : ((74467621/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos1142o2c k) + cos1142o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_44
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 45 - ((9294573/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_46 : ((8369937/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos1142o2c k) + cos1142o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_45
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 46 - ((9232749/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_47 : ((45735321/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos1142o2c k) + cos1142o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_46
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 47 - ((485767/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_48 : ((9485507/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos1142o2c k) + cos1142o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_47
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 48 - ((846357/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_49 : ((90527483/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos1142o2c k) + cos1142o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_48
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 49 - ((-4326587/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_50 : ((80569497/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos1142o2c k) + cos1142o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_49
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 50 - ((-4978493/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_51 : ((1532659/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos1142o2c k) + cos1142o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_50
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 51 - ((-3935547/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_52 : ((85423759/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos1142o2c k) + cos1142o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_51
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 52 - ((8791809/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_53 : ((89109701/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos1142o2c k) + cos1142o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_52
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 53 - ((1843471/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_54 : ((79123943/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos1142o2c k) + cos1142o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_53
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 54 - ((-4992379/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_55 : ((4179473/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos1142o2c k) + cos1142o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_54
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 55 - ((4466517/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_56 : ((43744849/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos1142o2c k) + cos1142o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_55
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 56 - ((1950619/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_57 : ((78657553/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos1142o2c k) + cos1142o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_56
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 57 - ((-1766229/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_58 : ((22163751/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos1142o2c k) + cos1142o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_57
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 58 - ((9998451/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_59 : ((19818281/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos1142o2c k) + cos1142o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_58
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 59 - ((-117261/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_60 : ((21980333/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos1142o2c k) + cos1142o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_59
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 60 - ((1081151/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_61 : ((79339423/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos1142o2c k) + cos1142o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_60
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 61 - ((-8580909/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_62 : ((88552053/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos1142o2c k) + cos1142o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_61
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 62 - ((921363/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_63 : ((39306117/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos1142o2c k) + cos1142o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_62
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 63 - ((-9938819/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_64 : ((88097833/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos1142o2c k) + cos1142o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_63
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 64 - ((9486599/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_65 : ((81831541/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos1142o2c k) + cos1142o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_64
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 65 - ((-1566323/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_66 : ((81531151/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos1142o2c k) + cos1142o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_65
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 66 - ((-29939/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_67 : ((89161049/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos1142o2c k) + cos1142o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_66
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 67 - ((3815449/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_68 : ((7950297/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos1142o2c k) + cos1142o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_67
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 68 - ((-9657079/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_69 : ((81677367/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos1142o2c k) + cos1142o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_68
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 69 - ((2175397/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_70 : ((45017043/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos1142o2c k) + cos1142o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_69
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 70 - ((8357719/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_71 : ((82676191/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos1142o2c k) + cos1142o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_70
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 71 - ((-1471379/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_72 : ((38465409/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos1142o2c k) + cos1142o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_71
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 72 - ((-5744373/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_73 : ((2663739/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos1142o2c k) + cos1142o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_72
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 73 - ((830983/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_74 : ((91488463/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos1142o2c k) + cos1142o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_73
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 74 - ((1249963/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_75 : ((84997253/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos1142o2c k) + cos1142o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_74
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 75 - ((-649021/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_76 : ((75846399/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos1142o2c k) + cos1142o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_75
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 76 - ((-4574927/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_77 : ((76100491/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos1142o2c k) + cos1142o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_76
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 77 - ((63773/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_78 : ((3402289/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos1142o2c k) + cos1142o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_77
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 78 - ((4478867/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_79 : ((9368351/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos1142o2c k) + cos1142o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_78
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 79 - ((1725457/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_80 : ((23772781/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos1142o2c k) + cos1142o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_79
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 80 - ((704307/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_81 : ((44445109/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos1142o2c k) + cos1142o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_80
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 81 - ((-3099953/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_82 : ((39524519/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos1142o2c k) + cos1142o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_81
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 82 - ((-492009/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_83 : ((70083567/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos1142o2c k) + cos1142o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_82
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 83 - ((-8964471/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_84 : ((64800479/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos1142o2c k) + cos1142o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_83
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 84 - ((-660261/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_85 : ((15994591/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos1142o2c k) + cos1142o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_84
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 85 - ((-164223/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_86 : ((67056761/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos1142o2c k) + cos1142o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_85
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 86 - ((3079397/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_87 : ((9119527/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos1142o2c k) + cos1142o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_86
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 87 - ((1180091/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_88 : ((3224897/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos1142o2c k) + cos1142o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_87
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 88 - ((7667209/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_89 : ((22314583/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos1142o2c k) + cos1142o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_88
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 89 - ((8636907/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_90 : ((12292601/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos1142o2c k) + cos1142o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_89
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 90 - ((2270869/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_91 : ((53765019/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos1142o2c k) + cos1142o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_90
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 91 - ((919023/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_92 : ((116542627/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos1142o2c k) + cos1142o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_91
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 92 - ((9013589/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_93 : ((7814029/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos1142o2c k) + cos1142o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_92
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 93 - ((8482837/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_94 : ((16555867/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos1142o2c k) + cos1142o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_93
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 94 - ((463967/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_95 : ((3451433/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos1142o2c k) + cos1142o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_94
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 95 - ((701423/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_96 : ((17616501/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos1142o2c k) + cos1142o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_95
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 96 - ((359461/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_97 : ((140188303/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos1142o2c k) + cos1142o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_96
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 97 - ((-148541/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_98 : ((135383723/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos1142o2c k) + cos1142o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_97
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 98 - ((-240179/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_99 : ((127037707/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos1142o2c k) + cos1142o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_98
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 99 - ((-1043127/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_100 : ((914409/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos1142o2c k) + cos1142o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_99
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 100 - ((-1998471/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_101 : ((54291793/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos1142o2c k) + cos1142o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_100
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 101 - ((-4229883/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_102 : ((52572709/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos1142o2c k) + cos1142o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_101
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 102 - ((-214823/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_103 : ((21736389/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos1142o2c k) + cos1142o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_102
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 103 - ((3537527/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_104 : ((117715747/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos1142o2c k) + cos1142o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_103
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 104 - ((4517401/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_105 : ((992313/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos1142o2c k) + cos1142o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_104
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 105 - ((9301317/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_106 : ((2603959/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos1142o2c k) + cos1142o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_105
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 106 - ((1591443/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_107 : ((3114241/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos1142o2c k) + cos1142o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_106
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 107 - ((-562731/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_108 : ((114568653/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos1142o2c k) + cos1142o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_107
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 108 - ((-9999987/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_109 : ((109324719/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos1142o2c k) + cos1142o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_108
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 109 - ((-2621467/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_110 : ((114263357/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos1142o2c k) + cos1142o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_109
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 110 - ((2469819/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_111 : ((31060857/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos1142o2c k) + cos1142o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_110
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 111 - ((9981071/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_112 : ((127644553/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos1142o2c k) + cos1142o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_111
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 112 - ((27217/80000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_113 : ((60031183/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos1142o2c k) + cos1142o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_112
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 113 - ((-7581187/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_114 : ((27873593/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos1142o2c k) + cos1142o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_113
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 114 - ((-4283497/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_115 : ((57067839/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos1142o2c k) + cos1142o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_114
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 115 - ((1321153/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_116 : ((124128171/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos1142o2c k) + cos1142o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_115
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 116 - ((9993493/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_117 : ((6282503/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos1142o2c k) + cos1142o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_116
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 117 - ((1522889/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_118 : ((29024001/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos1142o2c k) + cos1142o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_117
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 118 - ((-298533/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_119 : ((14017893/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos1142o2c k) + cos1142o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_118
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 119 - ((-197593/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_120 : ((12104793/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos1142o2c k) + cos1142o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_119
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 120 - ((4452893/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_121 : ((25165439/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos1142o2c k) + cos1142o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_120
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 121 - ((956053/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_122 : ((58491199/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos1142o2c k) + cos1142o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_121
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 122 - ((-8843797/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_123 : ((22554387/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos1142o2c k) + cos1142o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_122
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 123 - ((-4209463/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_124 : ((122179657/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos1142o2c k) + cos1142o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_123
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 124 - ((4704361/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_125 : ((124357027/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos1142o2c k) + cos1142o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_124
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 125 - ((217837/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_126 : ((114372297/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos1142o2c k) + cos1142o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_125
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 126 - ((-998373/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_127 : ((28945459/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos1142o2c k) + cos1142o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_126
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 127 - ((1410539/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_128 : ((125084271/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos1142o2c k) + cos1142o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_127
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 128 - ((1860687/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_129 : ((119077677/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos1142o2c k) + cos1142o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_128
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 129 - ((-3002797/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_130 : ((7077383/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos1142o2c k) + cos1142o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_129
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 130 - ((-5838549/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_131 : ((61414623/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos1142o2c k) + cos1142o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_130
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 131 - ((4796059/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_132 : ((7624597/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos1142o2c k) + cos1142o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_131
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 132 - ((-417347/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_133 : ((56576413/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos1142o2c k) + cos1142o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_132
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 133 - ((-4419863/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_134 : ((30279581/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos1142o2c k) + cos1142o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_133
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 134 - ((3983249/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_135 : ((122927603/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos1142o2c k) + cos1142o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_134
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 135 - ((1810279/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_136 : ((56711369/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos1142o2c k) + cos1142o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_135
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 136 - ((-1900773/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_137 : ((15113101/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos1142o2c k) + cos1142o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_136
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 137 - ((748307/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_138 : ((15319047/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos1142o2c k) + cos1142o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_137
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 138 - ((206071/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_139 : ((14179601/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos1142o2c k) + cos1142o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_138
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 139 - ((-1139321/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_140 : ((24415161/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos1142o2c k) + cos1142o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_139
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 140 - ((8639997/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_141 : ((120870559/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos1142o2c k) + cos1142o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_140
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 141 - ((-602123/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_142 : ((14235783/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos1142o2c k) + cos1142o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_141
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 142 - ((-1396659/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_143 : ((61931171/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos1142o2c k) + cos1142o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_142
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 143 - ((4988539/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_144 : ((14710757/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos1142o2c k) + cos1142o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_143
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 144 - ((-3087643/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_145 : ((11624591/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos1142o2c k) + cos1142o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_144
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 145 - ((-719573/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_146 : ((24848927/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos1142o2c k) + cos1142o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_145
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 146 - ((319989/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_147 : ((114306793/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos1142o2c k) + cos1142o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_146
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 147 - ((-4968421/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_148 : ((30241257/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos1142o2c k) + cos1142o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_147
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 148 - ((1331847/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_149 : ((120712529/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos1142o2c k) + cos1142o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_148
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 149 - ((-251499/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_150 : ((22927771/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos1142o2c k) + cos1142o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_149
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 150 - ((-3036337/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_151 : ((124286929/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos1142o2c k) + cos1142o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_150
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 151 - ((4824537/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_152 : ((14366621/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos1142o2c k) + cos1142o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_151
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 152 - ((-9352961/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_153 : ((120631199/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos1142o2c k) + cos1142o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_152
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 153 - ((5699231/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_154 : ((30087281/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos1142o2c k) + cos1142o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_153
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 154 - ((-11243/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_155 : ((115326533/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos1142o2c k) + cos1142o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_154
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 155 - ((-5021591/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_156 : ((24806429/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos1142o2c k) + cos1142o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_155
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 156 - ((2176653/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_157 : ((114031409/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos1142o2c k) + cos1142o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_156
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 157 - ((-1249967/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_158 : ((61458159/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos1142o2c k) + cos1142o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_157
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 158 - ((8885909/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_159 : ((116997209/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos1142o2c k) + cos1142o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_158
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 159 - ((-5918109/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_160 : ((118933429/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos1142o2c k) + cos1142o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_159
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 160 - ((96861/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_161 : ((121125149/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos1142o2c k) + cos1142o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_160
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 161 - ((27409/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_162 : ((23070737/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos1142o2c k) + cos1142o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_161
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 162 - ((-180327/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_163 : ((61849303/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos1142o2c k) + cos1142o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_162
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 163 - ((8345921/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_164 : ((113967011/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos1142o2c k) + cos1142o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_163
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 164 - ((-1946119/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_165 : ((123919129/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos1142o2c k) + cos1142o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_164
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 165 - ((4976559/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_166 : ((143411/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos1142o2c k) + cos1142o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_165
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 166 - ((-9189329/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_167 : ((122419081/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos1142o2c k) + cos1142o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_166
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 167 - ((7691281/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_168 : ((14586031/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos1142o2c k) + cos1142o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_167
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 168 - ((-5729833/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_169 : ((120237707/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos1142o2c k) + cos1142o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_168
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 169 - ((3550459/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_170 : ((7430163/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos1142o2c k) + cos1142o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_169
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 170 - ((-1354099/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_171 : ((14770837/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos1142o2c k) + cos1142o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_170
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 171 - ((-22341/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_172 : ((120730737/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos1142o2c k) + cos1142o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_171
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 172 - ((2565041/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_173 : ((58289813/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos1142o2c k) + cos1142o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_172
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 173 - ((-4150111/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_174 : ((7627337/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos1142o2c k) + cos1142o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_173
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 174 - ((2729383/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_175 : ((115532687/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos1142o2c k) + cos1142o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_174
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 175 - ((-1300741/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_176 : ((614217/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos1142o2c k) + cos1142o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_175
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 176 - ((7311713/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_177 : ((57462609/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos1142o2c k) + cos1142o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_176
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 177 - ((-3958591/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_178 : ((123278567/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos1142o2c k) + cos1142o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_177
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 178 - ((8354349/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_179 : ((114622083/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos1142o2c k) + cos1142o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_178
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 179 - ((-2163871/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_180 : ((123467349/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos1142o2c k) + cos1142o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_179
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 180 - ((4423133/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_181 : ((14315033/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos1142o2c k) + cos1142o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_180
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 181 - ((-1789217/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_182 : ((61742437/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos1142o2c k) + cos1142o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_181
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 182 - ((896561/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_183 : ((57287841/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos1142o2c k) + cos1142o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_182
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 183 - ((-278381/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_184 : ((123343199/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos1142o2c k) + cos1142o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_183
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 184 - ((8768517/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_185 : ((114807757/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos1142o2c k) + cos1142o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_184
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 185 - ((-4267221/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_186 : ((6149679/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos1142o2c k) + cos1142o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_185
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 186 - ((8186823/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_187 : ((115290151/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos1142o2c k) + cos1142o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_186
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 187 - ((-7702429/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_188 : ((122342841/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos1142o2c k) + cos1142o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_187
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 188 - ((705369/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_189 : ((116127569/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos1142o2c k) + cos1142o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_188
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 189 - ((-48549/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_190 : ((97029/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos1142o2c k) + cos1142o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_189
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 190 - ((5159681/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_191 : ((117409937/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos1142o2c k) + cos1142o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_190
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 191 - ((-3875313/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_192 : ((119767157/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos1142o2c k) + cos1142o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_191
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 192 - ((117911/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_193 : ((119139543/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos1142o2c k) + cos1142o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_192
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 193 - ((-313307/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_194 : ((117862411/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos1142o2c k) + cos1142o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_193
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 194 - ((-319033/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_195 : ((121137913/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos1142o2c k) + cos1142o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_194
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 195 - ((1638251/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_196 : ((115870149/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos1142o2c k) + cos1142o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_195
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 196 - ((-1316691/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_197 : ((61487757/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos1142o2c k) + cos1142o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_196
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 197 - ((1421273/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_198 : ((14293271/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos1142o2c k) + cos1142o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_197
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 198 - ((-4314173/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_199 : ((123996259/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos1142o2c k) + cos1142o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_198
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 199 - ((9651091/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_200 : ((113996313/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos1142o2c k) + cos1142o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_199
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 200 - ((-4999473/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_201 : ((2470483/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos1142o2c k) + cos1142o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_200
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 201 - ((9528837/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_202 : ((57680833/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos1142o2c k) + cos1142o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_201
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 202 - ((-2040371/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_203 : ((30318861/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos1142o2c k) + cos1142o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_202
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 203 - ((2957389/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_204 : ((59173041/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos1142o2c k) + cos1142o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_203
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 204 - ((-1464181/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_205 : ((11782321/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos1142o2c k) + cos1142o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_204
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 205 - ((-32617/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_206 : ((12185597/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos1142o2c k) + cos1142o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_205
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 206 - ((25211/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_207 : ((114739683/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos1142o2c k) + cos1142o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_206
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 207 - ((-7115287/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_208 : ((123990233/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos1142o2c k) + cos1142o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_207
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 208 - ((185031/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_209 : ((113990159/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos1142o2c k) + cos1142o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_208
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 209 - ((-4999537/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_210 : ((61540141/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos1142o2c k) + cos1142o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_209
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 210 - ((9091123/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_211 : ((116544669/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos1142o2c k) + cos1142o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_210
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 211 - ((-6534613/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_212 : ((119213879/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos1142o2c k) + cos1142o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_211
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 212 - ((267021/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_213 : ((121044709/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos1142o2c k) + cos1142o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_212
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 213 - ((183183/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_214 : ((114981429/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos1142o2c k) + cos1142o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_213
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 214 - ((-151557/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_215 : ((62014193/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos1142o2c k) + cos1142o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_214
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 215 - ((9047957/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_216 : ((114040917/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos1142o2c k) + cos1142o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_215
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 216 - ((-9986469/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_217 : ((61266221/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos1142o2c k) + cos1142o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_216
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 217 - ((339701/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_218 : ((58876223/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos1142o2c k) + cos1142o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_217
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 218 - ((-1194749/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_219 : ((58725571/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos1142o2c k) + cos1142o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_218
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 219 - ((-18769/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_220 : ((1228487/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos1142o2c k) + cos1142o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_219
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 220 - ((2699279/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_221 : ((182139/16000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos1142o2c k) + cos1142o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_220
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 221 - ((-360433/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_222 : ((123769571/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos1142o2c k) + cos1142o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_221
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 222 - ((77607/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_223 : ((116059353/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos1142o2c k) + cos1142o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_222
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 223 - ((-3854609/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_224 : ((23790317/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos1142o2c k) + cos1142o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_223
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 224 - ((180827/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_225 : ((60974901/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos1142o2c k) + cos1142o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_224
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 225 - ((2999217/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_226 : ((114028819/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos1142o2c k) + cos1142o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_225
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 226 - ((-7919983/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_227 : ((7751331/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos1142o2c k) + cos1142o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_226
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 227 - ((9993477/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_228 : ((180847/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos1142o2c k) + cos1142o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_227
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 228 - ((-1034777/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_229 : ((59502789/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos1142o2c k) + cos1142o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_228
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 229 - ((1632249/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_230 : ((30540003/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos1142o2c k) + cos1142o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_229
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 230 - ((1577717/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_231 : ((22764821/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos1142o2c k) + cos1142o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_230
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 231 - ((-8334907/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_232 : ((123782901/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos1142o2c k) + cos1142o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_231
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 232 - ((2489949/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_233 : ((29160061/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos1142o2c k) + cos1142o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_232
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 233 - ((-7141657/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_234 : ((117630221/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos1142o2c k) + cos1142o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_233
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 234 - ((990977/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_235 : ((61668117/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos1142o2c k) + cos1142o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_234
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 235 - ((5707013/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_236 : ((14204683/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos1142o2c k) + cos1142o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_235
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 236 - ((-969777/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_237 : ((61251469/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos1142o2c k) + cos1142o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_236
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 237 - ((4433237/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_238 : ((23809621/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos1142o2c k) + cos1142o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_237
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 238 - ((-3453833/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_239 : ((115200873/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos1142o2c k) + cos1142o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_238
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 239 - ((-480779/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_240 : ((24867327/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos1142o2c k) + cos1142o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_239
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 240 - ((4568381/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_241 : ((114937859/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos1142o2c k) + cos1142o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_240
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 241 - ((-587361/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_242 : ((59619741/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos1142o2c k) + cos1142o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_241
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 242 - ((4302623/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_243 : ((24518773/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos1142o2c k) + cos1142o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_242
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 243 - ((3355383/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_244 : ((28377901/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos1142o2c k) + cos1142o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_243
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 244 - ((-9081261/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_245 : ((122818529/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos1142o2c k) + cos1142o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_244
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 245 - ((372317/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_246 : ((119100291/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos1142o2c k) + cos1142o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_245
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 246 - ((-1858619/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_247 : ((114801079/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos1142o2c k) + cos1142o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_246
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 247 - ((-1074553/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_248 : ((24875369/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos1142o2c k) + cos1142o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_247
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 248 - ((4788383/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_249 : ((57930153/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos1142o2c k) + cos1142o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_248
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 249 - ((-8515539/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_250 : ((58755721/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos1142o2c k) + cos1142o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_249
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 250 - ((206517/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_251 : ((61961701/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 251, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 251, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 250, cos1142o2c k) + cos1142o2c 251 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 250) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_250
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 251 - ((40081/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_251).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_252 : ((113922459/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 252, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 252, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 251, cos1142o2c k) + cos1142o2c 252 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 251) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_251
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 252 - ((-9999943/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_252).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_253 : ((120317343/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 253, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 253, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 252, cos1142o2c k) + cos1142o2c 253 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 252) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_252
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 253 - ((1598971/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_253).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_254 : ((122255471/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 254, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 254, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 253, cos1142o2c k) + cos1142o2c 254 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 253) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_253
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 254 - ((242391/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_254).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_255 : ((22674771/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 255, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 255, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 254, cos1142o2c k) + cos1142o2c 255 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 254) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_254
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 255 - ((-1110077/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_255).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_256 : ((61233191/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 256, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 256, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 255, cos1142o2c k) + cos1142o2c 256 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 255) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_255
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 256 - ((9093527/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_256).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_257 : ((120222297/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 257, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 257, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 256, cos1142o2c k) + cos1142o2c 257 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 256) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_256
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 257 - ((-448617/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_257).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_258 : ((113795343/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 258, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 258, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 257, cos1142o2c k) + cos1142o2c 258 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 257) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_257
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 258 - ((-3212977/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_258).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_259 : ((12377649/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 259, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 259, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 258, cos1142o2c k) + cos1142o2c 259 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 258) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_258
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 259 - ((9982147/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_259).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_260 : ((118380469/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 260, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 260, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 259, cos1142o2c k) + cos1142o2c 260 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 259) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_259
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 260 - ((-5395021/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_260).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_261 : ((22934439/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 261, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 261, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 260, cos1142o2c k) + cos1142o2c 261 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 260) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_260
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 261 - ((-1853637/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_261).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_262 : ((124401039/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 262, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 262, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 261, cos1142o2c k) + cos1142o2c 262 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 261) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_261
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 262 - ((2432461/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_262).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_263 : ((58485491/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 263, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 263, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 262, cos1142o2c k) + cos1142o2c 263 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 262) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_262
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 263 - ((-7429057/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_263).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_264 : ((7225149/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 264, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 264, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 263, cos1142o2c k) + cos1142o2c 264 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 263) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_263
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 264 - ((-683799/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_264).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_265 : ((155753/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 265, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 265, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 264, cos1142o2c k) + cos1142o2c 265 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 264) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_264
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 265 - ((1125127/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_265).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_266 : ((116024969/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 266, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 266, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 265, cos1142o2c k) + cos1142o2c 266 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 265) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_265
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 266 - ((-8576431/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_266).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_267 : ((116340311/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 267, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 267, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 266, cos1142o2c k) + cos1142o2c 267 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 266) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_266
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 267 - ((158171/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_267).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_268 : ((31154621/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 268, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 268, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 267, cos1142o2c k) + cos1142o2c 268 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 267) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_267
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 268 - ((8279173/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_268).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_269 : ((7217797/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 269, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 269, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 268, cos1142o2c k) + cos1142o2c 269 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 268) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_268
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 269 - ((-2283183/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_269).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_270 : ((11676431/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 270, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 270, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 269, cos1142o2c k) + cos1142o2c 270 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 269) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_269
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 270 - ((640279/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_270).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_271 : ((31152643/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 271, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 271, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 270, cos1142o2c k) + cos1142o2c 271 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 270) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_270
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 271 - ((3923631/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_271).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_272 : ((57643047/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 272, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 272, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 271, cos1142o2c k) + cos1142o2c 272 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 271) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_271
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 272 - ((-4661739/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_272).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_273 : ((4673021/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 273, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 273, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 272, cos1142o2c k) + cos1142o2c 273 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 272) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_272
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 273 - ((1540431/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_273).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_274 : ((124652379/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 274, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 274, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 273, cos1142o2c k) + cos1142o2c 274 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 273) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_273
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 274 - ((3913927/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_274).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_275 : ((115401641/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 275, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 275, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 274, cos1142o2c k) + cos1142o2c 275 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 274) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_274
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 275 - ((-4624869/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_275).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_276 : ((116518199/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 276, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 276, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 275, cos1142o2c k) + cos1142o2c 276 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 275) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_275
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 276 - ((558779/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_276).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_277 : ((124734653/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 277, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 277, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 276, cos1142o2c k) + cos1142o2c 277 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 276) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_276
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 277 - ((4108727/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_277).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_278 : ((115852683/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 278, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 278, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 277, cos1142o2c k) + cos1142o2c 278 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 277) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_277
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 278 - ((-888097/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_278).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_279 : ((57934983/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 279, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 279, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 278, cos1142o2c k) + cos1142o2c 279 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 278) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_278
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 279 - ((18283/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_279).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_280 : ((124766403/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 280, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 280, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 279, cos1142o2c k) + cos1142o2c 280 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 279) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_279
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 280 - ((8897437/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_280).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_281 : ((116696719/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 281, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 281, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 280, cos1142o2c k) + cos1142o2c 281 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 280) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_280
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 281 - ((-2017171/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_281).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_282 : ((11496113/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 282, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 282, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 281, cos1142o2c k) + cos1142o2c 282 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 281) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_281
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 282 - ((-1734589/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_282).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_283 : ((6229071/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 283, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 283, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 282, cos1142o2c k) + cos1142o2c 283 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 282) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_282
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 283 - ((962129/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_283).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_284 : ((117990801/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 284, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 284, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 283, cos1142o2c k) + cos1142o2c 284 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 283) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_283
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 284 - ((-6589619/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_284).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_285 : ((113956557/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 285, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 285, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 284, cos1142o2c k) + cos1142o2c 285 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 284) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_284
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 285 - ((-1008311/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_285).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_286 : ((123954563/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 286, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 286, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 285, cos1142o2c k) + cos1142o2c 286 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 285) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_285
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 286 - ((4999503/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_286).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_287 : ((119727487/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 287, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 287, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 286, cos1142o2c k) + cos1142o2c 287 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 286) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_286
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 287 - ((-1056519/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_287).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_288 : ((113138507/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 288, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 288, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 287, cos1142o2c k) + cos1142o2c 288 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 287) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_287
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 288 - ((-329399/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_288).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_289 : ((2453167/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 289, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 289, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 288, cos1142o2c k) + cos1142o2c 289 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 288) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_288
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 289 - ((9520843/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_289).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_290 : ((30437667/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 290, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 290, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 289, cos1142o2c k) + cos1142o2c 290 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 289) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_289
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 290 - ((-453341/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_290).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_291 : ((112905483/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 291, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 291, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 290, cos1142o2c k) + cos1142o2c 291 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 290) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_290
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 291 - ((-1768837/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_291).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_292 : ((24114221/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 292, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 292, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 291, cos1142o2c k) + cos1142o2c 292 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 291) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_291
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 292 - ((3833311/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_292).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_293 : ((7729761/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 293, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 293, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 292, cos1142o2c k) + cos1142o2c 293 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 292) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_292
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 293 - ((3106071/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_293).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_294 : ((56846237/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 294, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 294, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 293, cos1142o2c k) + cos1142o2c 294 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 293) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_293
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 294 - ((-4991351/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_294).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_295 : ((58916071/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 295, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 295, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 294, cos1142o2c k) + cos1142o2c 295 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 294) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_294
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 295 - ((1035167/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_295).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_296 : ((124880653/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 296, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 296, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 295, cos1142o2c k) + cos1142o2c 296 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 295) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_295
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 296 - ((7049511/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_296).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_297 : ((57889467/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 297, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 297, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 296, cos1142o2c k) + cos1142o2c 297 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 296) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_296
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 297 - ((-9100719/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_297).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_298 : ((57495211/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 298, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 298, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 297, cos1142o2c k) + cos1142o2c 298 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 297) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_297
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 298 - ((-98439/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_298).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_299 : ((124644843/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 299, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 299, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 298, cos1142o2c k) + cos1142o2c 299 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 298) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_298
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 299 - ((9655421/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_299).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_300 : ((3718929/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 300, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 300, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 299, cos1142o2c k) + cos1142o2c 300 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 299) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_299
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 300 - ((-1127623/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_300).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_301 : ((56506669/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 301, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 301, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 300, cos1142o2c k) + cos1142o2c 301 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 300) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_300
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 301 - ((-599139/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_301).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_302 : ((122506801/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 302, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 302, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 301, cos1142o2c k) + cos1142o2c 302 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 301) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_301
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 302 - ((9494463/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_302).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_303 : ((24506187/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 303, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 303, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 302, cos1142o2c k) + cos1142o2c 303 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 302) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_302
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 303 - ((12567/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_303).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_304 : ((56500377/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 304, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 304, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 303, cos1142o2c k) + cos1142o2c 304 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 303) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_303
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 304 - ((-9529181/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_304).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_305 : ((118748459/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 305, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 305, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 304, cos1142o2c k) + cos1142o2c 305 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 304) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_304
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 305 - ((1149741/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_305).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_306 : ((124878907/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 306, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 306, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 305, cos1142o2c k) + cos1142o2c 306 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 305) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_305
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 306 - ((766431/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_306).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_307 : ((57773507/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 307, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 307, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 306, cos1142o2c k) + cos1142o2c 307 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 306) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_306
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 307 - ((-9330893/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_307).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_308 : ((114729011/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 308, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 308, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 307, cos1142o2c k) + cos1142o2c 308 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 307) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_307
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 308 - ((-817003/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_308).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_309 : ((124532023/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 309, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 309, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 308, cos1142o2c k) + cos1142o2c 309 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 308) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_308
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 309 - ((2451003/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_309).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_310 : ((7498791/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 310, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 310, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 309, cos1142o2c k) + cos1142o2c 310 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 309) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_309
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 310 - ((-4550367/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_310).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_311 : ((56299633/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 311, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 311, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 310, cos1142o2c k) + cos1142o2c 311 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 310) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_310
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 311 - ((-738039/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_311).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_312 : ((121028419/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 312, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 312, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 311, cos1142o2c k) + cos1142o2c 312 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 311) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_311
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 312 - ((8430153/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_312).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_313 : ((62046277/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 313, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 313, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 312, cos1142o2c k) + cos1142o2c 313 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 312) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_312
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 313 - ((613027/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_313).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_314 : ((57055061/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 314, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 314, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 313, cos1142o2c k) + cos1142o2c 314 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 313) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_313
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 314 - ((-1247679/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_314).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_315 : ((57968709/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 315, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 315, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 314, cos1142o2c k) + cos1142o2c 315 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 314) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_314
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 315 - ((228537/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_315).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_316 : ((125055407/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 316, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 316, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 315, cos1142o2c k) + cos1142o2c 316 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 315) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_315
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 316 - ((9118989/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_316).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_317 : ((118953403/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 317, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 317, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 316, cos1142o2c k) + cos1142o2c 317 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 316) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_316
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 317 - ((-1525251/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_317).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_318 : ((56305161/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 318, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 318, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 317, cos1142o2c k) + cos1142o2c 318 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 317) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_317
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 318 - ((-6342081/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_318).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_319 : ((60773871/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 319, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 319, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 318, cos1142o2c k) + cos1142o2c 319 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 318) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_318
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 319 - ((446921/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_319).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_320 : ((968809/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 320, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 320, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 319, cos1142o2c k) + cos1142o2c 320 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 319) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_319
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 320 - ((246081/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_320).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_321 : ((57006847/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 321, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 321, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 320, cos1142o2c k) + cos1142o2c 321 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 320) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_320
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 321 - ((-4996429/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_321).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_322 : ((28919833/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 322, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 322, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 321, cos1142o2c k) + cos1142o2c 322 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 321) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_321
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 322 - ((833319/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_322).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_323 : ((62505837/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 323, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 323, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 322, cos1142o2c k) + cos1142o2c 323 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 322) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_322
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 323 - ((4666671/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_323).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_324 : ((119686241/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 324, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 324, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 323, cos1142o2c k) + cos1142o2c 324 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 323) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_323
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 324 - ((-5324433/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_324).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_325 : ((112370273/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 325, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 325, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 324, cos1142o2c k) + cos1142o2c 325 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 324) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_324
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 325 - ((-914371/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_325).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_326 : ((60203803/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 326, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 326, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 325, cos1142o2c k) + cos1142o2c 326 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 325) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_325
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 326 - ((8038333/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_326).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_327 : ((31209331/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 327, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 327, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 326, cos1142o2c k) + cos1142o2c 327 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 326) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_326
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 327 - ((2215359/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_327).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_328 : ((57621643/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 328, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 328, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 327, cos1142o2c k) + cos1142o2c 328 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 327) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_327
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 328 - ((-4796519/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_328).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_329 : ((114056231/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 329, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 329, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 328, cos1142o2c k) + cos1142o2c 329 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 328) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_328
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 329 - ((-237211/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_329).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_330 : ((124045881/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 330, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 330, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 329, cos1142o2c k) + cos1142o2c 330 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 329) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_329
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 330 - ((199813/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_330).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_331 : ((61028483/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 331, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 331, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 330, cos1142o2c k) + cos1142o2c 331 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 330) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_330
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 331 - ((-397583/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_331).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_332 : ((2253369/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 332, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 332, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 331, cos1142o2c k) + cos1142o2c 332 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 331) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_331
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 332 - ((-2346879/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_332).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_333 : ((117446719/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 333, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 333, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 332, cos1142o2c k) + cos1142o2c 333 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 332) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_332
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 333 - ((4779269/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_333).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_334 : ((5018753/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 334, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 334, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 333, cos1142o2c k) + cos1142o2c 334 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 333) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_333
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 334 - ((4011553/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_334).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_335 : ((59232099/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 335, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 335, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 334, cos1142o2c k) + cos1142o2c 335 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 334) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_334
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 335 - ((-7003627/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_335).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_336 : ((56151167/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 336, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 336, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 335, cos1142o2c k) + cos1142o2c 336 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 335) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_335
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 336 - ((-192527/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_336).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_337 : ((120890413/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 337, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 337, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 336, cos1142o2c k) + cos1142o2c 337 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 336) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_336
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 337 - ((8589079/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_337).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_338 : ((124936347/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 338, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 338, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 337, cos1142o2c k) + cos1142o2c 338 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 337) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_337
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 338 - ((2023467/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_338).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_339 : ((115383563/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 339, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 339, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 338, cos1142o2c k) + cos1142o2c 339 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 338) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_338
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 339 - ((-1193973/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_339).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_340 : ((28374843/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 340, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 340, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 339, cos1142o2c k) + cos1142o2c 340 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 339) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_339
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 340 - ((-1883191/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_340).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_341 : ((123463669/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 341, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 341, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 340, cos1142o2c k) + cos1142o2c 341 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 340) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_340
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 341 - ((9965297/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_341).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_342 : ((123283387/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 342, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 342, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 341, cos1142o2c k) + cos1142o2c 342 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 341) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_341
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 342 - ((-89641/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_342).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_343 : ((113347617/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 343, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 343, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 342, cos1142o2c k) + cos1142o2c 343 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 342) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_342
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 343 - ((-993477/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_343).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_344 : ((14423741/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 344, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 344, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 343, cos1142o2c k) + cos1142o2c 344 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 343) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_343
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 344 - ((2043311/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_344).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_345 : ((124964237/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 345, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 345, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 344, cos1142o2c k) + cos1142o2c 345 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 344) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_344
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 345 - ((9575309/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_345).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_346 : ((12130673/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 346, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 346, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 345, cos1142o2c k) + cos1142o2c 346 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 345) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_345
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 346 - ((-3656507/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_346).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_347 : ((56153769/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 347, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 347, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 346, cos1142o2c k) + cos1142o2c 347 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 346) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_346
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 347 - ((-562387/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_347).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_348 : ((117308383/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 348, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 348, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 347, cos1142o2c k) + cos1142o2c 348 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 347) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_347
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 348 - ((1000369/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_348).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_349 : ((25121687/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 349, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 349, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 348, cos1142o2c k) + cos1142o2c 349 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 348) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_348
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 349 - ((2075263/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_349).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_350 : ((59760107/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 350, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 350, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 349, cos1142o2c k) + cos1142o2c 350 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 349) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_349
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 350 - ((-6087221/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_350).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_351 : ((55976849/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 351, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 351, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 350, cos1142o2c k) + cos1142o2c 351 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 350) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_350
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 351 - ((-1891379/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_351).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_352 : ((118888263/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 352, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 352, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 351, cos1142o2c k) + cos1142o2c 352 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 351) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_351
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 352 - ((1387113/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_352).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_353 : ((31435599/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 353, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 353, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 352, cos1142o2c k) + cos1142o2c 353 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 352) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_352
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 353 - ((6855133/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_353).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_354 : ((118163013/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 354, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 354, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 353, cos1142o2c k) + cos1142o2c 354 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 353) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_353
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 354 - ((-7578383/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_354).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_355 : ((4477797/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 355, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 355, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 354, cos1142o2c k) + cos1142o2c 355 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 354) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_354
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 355 - ((-48571/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_355).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_356 : ((1199917/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 356, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 356, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 355, cos1142o2c k) + cos1142o2c 356 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 355) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_355
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 356 - ((321911/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_356).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_357 : ((15709417/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 357, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 357, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 356, cos1142o2c k) + cos1142o2c 357 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 356) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_356
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 357 - ((1421159/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_357).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_358 : ((23460007/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 358, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 358, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 357, cos1142o2c k) + cos1142o2c 358 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 357) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_357
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 358 - ((-8374301/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_358).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_359 : ((56009359/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 359, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 359, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 358, cos1142o2c k) + cos1142o2c 359 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 358) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_358
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 359 - ((-5280317/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_359).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_360 : ((942198/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 360, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 360, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 359, cos1142o2c k) + cos1142o2c 360 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 359) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_359
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 360 - ((4291813/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_360).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_361 : ((31404473/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 361, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 361, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 360, cos1142o2c k) + cos1142o2c 361 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 360) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_360
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 361 - ((1254387/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_361).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_362 : ((116923167/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 362, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 362, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 361, cos1142o2c k) + cos1142o2c 362 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 361) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_361
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 362 - ((-347749/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_362).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_363 : ((112018583/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 363, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 363, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 362, cos1142o2c k) + cos1142o2c 363 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 362) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_362
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 363 - ((-153237/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_363).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_364 : ((120732913/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 364, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 364, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 363, cos1142o2c k) + cos1142o2c 364 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 363) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_363
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 364 - ((871533/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_364).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_365 : ((62836173/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 365, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 365, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 364, cos1142o2c k) + cos1142o2c 365 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 364) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_364
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 365 - ((4940433/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_365).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_366 : ((117019483/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 366, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 366, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 365, cos1142o2c k) + cos1142o2c 366 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 365) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_365
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 366 - ((-8651863/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_366).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_367 : ((27973363/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 367, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 367, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 366, cos1142o2c k) + cos1142o2c 367 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 366) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_366
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 367 - ((-5125031/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_367).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_368 : ((12039069/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 368, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 368, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 367, cos1142o2c k) + cos1142o2c 368 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 367) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_367
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 368 - ((4249119/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_368).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_369 : ((62919971/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 369, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 369, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 368, cos1142o2c k) + cos1142o2c 369 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 368) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_368
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 369 - ((1362563/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_369).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_370 : ((29399027/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 370, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 370, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 369, cos1142o2c k) + cos1142o2c 370 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 369) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_369
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 370 - ((-4121417/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_370).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_371 : ((111691317/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 371, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 371, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 370, cos1142o2c k) + cos1142o2c 371 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 370) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_370
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 371 - ((-5903791/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_371).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_372 : ((119557591/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 372, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 372, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 371, cos1142o2c k) + cos1142o2c 372 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 371) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_371
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 372 - ((3933637/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_372).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_373 : ((7876449/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 373, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 373, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 372, cos1142o2c k) + cos1142o2c 373 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 372) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_372
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 373 - ((6466593/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_373).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_374 : ((14834129/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 374, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 374, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 373, cos1142o2c k) + cos1142o2c 374 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 373) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_373
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 374 - ((-229661/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_374).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_375 : ((111559287/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 375, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 375, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 374, cos1142o2c k) + cos1142o2c 375 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 374) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_374
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 375 - ((-1422549/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_375).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_376 : ((59110959/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 376, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 376, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 375, cos1142o2c k) + cos1142o2c 376 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 375) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_375
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 376 - ((6663631/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_376).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_377 : ((63013681/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 377, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 377, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 376, cos1142o2c k) + cos1142o2c 377 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 376) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_376
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 377 - ((1951611/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_377).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_378 : ((120241409/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 378, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 378, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 377, cos1142o2c k) + cos1142o2c 378 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 377) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_377
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 378 - ((-5784953/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_378).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_379 : ((111739959/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 379, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 379, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 378, cos1142o2c k) + cos1142o2c 379 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 378) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_378
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 379 - ((-170009/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_379).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_380 : ((116432103/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 380, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 380, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 379, cos1142o2c k) + cos1142o2c 380 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 379) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_379
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 380 - ((586643/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_380).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_381 : ((25113731/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 381, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 381, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 380, cos1142o2c k) + cos1142o2c 381 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 380) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_380
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 381 - ((571097/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_381).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_382 : ((30548001/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 382, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 382, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 381, cos1142o2c k) + cos1142o2c 382 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 381) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_381
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 382 - ((-3375651/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_382).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_383 : ((112543487/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 383, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 383, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 382, cos1142o2c k) + cos1142o2c 383 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 382) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_382
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 383 - ((-9647517/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_383).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_384 : ((114376459/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 384, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 384, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 383, cos1142o2c k) + cos1142o2c 384 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 383) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_383
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 384 - ((458493/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_384).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_385 : ((31081697/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 385, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 385, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 384, cos1142o2c k) + cos1142o2c 385 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 384) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_384
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 385 - ((9951329/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_385).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_386 : ((31058749/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 386, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 386, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 385, cos1142o2c k) + cos1142o2c 386 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 385) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_385
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 386 - ((-11349/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_386).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_387 : ((22853913/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 387, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 387, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 386, cos1142o2c k) + cos1142o2c 387 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 386) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_386
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 387 - ((-9964431/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_387).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_388 : ((4498507/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 388, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 388, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 387, cos1142o2c k) + cos1142o2c 388 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 387) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_387
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 388 - ((-180589/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_388).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_389 : ((24412987/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 389, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 389, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 388, cos1142o2c k) + cos1142o2c 389 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 388) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_388
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 389 - ((480163/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_389).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_390 : ((31460529/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 390, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 390, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 389, cos1142o2c k) + cos1142o2c 390 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 389) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_389
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 390 - ((3778181/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_390).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_391 : ((11704627/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 391, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 391, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 390, cos1142o2c k) + cos1142o2c 391 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 390) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_390
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 391 - ((-4397423/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_391).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_392 : ((111330463/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 392, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 392, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 391, cos1142o2c k) + cos1142o2c 392 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 391) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_391
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 392 - ((-5714807/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_392).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_393 : ((5940951/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 393, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 393, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 392, cos1142o2c k) + cos1142o2c 393 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 392) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_392
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 393 - ((7489557/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_393).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_394 : ((126291261/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 394, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 394, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 393, cos1142o2c k) + cos1142o2c 394 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 393) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_393
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 394 - ((7473241/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_394).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_395 : ((120616259/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 395, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 395, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 394, cos1142o2c k) + cos1142o2c 395 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 394) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_394
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 395 - ((-2837001/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_395).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_396 : ((111728387/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 396, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 396, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 395, cos1142o2c k) + cos1142o2c 396 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 395) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_395
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 396 - ((-1110859/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_396).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_397 : ((57557443/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 397, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 397, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 396, cos1142o2c k) + cos1142o2c 397 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 396) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_396
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 397 - ((3387499/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_397).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_398 : ((124891449/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 398, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 398, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 397, cos1142o2c k) + cos1142o2c 398 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 397) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_397
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 398 - ((9777563/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_398).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_399 : ((62078631/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 399, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 399, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 398, cos1142o2c k) + cos1142o2c 399 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 398) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_398
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 399 - ((-733187/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_399).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_400 : ((114179469/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 400, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 400, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 399, cos1142o2c k) + cos1142o2c 400 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 399) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_399
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 400 - ((-9976793/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_400).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_401 : ((14007813/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 401, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 401, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 400, cos1142o2c k) + cos1142o2c 401 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 400) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_400
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 401 - ((-423193/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_401).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_402 : ((60706931/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 402, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 402, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 401, cos1142o2c k) + cos1142o2c 402 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 401) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_401
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 402 - ((4676179/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_402).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_403 : ((31582417/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 403, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 403, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 402, cos1142o2c k) + cos1142o2c 403 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 402) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_402
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 403 - ((2458403/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_403).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_404 : ((7405539/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 404, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 404, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 403, cos1142o2c k) + cos1142o2c 404 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 403) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_403
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 404 - ((-1960011/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_404).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_405 : ((55557951/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 405, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 405, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 404, cos1142o2c k) + cos1142o2c 405 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 404) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_404
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 405 - ((-3685861/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_405).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_406 : ((116589011/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 406, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 406, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 405, cos1142o2c k) + cos1142o2c 406 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 405) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_405
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 406 - ((5474109/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_406).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_407 : ((62873347/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 407, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 407, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 406, cos1142o2c k) + cos1142o2c 407 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 406) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_406
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 407 - ((9158683/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_407).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_408 : ((6166701/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 408, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 408, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 407, cos1142o2c k) + cos1142o2c 408 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 407) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_407
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 408 - ((-1205837/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_408).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_409 : ((56678959/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 409, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 409, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 408, cos1142o2c k) + cos1142o2c 409 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 408) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_408
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 409 - ((-4987551/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_409).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_410 : ((14037569/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 410, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 410, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 409, cos1142o2c k) + cos1142o2c 410 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 409) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_409
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 410 - ((-528183/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_410).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_411 : ((121894431/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 411, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 411, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 410, cos1142o2c k) + cos1142o2c 411 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 410) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_410
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 411 - ((9594879/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_411).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_412 : ((31602957/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 412, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 412, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 411, cos1142o2c k) + cos1142o2c 412 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 411) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_411
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 412 - ((4518397/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_412).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_413 : ((59241407/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 413, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 413, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 412, cos1142o2c k) + cos1142o2c 413 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 412) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_412
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 413 - ((-3964007/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_413).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_414 : ((27750037/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 414, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 414, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 413, cos1142o2c k) + cos1142o2c 414 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 413) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_413
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 414 - ((-3740833/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_414).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_415 : ((116074313/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 415, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 415, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 414, cos1142o2c k) + cos1142o2c 415 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 414) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_414
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 415 - ((1015033/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_415).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_416 : ((15689377/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 416, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 416, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 415, cos1142o2c k) + cos1142o2c 416 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 415) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_415
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 416 - ((9441703/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_416).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_417 : ((24831831/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 417, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 417, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 416, cos1142o2c k) + cos1142o2c 417 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 416) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_416
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 417 - ((-1354861/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_417).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_418 : ((28545187/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 418, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 418, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 417, cos1142o2c k) + cos1142o2c 418 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 417) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_417
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 418 - ((-9977407/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_418).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_419 : ((27869379/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 419, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 419, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 418, cos1142o2c k) + cos1142o2c 419 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 418) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_418
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 419 - ((-337779/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_419).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_420 : ((120331311/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 420, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 420, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 419, cos1142o2c k) + cos1142o2c 420 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 419) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_419
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 420 - ((1770959/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_420).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_421 : ((126743167/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 421, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 421, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 420, cos1142o2c k) + cos1142o2c 421 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 420) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_420
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 421 - ((801607/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_421).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_422 : ((120622659/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 422, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 422, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 421, cos1142o2c k) + cos1142o2c 422 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 421) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_421
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 422 - ((-1529877/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_422).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_423 : ((13946327/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 423, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 423, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 422, cos1142o2c k) + cos1142o2c 423 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 422) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_422
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 423 - ((-9051043/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_423).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_424 : ((56859737/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 424, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 424, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 423, cos1142o2c k) + cos1142o2c 424 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 423) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_423
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 424 - ((1074929/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_424).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_425 : ((30929517/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 425, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 425, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 424, cos1142o2c k) + cos1142o2c 425 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 424) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_424
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 425 - ((4999797/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_425).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_426 : ((12607317/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 426, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 426, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 425, cos1142o2c k) + cos1142o2c 426 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 425) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_425
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 426 - ((1178051/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_426).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_427 : ((29288917/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 427, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 427, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 426, cos1142o2c k) + cos1142o2c 427 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 426) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_426
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 427 - ((-4458251/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_427).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_428 : ((110674411/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 428, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 428, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 427, cos1142o2c k) + cos1142o2c 428 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 427) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_427
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 428 - ((-6480257/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_428).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_429 : ((58272767/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 429, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 429, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 428, cos1142o2c k) + cos1142o2c 429 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 428) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_428
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 429 - ((5872123/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_429).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_430 : ((7862983/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 430, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 430, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 429, cos1142o2c k) + cos1142o2c 430 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 429) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_429
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 430 - ((4631597/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_430).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_431 : ((24878703/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 431, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 431, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 430, cos1142o2c k) + cos1142o2c 431 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 430) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_430
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 431 - ((-1413213/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_431).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_432 : ((57224167/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 432, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 432, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 431, cos1142o2c k) + cos1142o2c 432 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 431) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_431
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 432 - ((-9944181/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_432).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_433 : ((4438393/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 433, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 433, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 432, cos1142o2c k) + cos1142o2c 433 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 432) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_432
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 433 - ((-3487509/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_433).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_434 : ((29789039/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 434, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 434, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 433, cos1142o2c k) + cos1142o2c 434 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 433) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_433
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 434 - ((8197331/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_434).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_435 : ((63387887/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 435, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 435, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 434, cos1142o2c k) + cos1142o2c 435 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 434) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_434
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 435 - ((3810309/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_435).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_436 : ((24494691/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 436, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 436, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 435, cos1142o2c k) + cos1142o2c 436 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 435) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_435
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 436 - ((-4301319/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_436).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_437 : ((112637521/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 437, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 437, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 436, cos1142o2c k) + cos1142o2c 437 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 436) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_436
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 437 - ((-4917467/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_437).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_438 : ((22360183/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 438, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 438, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 437, cos1142o2c k) + cos1142o2c 438 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 437) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_437
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 438 - ((-417803/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_438).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_439 : ((121185769/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 439, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 439, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 438, cos1142o2c k) + cos1142o2c 439 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 438) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_438
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 439 - ((4692927/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_439).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_440 : ((15878341/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 440, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 440, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 439, cos1142o2c k) + cos1142o2c 440 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 439) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_439
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 440 - ((5841959/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_440).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_441 : ((60398779/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 441, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 441, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 440, cos1142o2c k) + cos1142o2c 441 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 440) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_440
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 441 - ((-622817/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_441).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_442 : ((111566041/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 442, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 442, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 441, cos1142o2c k) + cos1142o2c 442 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 441) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_441
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 442 - ((-9230517/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_442).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_443 : ((112707177/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 443, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 443, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 442, cos1142o2c k) + cos1142o2c 443 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 442) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_442
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 443 - ((142767/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_443).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_444 : ((122563977/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 444, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 444, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 443, cos1142o2c k) + cos1142o2c 444 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 443) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_443
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 444 - ((49289/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_444).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_445 : ((126958137/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 445, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 445, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 444, cos1142o2c k) + cos1142o2c 445 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 444) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_444
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 445 - ((109879/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_445).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_446 : ((59800189/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 446, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 446, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 445, cos1142o2c k) + cos1142o2c 446 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 445) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_445
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 446 - ((-7356759/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_446).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_447 : ((110995057/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 447, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 447, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 446, cos1142o2c k) + cos1142o2c 447 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 446) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_446
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 447 - ((-8604321/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_447).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_448 : ((113370079/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 448, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 448, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 447, cos1142o2c k) + cos1142o2c 448 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 447) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_447
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 448 - ((1188011/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_448).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_449 : ((123352381/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 449, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 449, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 448, cos1142o2c k) + cos1142o2c 449 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 448) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_448
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 449 - ((4991651/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_449).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_450 : ((63429061/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 450, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 450, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 449, cos1142o2c k) + cos1142o2c 450 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 449) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_449
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 450 - ((3506741/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_450).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_451 : ((23793381/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 451, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 451, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 450, cos1142o2c k) + cos1142o2c 451 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 450) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_450
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 451 - ((-7890217/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_451).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_452 : ((110729919/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 452, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 452, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 451, cos1142o2c k) + cos1142o2c 452 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 451) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_451
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 452 - ((-4117993/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_452).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_453 : ((113628501/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 453, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 453, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 452, cos1142o2c k) + cos1142o2c 453 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 452) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_452
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 453 - ((1449791/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_453).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_454 : ((3090649/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 454, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 454, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 453, cos1142o2c k) + cos1142o2c 454 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 453) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_453
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 454 - ((9998459/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_454).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_455 : ((25376829/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 455, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 455, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 454, cos1142o2c k) + cos1142o2c 455 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 454) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_454
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 455 - ((651837/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_455).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_456 : ((23783501/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 456, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 456, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 455, cos1142o2c k) + cos1142o2c 456 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 455) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_455
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 456 - ((-199141/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_456).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_457 : ((110672021/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 457, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 457, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 456, cos1142o2c k) + cos1142o2c 457 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 456) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_456
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 457 - ((-2061121/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_457).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_458 : ((113423667/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 458, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 458, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 457, cos1142o2c k) + cos1142o2c 458 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 457) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_457
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 458 - ((1376323/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_458).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_459 : ((123411847/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 459, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 459, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 458, cos1142o2c k) + cos1142o2c 459 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 458) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_458
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 459 - ((499459/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_459).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_460 : ((127070869/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 460, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 460, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 459, cos1142o2c k) + cos1142o2c 460 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 459) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_459
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 460 - ((1830011/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_460).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_461 : ((119457139/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 461, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 461, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 460, cos1142o2c k) + cos1142o2c 461 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 460) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_460
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 461 - ((-761273/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_461).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_462 : ((110836779/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 462, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 462, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 461, cos1142o2c k) + cos1142o2c 462 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 461) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_461
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 462 - ((-53871/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_462).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_463 : ((56389373/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 463, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 463, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 462, cos1142o2c k) + cos1142o2c 463 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 462) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_462
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 463 - ((1942967/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_463).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_464 : ((61337607/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 464, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 464, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 463, cos1142o2c k) + cos1142o2c 464 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 463) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_463
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 464 - ((2474367/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_464).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_465 : ((2546693/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 465, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 465, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 464, cos1142o2c k) + cos1142o2c 465 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 464) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_464
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 465 - ((1165109/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_465).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_466 : ((120577427/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 466, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 466, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 465, cos1142o2c k) + cos1142o2c 466 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 465) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_465
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 466 - ((-6756223/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_466).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_467 : ((111346491/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 467, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 467, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 466, cos1142o2c k) + cos1142o2c 467 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 466) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_466
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 467 - ((-576871/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_467).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_468 : ((111801137/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 468, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 468, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 467, cos1142o2c k) + cos1142o2c 468 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 467) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_467
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 468 - ((227823/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_468).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_469 : ((121334343/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 469, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 469, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 468, cos1142o2c k) + cos1142o2c 469 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 468) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_468
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 469 - ((4767103/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_469).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_470 : ((127472723/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 470, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 470, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 469, cos1142o2c k) + cos1142o2c 470 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 469) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_469
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 470 - ((306969/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_470).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_471 : ((122223013/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 471, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 471, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 470, cos1142o2c k) + cos1142o2c 471 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 470) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_470
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 471 - ((-524871/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_471).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_472 : ((112407299/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 472, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 472, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 471, cos1142o2c k) + cos1142o2c 472 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 471) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_471
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 472 - ((-4907357/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_472).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_473 : ((1107191/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 473, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 473, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 472, cos1142o2c k) + cos1142o2c 473 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 472) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_472
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 473 - ((-1687199/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_473).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_474 : ((11932397/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 474, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 474, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 473, cos1142o2c k) + cos1142o2c 474 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 473) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_473
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 474 - ((860587/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_474).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_475 : ((127167347/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 475, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 475, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 474, cos1142o2c k) + cos1142o2c 475 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 474) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_474
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 475 - ((7844377/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_475).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_476 : ((12422047/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 476, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 476, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 475, cos1142o2c k) + cos1142o2c 476 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 475) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_475
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 476 - ((-2945877/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_476).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_477 : ((7140403/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 477, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 477, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 476, cos1142o2c k) + cos1142o2c 477 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 476) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_476
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 477 - ((-4986511/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_477).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_478 : ((10991/1000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 478, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 478, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 477, cos1142o2c k) + cos1142o2c 478 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 477) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_477
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 478 - ((-541931/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_478).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_479 : ((58343819/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 479, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 479, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 478, cos1142o2c k) + cos1142o2c 479 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 478) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_478
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 479 - ((3389319/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_479).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_480 : ((12602811/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 480, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 480, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 479, cos1142o2c k) + cos1142o2c 480 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 479) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_479
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 480 - ((291921/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_480).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_481 : ((1577533/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 481, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 481, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 480, cos1142o2c k) + cos1142o2c 481 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 480) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_480
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 481 - ((17553/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_481).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_482 : ((117000561/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 482, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 482, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 481, cos1142o2c k) + cos1142o2c 482 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 481) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_481
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 482 - ((-9201079/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_482).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_483 : ((2747429/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 483, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 483, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 482, cos1142o2c k) + cos1142o2c 483 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 482) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_482
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 483 - ((-7102401/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_483).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_484 : ((28427193/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 484, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 484, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 483, cos1142o2c k) + cos1142o2c 484 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 483) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_483
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 484 - ((953153/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_484).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_485 : ((24741553/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 485, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 485, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 484, cos1142o2c k) + cos1142o2c 485 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 484) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_484
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 485 - ((9999993/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_485).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_486 : ((31890557/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 486, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 486, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 485, cos1142o2c k) + cos1142o2c 486 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 485) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_485
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 486 - ((3855463/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_486).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_487 : ((24108689/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 487, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 487, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 486, cos1142o2c k) + cos1142o2c 487 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 486) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_486
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 487 - ((-7017783/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_487).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_488 : ((55624913/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 488, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 488, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 487, cos1142o2c k) + cos1142o2c 488 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 487) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_487
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 488 - ((-9292619/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_488).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_489 : ((111013121/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 489, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 489, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 488, cos1142o2c k) + cos1142o2c 489 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 488) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_488
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 489 - ((-47141/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_489).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_490 : ((3753457/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 490, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 490, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 489, cos1142o2c k) + cos1142o2c 490 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 489) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_489
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 490 - ((9098503/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_490).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_491 : ((12751933/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 491, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 491, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 490, cos1142o2c k) + cos1142o2c 491 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 490) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_490
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 491 - ((3704853/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_491).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_492 : ((31076001/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 492, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 492, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 491, cos1142o2c k) + cos1142o2c 492 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 491) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_491
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 492 - ((-1607163/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_492).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_493 : ((28584607/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 493, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 493, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 492, cos1142o2c k) + cos1142o2c 493 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 492) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_492
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 493 - ((-311393/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_493).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_494 : ((21912291/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 494, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 494, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 493, cos1142o2c k) + cos1142o2c 494 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 493) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_493
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 494 - ((-4775973/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_494).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_495 : ((57832991/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 495, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 495, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 494, cos1142o2c k) + cos1142o2c 495 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 494) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_494
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 495 - ((6105527/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_495).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_496 : ((125382261/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 496, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 496, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 495, cos1142o2c k) + cos1142o2c 496 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 495) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_495
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 496 - ((9717279/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_496).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_497 : ((5087803/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 497, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 497, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 496, cos1142o2c k) + cos1142o2c 497 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 496) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_496
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 497 - ((906907/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_497).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_498 : ((11897177/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 498, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 498, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 497, cos1142o2c k) + cos1142o2c 498 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 497) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_497
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 498 - ((-1644461/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_498).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_499 : ((110393419/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 499, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 499, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 498, cos1142o2c k) + cos1142o2c 499 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 498) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_498
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 499 - ((-8577351/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_499).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_500 : ((27878251/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 500, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 500, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 499, cos1142o2c k) + cos1142o2c 500 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 499) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_499
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 500 - ((224117/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_500).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_501 : ((121011921/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 501, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 501, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 500, cos1142o2c k) + cos1142o2c 501 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 500) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_500
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 501 - ((9499917/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_501).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_502 : ((127825913/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 502, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 502, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 501, cos1142o2c k) + cos1142o2c 502 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 501) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_501
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 502 - ((425937/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_502).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_503 : ((62027801/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 503, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 503, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 502, cos1142o2c k) + cos1142o2c 503 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 502) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_502
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 503 - ((-3769311/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_503).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_504 : ((57033613/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 504, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 504, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 503, cos1142o2c k) + cos1142o2c 504 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 503) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_503
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 504 - ((-624211/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_504).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_505 : ((27341729/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 505, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 505, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 504, cos1142o2c k) + cos1142o2c 505 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 504) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_504
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 505 - ((-469931/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_505).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_506 : ((57670297/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 506, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 506, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 505, cos1142o2c k) + cos1142o2c 506 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 505) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_505
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 506 - ((2987339/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_506).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_507 : ((125146321/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 507, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 507, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 506, cos1142o2c k) + cos1142o2c 507 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 506) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_506
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 507 - ((9806727/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_507).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_508 : ((127607463/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 508, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 508, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 507, cos1142o2c k) + cos1142o2c 508 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 507) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_507
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 508 - ((1231071/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_508).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_509 : ((59968219/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 509, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 509, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 508, cos1142o2c k) + cos1142o2c 509 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 508) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_508
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 509 - ((-306801/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_509).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_510 : ((55410593/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 510, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 510, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 509, cos1142o2c k) + cos1142o2c 510 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 509) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_509
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 510 - ((-2278563/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_510).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_511 : ((55268813/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 511, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 511, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 510, cos1142o2c k) + cos1142o2c 511 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 510) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_510
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 511 - ((-883/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_511).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_512 : ((119394103/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 512, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 512, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 511, cos1142o2c k) + cos1142o2c 512 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 511) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_511
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 512 - ((8857477/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_512).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_513 : ((127464879/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 513, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 513, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 512, cos1142o2c k) + cos1142o2c 513 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 512) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_512
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 513 - ((252243/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_513).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_514 : ((25149267/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 514, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 514, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 513, cos1142o2c k) + cos1142o2c 514 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 513) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_513
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 514 - ((-214693/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_514).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_515 : ((1814971/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 515, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 515, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 514, cos1142o2c k) + cos1142o2c 515 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 514) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_514
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 515 - ((-9587191/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_515).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_516 : ((683311/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 516, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 516, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 515, cos1142o2c k) + cos1142o2c 516 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 515) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_515
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 516 - ((-853423/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_516).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_517 : ((28198843/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 517, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 517, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 516, cos1142o2c k) + cos1142o2c 517 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 516) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_516
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 517 - ((866653/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_517).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_518 : ((61365079/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 518, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 518, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 517, cos1142o2c k) + cos1142o2c 518 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 517) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_517
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 518 - ((4967893/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_518).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_519 : ((12823407/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 519, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 519, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 518, cos1142o2c k) + cos1142o2c 519 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 518) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_518
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 519 - ((344057/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_519).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_520 : ((24659417/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 520, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 520, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 519, cos1142o2c k) + cos1142o2c 520 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 519) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_519
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 520 - ((-987197/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_520).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_521 : ((56652543/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 521, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 521, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 520, cos1142o2c k) + cos1142o2c 521 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 520) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_520
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 521 - ((-9990999/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_521).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_522 : ((681899/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 522, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 522, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 521, cos1142o2c k) + cos1142o2c 522 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 521) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_521
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 522 - ((-2100123/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_522).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_523 : ((115228987/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 523, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 523, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 522, cos1142o2c k) + cos1142o2c 523 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 522) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_522
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 523 - ((6126147/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_523).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_524 : ((15633461/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 524, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 524, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 523, cos1142o2c k) + cos1142o2c 524 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 523) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_523
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 524 - ((9839701/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_524).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_525 : ((25609793/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 525, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 525, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 524, cos1142o2c k) + cos1142o2c 525 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 524) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_524
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 525 - ((2982277/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_525).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_526 : ((24197673/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 526, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 526, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 525, cos1142o2c k) + cos1142o2c 526 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 525) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_525
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 526 - ((-17649/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_526).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_527 : ((27856647/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 527, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 527, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 526, cos1142o2c k) + cos1142o2c 527 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 526) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_526
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 527 - ((-9560777/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_527).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_528 : ((13691057/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 528, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 528, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 527, cos1142o2c k) + cos1142o2c 528 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 527) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_527
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 528 - ((-474283/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_528).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_529 : ((23459101/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 529, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 529, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 528, cos1142o2c k) + cos1142o2c 529 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 528) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_528
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 529 - ((7768049/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_529).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_530 : ((126516097/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 530, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 530, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 529, cos1142o2c k) + cos1142o2c 530 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 529) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_529
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 530 - ((1152699/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_530).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_531 : ((15935809/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 531, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 531, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 530, cos1142o2c k) + cos1142o2c 531 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 530) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_530
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 531 - ((7771/80000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_531).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_532 : ((119197311/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 532, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 532, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 531, cos1142o2c k) + cos1142o2c 532 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 531) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_531
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 532 - ((-8288161/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_532).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_533 : ((3447487/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 533, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 533, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 532, cos1142o2c k) + cos1142o2c 533 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 532) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_532
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 533 - ((-8876727/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_533).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_534 : ((22019753/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 534, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 534, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 533, cos1142o2c k) + cos1142o2c 534 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 533) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_533
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 534 - ((-219819/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_534).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_535 : ((118753529/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 535, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 535, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 534, cos1142o2c k) + cos1142o2c 535 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 534) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_534
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 535 - ((2163941/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_535).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_536 : ((127320403/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 536, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 536, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 535, cos1142o2c k) + cos1142o2c 536 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 535) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_535
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 536 - ((4283937/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_536).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_537 : ((63483339/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 537, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 537, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 536, cos1142o2c k) + cos1142o2c 537 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 536) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_536
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 537 - ((-14109/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_537).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_538 : ((118064401/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 538, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 538, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 537, cos1142o2c k) + cos1142o2c 538 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 537) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_537
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 538 - ((-8901277/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_538).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_539 : ((27434579/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 539, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 539, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 538, cos1142o2c k) + cos1142o2c 539 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 538) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_538
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 539 - ((-1665017/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_539).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_540 : ((13810559/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 540, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 540, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 539, cos1142o2c k) + cos1142o2c 540 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 539) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_539
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 540 - ((186789/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_540).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_541 : ((4781307/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 541, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 541, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 540, cos1142o2c k) + cos1142o2c 541 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 540) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_540
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 541 - ((9049203/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_541).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_542 : ((63849939/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 542, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 542, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 541, cos1142o2c k) + cos1142o2c 542 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 541) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_541
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 542 - ((8168203/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_542).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_543 : ((63366957/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 543, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 543, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 542, cos1142o2c k) + cos1142o2c 543 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 542) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_542
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 543 - ((-241241/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_543).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_544 : ((58808313/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 544, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 544, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 543, cos1142o2c k) + cos1142o2c 544 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 543) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_543
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 544 - ((-71221/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_544).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_545 : ((109506433/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 545, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 545, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 544, cos1142o2c k) + cos1142o2c 545 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 544) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_544
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 545 - ((-8109193/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_545).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_546 : ((110514073/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 546, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 546, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 545, cos1142o2c k) + cos1142o2c 546 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 545) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_545
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 546 - ((1576/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_546).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_547 : ((119623923/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 547, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 547, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 546, cos1142o2c k) + cos1142o2c 547 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 546) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_546
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 547 - ((182217/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_547).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_548 : ((127773389/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 548, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 548, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 547, cos1142o2c k) + cos1142o2c 548 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 547) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_547
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 548 - ((4075233/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_548).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_549 : ((63445579/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 549, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 549, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 548, cos1142o2c k) + cos1142o2c 549 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 548) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_548
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 549 - ((-881231/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_549).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_550 : ((117857403/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 550, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 550, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 549, cos1142o2c k) + cos1142o2c 550 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 549) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_549
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 550 - ((-1806551/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_550).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_551 : ((54784171/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 551, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 551, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 550, cos1142o2c k) + cos1142o2c 551 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 550) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_550
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 551 - ((-8288061/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_551).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_552 : ((27537669/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 552, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 552, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 551, cos1142o2c k) + cos1142o2c 552 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 551) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_551
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 552 - ((291667/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_552).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_553 : ((3719519/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 553, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 553, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 552, cos1142o2c k) + cos1142o2c 553 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 552) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_552
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 553 - ((2218733/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_553).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_554 : ((63767489/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 554, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 554, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 553, cos1142o2c k) + cos1142o2c 554 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 553) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_553
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 554 - ((851137/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_554).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_555 : ((127417471/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 555, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 555, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 554, cos1142o2c k) + cos1142o2c 555 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 554) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_554
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 555 - ((-116507/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_555).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_556 : ((2969873/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 556, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 556, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 555, cos1142o2c k) + cos1142o2c 556 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 555) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_555
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 556 - ((-8621551/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_556).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_557 : ((109993277/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 557, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 557, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 556, cos1142o2c k) + cos1142o2c 557 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 556) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_556
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 557 - ((-8800643/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_557).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_558 : ((171054/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 558, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 558, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 557, cos1142o2c k) + cos1142o2c 558 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 557) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_557
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 558 - ((-517717/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_558).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_559 : ((58862849/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 559, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 559, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 558, cos1142o2c k) + cos1142o2c 559 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 558) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_558
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 559 - ((4126069/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_559).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_560 : ((126854231/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 560, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 560, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 559, cos1142o2c k) + cos1142o2c 560 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 559) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_559
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 560 - ((9129533/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_560).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_561 : ((128166283/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 561, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 561, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 560, cos1142o2c k) + cos1142o2c 561 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 560) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_560
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 561 - ((328263/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_561).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_562 : ((60212407/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 562, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 562, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 561, cos1142o2c k) + cos1142o2c 562 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 561) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_561
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 562 - ((-7740469/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_562).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_563 : ((3467559/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 563, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 563, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 562, cos1142o2c k) + cos1142o2c 563 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 562) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_562
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 563 - ((-4730963/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_563).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_564 : ((108700943/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 564, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 564, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 563, cos1142o2c k) + cos1142o2c 564 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 563) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_563
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 564 - ((-451989/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_564).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_565 : ((5787901/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 565, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 565, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 564, cos1142o2c k) + cos1142o2c 565 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 564) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_564
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 565 - ((7058077/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_565).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_566 : ((15688823/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 566, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 566, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 565, cos1142o2c k) + cos1142o2c 566 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 565) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_565
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 566 - ((2438391/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_566).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_567 : ((64423851/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 567, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 567, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 566, cos1142o2c k) + cos1142o2c 567 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 566) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_566
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 567 - ((1669059/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_567).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_568 : ((61334851/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 568, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 568, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 567, cos1142o2c k) + cos1142o2c 568 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 567) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_567
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 568 - ((-6177/10000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_568).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_569 : ((11271807/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 569, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 569, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 568, cos1142o2c k) + cos1142o2c 569 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 568) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_568
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 569 - ((-1243829/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_569).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_570 : ((13524897/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 570, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 570, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 569, cos1142o2c k) + cos1142o2c 570 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 569) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_569
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 570 - ((-2258947/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_570).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_571 : ((56635963/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 571, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 571, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 570, cos1142o2c k) + cos1142o2c 571 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 570) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_570
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 571 - ((4059/8000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_571).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_572 : ((123263093/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 572, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 572, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 571, cos1142o2c k) + cos1142o2c 572 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 571) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_571
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 572 - ((9992167/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_572).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_573 : ((64507483/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 573, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 573, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 572, cos1142o2c k) + cos1142o2c 573 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 572) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_572
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 573 - ((5752873/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_573).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_574 : ((25056051/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 574, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 574, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 573, cos1142o2c k) + cos1142o2c 574 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 573) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_573
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 574 - ((-3733711/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_574).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_575 : ((115467263/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 575, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 575, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 574, cos1142o2c k) + cos1142o2c 575 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 574) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_574
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 575 - ((-1226499/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_575).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_576 : ((6780283/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 576, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 576, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 575, cos1142o2c k) + cos1142o2c 576 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 575) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_575
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 576 - ((-1396347/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_576).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_577 : ((110642529/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 577, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 577, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 576, cos1142o2c k) + cos1142o2c 577 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 576) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_576
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 577 - ((2159001/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_577).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_578 : ((119984767/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 578, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 578, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 577, cos1142o2c k) + cos1142o2c 578 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 577) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_577
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 578 - ((4671619/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_578).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_579 : ((128107467/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 579, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 579, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 578, cos1142o2c k) + cos1142o2c 579 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 578) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_578
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 579 - ((81237/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_579).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_580 : ((25546971/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 580, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 580, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 579, cos1142o2c k) + cos1142o2c 580 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 579) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_579
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 580 - ((-92903/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_580).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_581 : ((29802181/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 581, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 581, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 580, cos1142o2c k) + cos1142o2c 581 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 580) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_580
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 581 - ((-8525131/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_581).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_582 : ((22025223/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 582, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 582, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 581, cos1142o2c k) + cos1142o2c 582 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 581) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_581
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 582 - ((-9081609/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_582).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_583 : ((108545421/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 583, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 583, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 582, cos1142o2c k) + cos1142o2c 583 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 582) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_582
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 583 - ((-789847/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_583).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_584 : ((11585551/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 584, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 584, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 583, cos1142o2c k) + cos1142o2c 584 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 583) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_583
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 584 - ((7311089/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_584).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_585 : ((2512001/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 585, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 585, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 584, cos1142o2c k) + cos1142o2c 585 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 584) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_584
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 585 - ((487277/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_585).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_586 : ((129210653/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 586, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 586, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 585, cos1142o2c k) + cos1142o2c 586 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 585) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_585
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 586 - ((3611603/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_586).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_587 : ((30882359/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 587, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 587, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 586, cos1142o2c k) + cos1142o2c 587 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 586) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_586
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 587 - ((-5680217/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_587).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_588 : ((113528571/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 588, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 588, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 587, cos1142o2c k) + cos1142o2c 588 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 587) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_587
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 588 - ((-1999973/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_588).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_589 : ((3372487/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 589, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 589, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 588, cos1142o2c k) + cos1142o2c 589 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 588) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_588
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 589 - ((-5607987/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_589).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_590 : ((111565431/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 590, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 590, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 589, cos1142o2c k) + cos1142o2c 590 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 589) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_589
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 590 - ((3646847/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_590).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_591 : ((121299923/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 591, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 591, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 590, cos1142o2c k) + cos1142o2c 591 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 590) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_590
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 591 - ((2433873/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_591).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_592 : ((32179611/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 592, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 592, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 591, cos1142o2c k) + cos1142o2c 592 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 591) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_591
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 592 - ((7419521/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_592).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_593 : ((63721959/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 593, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 593, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 592, cos1142o2c k) + cos1142o2c 593 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 592) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_592
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 593 - ((-636763/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_593).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_594 : ((23715483/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 594, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 594, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 593, cos1142o2c k) + cos1142o2c 594 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 593) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_593
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 594 - ((-8865503/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_594).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_595 : ((109704237/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 595, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 595, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 594, cos1142o2c k) + cos1142o2c 595 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 594) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_594
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 595 - ((-4436089/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_595).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_596 : ((108382547/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 596, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 596, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 595, cos1142o2c k) + cos1142o2c 596 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 595) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_595
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 596 - ((-132069/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_596).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_597 : ((115725841/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 597, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 597, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 596, cos1142o2c k) + cos1142o2c 597 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 596) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_596
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 597 - ((3672147/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_597).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_598 : ((125505869/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 598, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 598, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 597, cos1142o2c k) + cos1142o2c 598 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 597) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_597
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 598 - ((2445257/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_598).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_599 : ((25892897/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 599, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 599, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 598, cos1142o2c k) + cos1142o2c 599 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 598) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_598
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 599 - ((61869/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_599).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_600 : ((124276137/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 600, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 600, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 599, cos1142o2c k) + cos1142o2c 600 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 599) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_599
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 600 - ((-1296837/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_600).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_601 : ((22860581/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 601, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 601, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 600, cos1142o2c k) + cos1142o2c 601 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 600) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_600
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 601 - ((-1246529/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_601).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_602 : ((107890001/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 602, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 602, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 601, cos1142o2c k) + cos1142o2c 602 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 601) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_601
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 602 - ((-50093/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_602).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_603 : ((110378929/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 603, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 603, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 602, cos1142o2c k) + cos1142o2c 603 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 602) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_602
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 603 - ((311241/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_603).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_604 : ((119690279/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 604, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 604, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 603, cos1142o2c k) + cos1142o2c 604 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 603) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_603
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 604 - ((186247/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_604).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_605 : ((25619933/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 605, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 605, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 604, cos1142o2c k) + cos1142o2c 605 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 604) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_604
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 605 - ((4205193/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_605).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_606 : ((64330153/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 606, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 606, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 605, cos1142o2c k) + cos1142o2c 606 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 605) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_605
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 606 - ((561641/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_606).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_607 : ((120918439/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 607, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 607, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 606, cos1142o2c k) + cos1142o2c 607 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 606) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_606
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 607 - ((-7740867/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_607).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_608 : ((111239289/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 608, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 608, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 607, cos1142o2c k) + cos1142o2c 608 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 607) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_607
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 608 - ((-193563/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_608).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_609 : ((107547507/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 609, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 609, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 608, cos1142o2c k) + cos1142o2c 609 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 608) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_608
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 609 - ((-1845391/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_609).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_610 : ((11284839/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 610, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 610, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 609, cos1142o2c k) + cos1142o2c 610 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 609) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_609
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 610 - ((5301883/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_610).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_611 : ((122818009/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 611, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 611, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 610, cos1142o2c k) + cos1142o2c 611 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 610) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_610
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 611 - ((9970619/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_611).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_612 : ((3234087/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 612, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 612, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 611, cos1142o2c k) + cos1142o2c 612 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 611) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_611
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 612 - ((6546471/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_612).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_613 : ((63597139/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 613, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 613, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 612, cos1142o2c k) + cos1142o2c 613 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 612) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_612
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 613 - ((-1084101/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_613).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_614 : ((118068557/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 614, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 614, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 613, cos1142o2c k) + cos1142o2c 614 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 613) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_613
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 614 - ((-9124721/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_614).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_615 : ((136661/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 615, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 615, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 614, cos1142o2c k) + cos1142o2c 615 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 614) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_614
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 615 - ((-8738757/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_615).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_616 : ((26994447/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 616, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 616, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 615, cos1142o2c k) + cos1142o2c 616 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 615) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_615
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 616 - ((-337503/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_616).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_617 : ((115085981/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 617, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 617, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 616, cos1142o2c k) + cos1142o2c 617 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 616) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_616
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 617 - ((7109193/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_617).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_618 : ((62490247/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 618, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 618, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 617, cos1142o2c k) + cos1142o2c 618 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 617) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_617
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 618 - ((9895513/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_618).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_619 : ((129799337/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 619, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 619, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 618, cos1142o2c k) + cos1142o2c 619 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 618) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_618
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 619 - ((4819843/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_619).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_620 : ((62865891/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 620, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 620, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 619, cos1142o2c k) + cos1142o2c 620 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 619) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_619
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 620 - ((-813311/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_620).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_621 : ((115998197/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 621, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 621, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 620, cos1142o2c k) + cos1142o2c 621 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 620) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_620
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 621 - ((-1946517/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_621).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_622 : ((541327/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 622, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 622, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 621, cos1142o2c k) + cos1142o2c 622 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 621) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_621
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 622 - ((-7731797/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_622).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_623 : ((54299527/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 623, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 623, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 622, cos1142o2c k) + cos1142o2c 623 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 622) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_622
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 623 - ((167327/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_623).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_624 : ((23345559/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 624, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 624, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 623, cos1142o2c k) + cos1142o2c 624 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 623) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_623
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 624 - ((8129741/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_624).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_625 : ((63150613/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 625, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 625, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 624, cos1142o2c k) + cos1142o2c 625 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 624) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_624
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 625 - ((9574431/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_625).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_626 : ((129871131/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 626, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 626, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 625, cos1142o2c k) + cos1142o2c 626 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 625) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_625
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 626 - ((714181/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_626).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_627 : ((124675017/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 627, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 627, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 626, cos1142o2c k) + cos1142o2c 627 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 626) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_626
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 627 - ((-2597557/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_627).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_628 : ((114739579/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 628, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 628, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 627, cos1142o2c k) + cos1142o2c 628 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 627) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_627
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 628 - ((-4967219/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_628).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_629 : ((53864107/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 629, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 629, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 628, cos1142o2c k) + cos1142o2c 629 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 628) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_628
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 629 - ((-1402073/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_629).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_630 : ((54512971/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 630, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 630, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 629, cos1142o2c k) + cos1142o2c 630 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 629) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_629
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 630 - ((162341/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_630).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_631 : ((23525577/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 631, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 631, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 630, cos1142o2c k) + cos1142o2c 631 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 630) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_630
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 631 - ((8602943/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_631).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_632 : ((7934559/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 632, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 632, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 631, cos1142o2c k) + cos1142o2c 632 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 631) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_631
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 632 - ((9326059/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_632).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_633 : ((32473823/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 633, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 633, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 632, cos1142o2c k) + cos1142o2c 633 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 632) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_632
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 633 - ((735837/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_633).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_634 : ((124226723/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 634, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 634, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 633, cos1142o2c k) + cos1142o2c 634 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 633) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_633
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 634 - ((-5667569/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_634).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_635 : ((114249063/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 635, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 635, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 634, cos1142o2c k) + cos1142o2c 635 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 634) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_634
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 635 - ((-498833/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_635).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_636 : ((107500703/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 636, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 636, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 635, cos1142o2c k) + cos1142o2c 636 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 635) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_635
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 636 - ((-42171/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_636).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_637 : ((21811647/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 637, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 637, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 636, cos1142o2c k) + cos1142o2c 637 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 636) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_636
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 637 - ((389633/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_637).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_638 : ((117742203/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 638, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 638, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 637, cos1142o2c k) + cos1142o2c 638 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 637) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_637
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 638 - ((1085621/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_638).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_639 : ((127043839/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 639, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 639, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 638, cos1142o2c k) + cos1142o2c 639 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 638) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_638
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 639 - ((2325659/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_639).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_640 : ((26003921/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 640, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 640, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 639, cos1142o2c k) + cos1142o2c 640 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 639) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_639
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 640 - ((1488383/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_640).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_641 : ((31115319/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 641, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 641, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 640, cos1142o2c k) + cos1142o2c 641 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 640) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_640
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 641 - ((-5557329/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_641).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_642 : ((22900407/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 642, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 642, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 641, cos1142o2c k) + cos1142o2c 642 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 641) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_641
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 642 - ((-9958241/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_642).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_643 : ((6719657/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 643, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 643, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 642, cos1142o2c k) + cos1142o2c 643 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 642) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_642
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 643 - ((-6986523/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_643).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_644 : ((27162319/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 644, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 644, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 643, cos1142o2c k) + cos1142o2c 644 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 643) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_643
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 644 - ((283941/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_644).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_645 : ((117061827/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 645, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 645, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 644, cos1142o2c k) + cos1142o2c 645 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 644) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_644
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 645 - ((8413551/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_645).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_646 : ((126573173/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 646, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 646, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 645, cos1142o2c k) + cos1142o2c 646 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 645) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_645
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 646 - ((4756173/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_646).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_647 : ((3255651/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 647, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 647, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 646, cos1142o2c k) + cos1142o2c 647 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 646) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_646
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 647 - ((3653867/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_647).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_648 : ((125362443/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 648, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 648, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 647, cos1142o2c k) + cos1142o2c 648 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 647) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_647
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 648 - ((-4862597/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_648).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_649 : ((115527427/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 649, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 649, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 648, cos1142o2c k) + cos1142o2c 649 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 648) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_648
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 649 - ((-307313/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_649).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_650 : ((53928261/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 650, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 650, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 649, cos1142o2c k) + cos1142o2c 650 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 649) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_649
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 650 - ((-1533981/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_650).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_651 : ((3371629/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 651, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 651, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 650, cos1142o2c k) + cos1142o2c 651 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 650) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_650
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 651 - ((18303/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_651).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_652 : ((2889977/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 652, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 652, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 651, cos1142o2c k) + cos1142o2c 652 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 651) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_651
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 652 - ((481747/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_652).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_653 : ((31357133/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 653, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 653, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 652, cos1142o2c k) + cos1142o2c 653 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 652) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_652
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 653 - ((2457613/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_653).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_654 : ((1042659/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 654, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 654, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 653, cos1142o2c k) + cos1142o2c 654 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 653) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_653
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 654 - ((4904843/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_654).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_655 : ((1585133/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 655, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 655, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 654, cos1142o2c k) + cos1142o2c 655 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 654) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_654
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 655 - ((-704147/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_655).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_656 : ((14672741/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 656, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 656, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 655, cos1142o2c k) + cos1142o2c 656 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 655) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_655
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 656 - ((-73654/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_656).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_657 : ((108752119/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 657, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 657, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 656, cos1142o2c k) + cos1142o2c 657 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 656) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_656
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 657 - ((-8628809/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_657).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_658 : ((53517289/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 658, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 658, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 657, cos1142o2c k) + cos1142o2c 658 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 657) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_657
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 658 - ((-1716541/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_658).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_659 : ((113434453/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 659, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 659, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 658, cos1142o2c k) + cos1142o2c 659 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 658) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_658
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 659 - ((51207/80000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_659).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_660 : ((24686583/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 660, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 660, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 659, cos1142o2c k) + cos1142o2c 660 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 659) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_659
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 660 - ((4999731/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_660).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_661 : ((130000759/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 661, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 661, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 660, cos1142o2c k) + cos1142o2c 661 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 660) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_660
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 661 - ((1642211/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_661).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_662 : ((128539979/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 662, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 662, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 661, cos1142o2c k) + cos1142o2c 662 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 661) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_661
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 662 - ((-72989/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_662).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_663 : ((120079347/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 663, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 663, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 662, cos1142o2c k) + cos1142o2c 663 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 662) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_662
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 663 - ((-528727/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_663).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_664 : ((110519631/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 664, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 664, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 663, cos1142o2c k) + cos1142o2c 664 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 663) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_663
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 664 - ((-2389679/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_664).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_665 : ((1331277/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 665, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 665, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 664, cos1142o2c k) + cos1142o2c 665 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 664) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_664
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 665 - ((-4016471/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_665).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_666 : ((110802759/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 666, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 666, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 665, cos1142o2c k) + cos1142o2c 666 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 665) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_665
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 666 - ((4301599/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_666).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_667 : ((7527567/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 667, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 667, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 666, cos1142o2c k) + cos1142o2c 667 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 666) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_666
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 667 - ((9639313/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_667).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_668 : ((32192893/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 668, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 668, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 667, cos1142o2c k) + cos1142o2c 668 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 667) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_667
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 668 - ((16663/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_668).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_669 : ((16259133/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 669, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 669, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 668, cos1142o2c k) + cos1142o2c 669 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 668) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_668
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 669 - ((325623/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_669).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_670 : ((4938443/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 670, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 670, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 669, cos1142o2c k) + cos1142o2c 670 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 669) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_669
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 670 - ((-6610989/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_670).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_671 : ((56730061/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 671, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 671, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 670, cos1142o2c k) + cos1142o2c 671 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 670) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_670
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 671 - ((-9999953/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_671).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_672 : ((106884937/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 672, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 672, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 671, cos1142o2c k) + cos1142o2c 672 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 671) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_671
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 672 - ((-1314837/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_672).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_673 : ((108197027/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 673, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 673, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 672, cos1142o2c k) + cos1142o2c 673 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 672) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_672
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 673 - ((131309/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_673).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_674 : ((116498271/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 674, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 674, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 673, cos1142o2c k) + cos1142o2c 674 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 673) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_673
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 674 - ((2075561/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_674).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_675 : ((63086673/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 675, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 675, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 674, cos1142o2c k) + cos1142o2c 675 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 674) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_674
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 675 - ((387043/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_675).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_676 : ((65351793/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 676, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 676, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 675, cos1142o2c k) + cos1142o2c 676 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 675) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_675
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 676 - ((113281/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_676).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_677 : ((31762791/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 677, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 677, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 676, cos1142o2c k) + cos1142o2c 677 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 676) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_676
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 677 - ((-1825711/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_677).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_678 : ((117670973/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 678, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 678, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 677, cos1142o2c k) + cos1142o2c 678 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 677) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_677
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 678 - ((-9379191/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_678).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_679 : ((54417177/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 679, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 679, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 678, cos1142o2c k) + cos1142o2c 679 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 678) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_678
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 679 - ((-8835619/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_679).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_680 : ((106425931/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 680, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 680, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 679, cos1142o2c k) + cos1142o2c 680 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 679) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_679
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 680 - ((-2407423/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_680).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_681 : ((28009597/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 681, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 681, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 680, cos1142o2c k) + cos1142o2c 681 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 680) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_680
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 681 - ((5613457/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_681).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_682 : ((30485937/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 682, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 682, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 681, cos1142o2c k) + cos1142o2c 682 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 681) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_681
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 682 - ((247659/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_682).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_683 : ((129593281/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 683, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 683, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 682, cos1142o2c k) + cos1142o2c 683 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 682) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_682
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 683 - ((7650533/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_683).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_684 : ((64974573/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 684, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 684, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 683, cos1142o2c k) + cos1142o2c 684 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 683) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_683
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 684 - ((71373/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_684).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_685 : ((3837037/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 685, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 685, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 684, cos1142o2c k) + cos1142o2c 685 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 684) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_684
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 685 - ((-3581481/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_685).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_686 : ((7050161/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 686, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 686, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 685, cos1142o2c k) + cos1142o2c 686 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 685) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_685
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 686 - ((-1247701/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_686).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_687 : ((13315743/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 687, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 687, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 686, cos1142o2c k) + cos1142o2c 687 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 686) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_686
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 687 - ((-392227/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_687).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_688 : ((27010163/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 688, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 688, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 687, cos1142o2c k) + cos1142o2c 688 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 687) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_687
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 688 - ((378927/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_688).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_689 : ((116352847/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 689, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 689, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 688, cos1142o2c k) + cos1142o2c 689 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 688) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_688
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 689 - ((1662639/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_689).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_690 : ((63034033/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 690, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 690, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 689, cos1142o2c k) + cos1142o2c 690 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 689) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_689
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 690 - ((9716219/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_690).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_691 : ((130905267/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 691, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 691, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 690, cos1142o2c k) + cos1142o2c 691 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 690) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_690
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 691 - ((4838201/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_691).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_692 : ((204403/16000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 692, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 692, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 691, cos1142o2c k) + cos1142o2c 692 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 691) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_691
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 692 - ((-394049/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_692).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_693 : ((118642813/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 693, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 693, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 692, cos1142o2c k) + cos1142o2c 693 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 692) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_692
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 693 - ((-4554031/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_693).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_694 : ((109422729/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 694, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 694, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 693, cos1142o2c k) + cos1142o2c 694 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 693) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_693
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 694 - ((-2304771/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_694).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_695 : ((105985283/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 695, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 695, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 694, cos1142o2c k) + cos1142o2c 695 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 694) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_694
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 695 - ((-1718223/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_695).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_696 : ((27628707/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 696, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 696, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 695, cos1142o2c k) + cos1142o2c 696 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 695) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_695
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 696 - ((906109/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_696).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_697 : ((120122263/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 697, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 697, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 696, cos1142o2c k) + cos1142o2c 697 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 696) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_696
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 697 - ((1921687/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_697).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_698 : ((64354623/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 698, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 698, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 697, cos1142o2c k) + cos1142o2c 698 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 697) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_697
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 698 - ((8587983/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_698).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_699 : ((130846369/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 699, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 699, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 698, cos1142o2c k) + cos1142o2c 699 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 698) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_698
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 699 - ((2138123/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_699).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_700 : ((125192131/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 700, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 700, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 699, cos1142o2c k) + cos1142o2c 700 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 699) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_699
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 700 - ((-2826619/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_700).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_701 : ((28827703/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 701, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 701, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 700, cos1142o2c k) + cos1142o2c 701 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 700) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_700
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 701 - ((-9880319/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_701).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_702 : ((53702339/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 702, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 702, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 701, cos1142o2c k) + cos1142o2c 702 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 701) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_701
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 702 - ((-3952567/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_702).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_703 : ((21283287/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 703, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 703, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 702, cos1142o2c k) + cos1142o2c 703 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 702) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_702
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 703 - ((-987243/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_703).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_704 : ((56477457/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 704, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 704, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 703, cos1142o2c k) + cos1142o2c 704 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 703) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_703
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 704 - ((6539479/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_704).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_705 : ((122942649/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 705, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 705, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 704, cos1142o2c k) + cos1142o2c 705 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 704) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_704
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 705 - ((1997747/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_705).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_706 : ((2603543/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 706, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 706, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 705, cos1142o2c k) + cos1142o2c 706 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 705) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_705
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 706 - ((7235501/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_706).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_707 : ((32545883/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 707, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 707, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 706, cos1142o2c k) + cos1142o2c 707 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 706) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_706
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 707 - ((3691/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_707).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_708 : ((12296513/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 708, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 708, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 707, cos1142o2c k) + cos1142o2c 708 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 707) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_707
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 708 - ((-3608701/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_708).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_709 : ((112972733/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 709, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 709, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 708, cos1142o2c k) + cos1142o2c 709 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 708) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_708
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 709 - ((-9991397/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_709).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_710 : ((5317189/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 710, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 710, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 709, cos1142o2c k) + cos1142o2c 710 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 709) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_709
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 710 - ((-6627953/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_710).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_711 : ((107133323/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 711, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 711, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 710, cos1142o2c k) + cos1142o2c 711 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 710) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_710
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 711 - ((790543/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_711).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_712 : ((114850389/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 712, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 712, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 711, cos1142o2c k) + cos1142o2c 712 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 711) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_711
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 712 - ((3859033/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_712).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_713 : ((62393211/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 713, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 713, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 712, cos1142o2c k) + cos1142o2c 713 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 712) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_712
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 713 - ((9937033/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_713).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_714 : ((130902837/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 714, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 714, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 713, cos1142o2c k) + cos1142o2c 714 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 713) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_713
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 714 - ((1223483/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_714).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_715 : ((64748691/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 715, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 715, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 714, cos1142o2c k) + cos1142o2c 715 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 714) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_714
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 715 - ((-280891/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_715).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_716 : ((30356763/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 716, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 716, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 715, cos1142o2c k) + cos1142o2c 716 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 715) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_715
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 716 - ((-806933/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_716).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_717 : ((22312403/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 717, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 717, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 716, cos1142o2c k) + cos1142o2c 717 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 716) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_716
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 717 - ((-9864037/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_717).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_718 : ((169333/16000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 718, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 718, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 717, cos1142o2c k) + cos1142o2c 718 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 717) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_717
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 718 - ((-572789/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_718).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_719 : ((107669757/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 719, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 719, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 718, cos1142o2c k) + cos1142o2c 719 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 718) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_718
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 719 - ((28713/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_719).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_720 : ((115965067/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 720, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 720, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 719, cos1142o2c k) + cos1142o2c 720 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 719) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_719
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 720 - ((829631/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_720).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_721 : ((125764453/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 721, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 721, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 720, cos1142o2c k) + cos1142o2c 721 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 720) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_720
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 721 - ((4900193/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_721).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_722 : ((32809353/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 722, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 722, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 721, cos1142o2c k) + cos1142o2c 722 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 721) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_721
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 722 - ((5473959/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_722).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_723 : ((129141333/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 723, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 723, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 722, cos1142o2c k) + cos1142o2c 723 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 722) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_722
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 723 - ((-2095079/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_723).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_724 : ((30181067/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 724, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 724, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 723, cos1142o2c k) + cos1142o2c 724 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 723) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_723
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 724 - ((-1683213/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_724).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_725 : ((110959097/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 725, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 725, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 724, cos1142o2c k) + cos1142o2c 725 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 724) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_724
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 725 - ((-9764171/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_725).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_726 : ((6599653/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 726, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 726, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 725, cos1142o2c k) + cos1142o2c 726 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 725) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_725
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 726 - ((-5363649/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_726).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_727 : ((21554759/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 727, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 727, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 726, cos1142o2c k) + cos1142o2c 727 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 726) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_726
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 727 - ((2180347/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_727).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_728 : ((116212789/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 728, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 728, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 727, cos1142o2c k) + cos1142o2c 728 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 727) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_727
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 728 - ((4219997/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_728).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_729 : ((125975731/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 729, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 729, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 728, cos1142o2c k) + cos1142o2c 729 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 728) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_728
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 729 - ((4881971/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_729).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_730 : ((131374059/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 730, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 730, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 729, cos1142o2c k) + cos1142o2c 730 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 729) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_729
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 730 - ((168729/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_730).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_731 : ((64637949/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 731, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 731, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 730, cos1142o2c k) + cos1142o2c 731 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 730) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_730
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 731 - ((-2097161/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_731).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_732 : ((24180847/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 732, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 732, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 731, cos1142o2c k) + cos1142o2c 732 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 731) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_731
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 732 - ((-8370663/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_732).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_733 : ((55551913/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 733, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 733, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 732, cos1142o2c k) + cos1142o2c 733 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 732) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_732
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 733 - ((-9799409/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_733).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_734 : ((1648827/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 734, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 734, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 733, cos1142o2c k) + cos1142o2c 734 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 733) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_733
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 734 - ((-2788949/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_734).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_735 : ((53684837/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 735, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 735, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 734, cos1142o2c k) + cos1142o2c 735 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 734) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_734
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 735 - ((922873/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_735).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_736 : ((57786101/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 736, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 736, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 735, cos1142o2c k) + cos1142o2c 736 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 735) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_735
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 736 - ((1025441/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_736).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_737 : ((125432947/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 737, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 737, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 736, cos1142o2c k) + cos1142o2c 737 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 736) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_736
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 737 - ((1972349/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_737).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_738 : ((16415467/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 738, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 738, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 737, cos1142o2c k) + cos1142o2c 738 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 737) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_737
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 738 - ((5891789/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_738).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_739 : ((32474033/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 739, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 739, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 738, cos1142o2c k) + cos1142o2c 739 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 738) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_738
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 739 - ((-356651/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_739).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_740 : ((121967951/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 740, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 740, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 739, cos1142o2c k) + cos1142o2c 740 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 739) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_739
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 740 - ((-7927181/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_740).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_741 : ((112033687/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 741, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 741, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 740, cos1142o2c k) + cos1142o2c 741 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 740) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_740
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 741 - ((-620829/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_741).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_742 : ((105704783/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 742, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 742, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 741, cos1142o2c k) + cos1142o2c 742 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 741) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_741
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 742 - ((-197747/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_742).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_743 : ((106541513/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 743, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 743, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 742, cos1142o2c k) + cos1142o2c 743 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 742) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_742
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 743 - ((83773/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_743).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_744 : ((114065621/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 744, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 744, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 743, cos1142o2c k) + cos1142o2c 744 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 743) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_743
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 744 - ((1881277/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_744).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_745 : ((24810617/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 745, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 745, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 744, cos1142o2c k) + cos1142o2c 745 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 744) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_744
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 745 - ((624279/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_745).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_746 : ((130918213/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 746, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 746, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 745, cos1142o2c k) + cos1142o2c 746 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 745) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_745
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 746 - ((429133/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_746).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_747 : ((130836867/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 747, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 747, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 746, cos1142o2c k) + cos1142o2c 747 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 746) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_746
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 747 - ((-40173/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_747).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_748 : ((61930377/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 748, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 748, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 747, cos1142o2c k) + cos1142o2c 748 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 747) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_747
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 748 - ((-6975113/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_748).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_749 : ((113866241/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 749, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 749, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 748, cos1142o2c k) + cos1142o2c 749 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 748) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_748
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 749 - ((-9993513/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_749).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_750 : ((13298247/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 750, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 750, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 749, cos1142o2c k) + cos1142o2c 750 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 749) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_749
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 750 - ((-1495853/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_750).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_751 : ((26386161/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 751, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 751, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 750, cos1142o2c k) + cos1142o2c 751 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 750) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_750
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 751 - ((-210083/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_751).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_752 : ((111798059/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 752, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 752, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 751, cos1142o2c k) + cos1142o2c 752 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 751) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_751
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 752 - ((1250883/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_752).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_753 : ((60852159/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 753, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 753, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 752, cos1142o2c k) + cos1142o2c 753 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 752) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_752
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 753 - ((9907259/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_753).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_754 : ((16229189/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 754, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 754, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 753, cos1142o2c k) + cos1142o2c 754 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 753) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_753
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 754 - ((4065097/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_754).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_755 : ((65872901/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 755, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 755, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 754, cos1142o2c k) + cos1142o2c 755 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 754) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_754
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 755 - ((191329/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_755).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_756 : ((126405351/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 756, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 756, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 755, cos1142o2c k) + cos1142o2c 756 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 755) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_755
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 756 - ((-5339451/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_756).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_757 : ((58361011/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 757, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 757, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 756, cos1142o2c k) + cos1142o2c 757 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 756) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_756
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 757 - ((-9682329/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_757).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_758 : ((107950213/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 758, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 758, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 757, cos1142o2c k) + cos1142o2c 758 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 757) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_757
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 758 - ((-8770809/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_758).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_759 : ((20966513/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 759, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 759, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 758, cos1142o2c k) + cos1142o2c 759 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 758) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_758
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 759 - ((-389581/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_759).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_760 : ((109044681/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 760, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 760, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 759, cos1142o2c k) + cos1142o2c 760 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 759) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_759
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 760 - ((1053279/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_760).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_761 : ((1183113/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 761, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 761, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 760, cos1142o2c k) + cos1142o2c 761 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 760) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_760
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 761 - ((9267619/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_761).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_762 : ((63826233/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 762, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 762, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 761, cos1142o2c k) + cos1142o2c 762 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 761) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_761
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 762 - ((4671083/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_762).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_763 : ((132065751/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 763, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 763, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 762, cos1142o2c k) + cos1142o2c 763 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 762) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_762
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 763 - ((882857/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_763).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_764 : ((129199013/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 764, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 764, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 763, cos1142o2c k) + cos1142o2c 764 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 763) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_763
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 764 - ((-1432869/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_764).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_765 : ((60293139/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 765, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 765, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 764, cos1142o2c k) + cos1142o2c 765 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 764) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_764
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 765 - ((-1722347/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_765).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_766 : ((5540529/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 766, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 766, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 765, cos1142o2c k) + cos1142o2c 766 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 765) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_765
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 766 - ((-4887349/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_766).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_767 : ((52527607/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 767, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 767, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 766, cos1142o2c k) + cos1142o2c 767 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 766) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_766
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 767 - ((-2877183/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_767).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_768 : ((53179333/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 768, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 768, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 767, cos1142o2c k) + cos1142o2c 768 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 767) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_767
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 768 - ((326113/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_768).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_769 : ((7126589/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 769, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 769, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 768, cos1142o2c k) + cos1142o2c 769 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 768) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_768
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 769 - ((3833879/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_769).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_770 : ((24802853/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 770, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 770, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 769, cos1142o2c k) + cos1142o2c 770 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 769) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_769
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 770 - ((9989841/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_770).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_771 : ((13107921/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 771, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 771, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 770, cos1142o2c k) + cos1142o2c 771 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 770) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_770
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 771 - ((1413189/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_771).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_772 : ((131523501/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 772, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 772, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 771, cos1142o2c k) + cos1142o2c 772 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 771) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_771
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 772 - ((445291/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_772).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_773 : ((125121599/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 773, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 773, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 772, cos1142o2c k) + cos1142o2c 773 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 772) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_772
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 773 - ((-3200451/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_773).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_774 : ((115215657/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 774, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 774, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 773, cos1142o2c k) + cos1142o2c 774 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 773) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_773
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 774 - ((-4952471/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_774).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_775 : ((106957257/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 775, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 775, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 774, cos1142o2c k) + cos1142o2c 775 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 774) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_774
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 775 - ((-41287/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_775).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_776 : ((523129/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 776, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 776, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 775, cos1142o2c k) + cos1142o2c 776 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 775) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_775
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 776 - ((-2330457/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_776).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_777 : ((21884031/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 777, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 777, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 776, cos1142o2c k) + cos1142o2c 777 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 776) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_776
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 777 - ((959071/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_777).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_778 : ((59429569/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 778, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 778, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 777, cos1142o2c k) + cos1142o2c 778 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 777) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_777
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 778 - ((9439983/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_778).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_779 : ((6403981/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 779, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 779, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 778, cos1142o2c k) + cos1142o2c 779 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 778) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_778
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 779 - ((4610741/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_779).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_780 : ((66173809/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 780, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 780, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 779, cos1142o2c k) + cos1142o2c 780 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 779) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_779
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 780 - ((2134499/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_780).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_781 : ((4046321/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 781, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 781, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 780, cos1142o2c k) + cos1142o2c 781 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 780) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_780
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 781 - ((-1432173/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_781).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_782 : ((15119269/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 782, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 782, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 781, cos1142o2c k) + cos1142o2c 782 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 781) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_781
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 782 - ((-106589/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_782).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_783 : ((55557393/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 783, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 783, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 782, cos1142o2c k) + cos1142o2c 783 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 782) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_782
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 783 - ((-4919183/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_783).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_784 : ((26241841/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 784, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 784, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 783, cos1142o2c k) + cos1142o2c 784 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 783) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_783
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 784 - ((-3073211/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_784).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_785 : ((105625101/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 785, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 785, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 784, cos1142o2c k) + cos1142o2c 785 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 784) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_784
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 785 - ((658737/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_785).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_786 : ((7046709/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 786, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 786, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 785, cos1142o2c k) + cos1142o2c 786 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 785) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_785
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 786 - ((7123243/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_786).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_787 : ((24546569/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 787, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 787, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 786, cos1142o2c k) + cos1142o2c 787 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 786) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_786
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 787 - ((9986501/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_787).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_788 : ((130550833/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 788, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 788, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 787, cos1142o2c k) + cos1142o2c 788 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 787) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_787
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 788 - ((1954747/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_788).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_789 : ((132276207/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 789, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 789, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 788, cos1142o2c k) + cos1142o2c 789 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 788) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_788
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 789 - ((863187/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_789).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_790 : ((25410141/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 790, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 790, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 789, cos1142o2c k) + cos1142o2c 790 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 789) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_789
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 790 - ((-2612251/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_790).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_791 : ((117492681/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 791, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 791, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 790, cos1142o2c k) + cos1142o2c 791 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 790) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_790
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 791 - ((-298657/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_791).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_792 : ((108371597/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 792, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 792, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 791, cos1142o2c k) + cos1142o2c 792 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 791) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_791
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 792 - ((-2280021/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_792).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_793 : ((104223631/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 793, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 793, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 792, cos1142o2c k) + cos1142o2c 793 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 792) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_792
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 793 - ((-2073483/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_793).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_794 : ((4284039/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 794, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 794, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 793, cos1142o2c k) + cos1142o2c 794 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 793) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_793
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 794 - ((359793/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_794).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_795 : ((57785961/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 795, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 795, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 794, cos1142o2c k) + cos1142o2c 795 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 794) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_794
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 795 - ((8471947/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_795).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_796 : ((62723469/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 796, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 796, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 795, cos1142o2c k) + cos1142o2c 796 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 795) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_795
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 796 - ((617251/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_796).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_797 : ((65929781/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 797, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 797, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 796, cos1142o2c k) + cos1142o2c 797 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 796) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_796
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 797 - ((801703/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_797).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_798 : ((32915383/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 798, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 798, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 797, cos1142o2c k) + cos1142o2c 798 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 797) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_797
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 798 - ((-19703/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_798).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_799 : ((124955961/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 799, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 799, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 798, cos1142o2c k) + cos1142o2c 799 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 798) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_798
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 799 - ((-6704571/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_799).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_800 : ((115029003/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 800, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 800, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 799, cos1142o2c k) + cos1142o2c 800 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 799) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_799
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 800 - ((-4962979/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_800).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_801 : ((106727109/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 801, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 801, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 800, cos1142o2c k) + cos1142o2c 801 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 800) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_800
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 801 - ((-4150447/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_801).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_802 : ((104089347/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 802, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 802, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 801, cos1142o2c k) + cos1142o2c 802 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 801) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_801
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 802 - ((-1318381/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_802).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_803 : ((846798/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 803, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 803, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 802, cos1142o2c k) + cos1142o2c 803 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 802) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_802
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 803 - ((4301797/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_803).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_804 : ((11753831/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 804, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 804, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 803, cos1142o2c k) + cos1142o2c 804 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 803) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_803
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 804 - ((4574583/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_804).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_805 : ((63553743/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 805, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 805, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 804, cos1142o2c k) + cos1142o2c 805 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 804) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_804
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 805 - ((74767/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_805).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_806 : ((66241469/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 806, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 806, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 805, cos1142o2c k) + cos1142o2c 806 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 805) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_805
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 806 - ((1344113/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_806).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_807 : ((13108313/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 807, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 807, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 806, cos1142o2c k) + cos1142o2c 807 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 806) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_806
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 807 - ((-174851/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_807).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_808 : ((7724129/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 808, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 808, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 807, cos1142o2c k) + cos1142o2c 808 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 807) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_807
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 808 - ((-3748033/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_808).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_809 : ((113586519/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 809, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 809, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 808, cos1142o2c k) + cos1142o2c 809 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 808) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_808
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 809 - ((-1999709/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_809).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_810 : ((13232779/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 810, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 810, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 809, cos1142o2c k) + cos1142o2c 810 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 809) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_809
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 810 - ((-7723287/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_810).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_811 : ((33309/3200 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 811, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 811, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 810, cos1142o2c k) + cos1142o2c 811 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 810) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_810
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 811 - ((-1770607/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_811).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_812 : ((109107327/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 812, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 812, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 811, cos1142o2c k) + cos1142o2c 812 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 811) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_811
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 812 - ((2508851/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_812).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_813 : ((118525959/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 813, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 813, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 812, cos1142o2c k) + cos1142o2c 813 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 812) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_812
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 813 - ((588727/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_813).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_814 : ((6394283/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 814, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 814, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 813, cos1142o2c k) + cos1142o2c 814 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 813) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_813
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 814 - ((9360701/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_814).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_815 : ((132768307/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 815, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 815, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 814, cos1142o2c k) + cos1142o2c 815 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 814) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_814
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 815 - ((4883647/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_815).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_816 : ((65439627/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 816, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 816, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 815, cos1142o2c k) + cos1142o2c 816 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 815) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_815
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 816 - ((-1888053/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_816).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_817 : ((24622453/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 817, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 817, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 816, cos1142o2c k) + cos1142o2c 817 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 816) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_816
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 817 - ((-7765989/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_817).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_818 : ((113112703/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 818, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 818, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 817, cos1142o2c k) + cos1142o2c 818 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 817) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_817
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 818 - ((-4999281/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_818).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_819 : ((105557807/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 819, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 819, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 818, cos1142o2c k) + cos1142o2c 819 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 818) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_818
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 819 - ((-944237/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_819).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_820 : ((12996123/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 820, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 820, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 819, cos1142o2c k) + cos1142o2c 820 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 819) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_819
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 820 - ((-1587823/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_820).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_821 : ((1090791/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 821, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 821, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 820, cos1142o2c k) + cos1142o2c 821 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 820) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_820
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 821 - ((1277779/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_821).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_822 : ((118507987/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 822, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 822, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 821, cos1142o2c k) + cos1142o2c 822 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 821) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_821
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 822 - ((9429887/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_822).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_823 : ((127883517/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 823, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 823, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 822, cos1142o2c k) + cos1142o2c 823 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 822) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_822
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 823 - ((937653/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_823).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_824 : ((66436281/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 824, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 824, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 823, cos1142o2c k) + cos1142o2c 824 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 823) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_823
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 824 - ((998009/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_824).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_825 : ((32794789/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 825, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 825, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 824, cos1142o2c k) + cos1142o2c 825 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 824) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_824
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 825 - ((-846203/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_825).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_826 : ((30897051/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 826, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 826, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 825, cos1142o2c k) + cos1142o2c 826 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 825) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_825
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 826 - ((-118593/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_826).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_827 : ((14198607/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 827, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 827, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 826, cos1142o2c k) + cos1142o2c 827 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 826) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_826
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 827 - ((-2499587/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_827).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_828 : ((105761319/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 828, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 828, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 827, cos1142o2c k) + cos1142o2c 828 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 827) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_827
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 828 - ((-7826537/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_828).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_829 : ((25919613/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 829, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 829, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 828, cos1142o2c k) + cos1142o2c 829 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 828) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_828
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 829 - ((-2081867/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_829).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_830 : ((6767719/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 830, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 830, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 829, cos1142o2c k) + cos1142o2c 830 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 829) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_829
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 830 - ((1151513/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_830).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_831 : ((29368741/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 831, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 831, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 830, cos1142o2c k) + cos1142o2c 831 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 830) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_830
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 831 - ((459623/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_831).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_832 : ((31769669/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 832, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 832, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 831, cos1142o2c k) + cos1142o2c 832 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 831) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_831
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 832 - ((1200589/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_832).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_833 : ((33186807/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 833, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 833, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 832, cos1142o2c k) + cos1142o2c 833 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 832) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_832
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 833 - ((354347/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_833).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_834 : ((131924347/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 834, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 834, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 833, cos1142o2c k) + cos1142o2c 834 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 833) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_833
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 834 - ((-821881/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_834).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_835 : ((12498709/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 835, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 835, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 834, cos1142o2c k) + cos1142o2c 835 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 834) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_834
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 835 - ((-6936257/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_835).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_836 : ((14382379/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 836, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 836, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 835, cos1142o2c k) + cos1142o2c 836 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 835) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_835
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 836 - ((-4963529/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_836).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_837 : ((21318923/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 837, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 837, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 836, cos1142o2c k) + cos1142o2c 837 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 836) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_836
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 837 - ((-8463417/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_837).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_838 : ((3230601/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 838, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 838, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 837, cos1142o2c k) + cos1142o2c 838 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 837) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_837
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 838 - ((-3214383/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_838).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_839 : ((106842193/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 839, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 839, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 838, cos1142o2c k) + cos1142o2c 839 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 838) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_838
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 839 - ((3463961/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_839).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_840 : ((115433913/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 840, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 840, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 839, cos1142o2c k) + cos1142o2c 840 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 839) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_839
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 840 - ((107409/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_840).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_841 : ((125331661/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 841, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 841, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 840, cos1142o2c k) + cos1142o2c 841 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 840) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_840
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 841 - ((2474687/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_841).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_842 : ((66072777/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 842, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 842, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 841, cos1142o2c k) + cos1142o2c 842 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 841) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_841
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 842 - ((6814893/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_842).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_843 : ((132864689/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 843, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 843, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 842, cos1142o2c k) + cos1142o2c 843 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 842) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_842
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 843 - ((144027/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_843).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_844 : ((63588673/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 844, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 844, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 843, cos1142o2c k) + cos1142o2c 844 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 843) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_843
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 844 - ((-5686343/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_844).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_845 : ((5879663/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 845, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 845, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 844, cos1142o2c k) + cos1142o2c 845 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 844) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_844
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 845 - ((-4791543/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_845).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_846 : ((1692599/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 846, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 846, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 845, cos1142o2c k) + cos1142o2c 846 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 845) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_845
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 846 - ((-2316481/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_846).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_847 : ((10343723/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 847, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 847, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 846, cos1142o2c k) + cos1142o2c 847 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 846) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_846
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 847 - ((-2444053/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_847).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_848 : ((26264889/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 848, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 848, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 847, cos1142o2c k) + cos1142o2c 848 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 847) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_847
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 848 - ((811663/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_848).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_849 : ((175747/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 849, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 849, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 848, cos1142o2c k) + cos1142o2c 849 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 848) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_848
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 849 - ((1854881/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_849).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_850 : ((122457469/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 850, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 850, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 849, cos1142o2c k) + cos1142o2c 850 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 849) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_849
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 850 - ((9980389/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_850).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_851 : ((16332517/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 851, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 851, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 850, cos1142o2c k) + cos1142o2c 851 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 850) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_850
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 851 - ((8203667/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_851).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_852 : ((133532737/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 852, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 852, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 851, cos1142o2c k) + cos1142o2c 852 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 851) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_851
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 852 - ((2873601/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_852).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_853 : ((649191/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 853, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 853, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 852, cos1142o2c k) + cos1142o2c 853 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 852) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_852
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 853 - ((-3693537/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_853).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_854 : ((121176449/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 854, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 854, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 853, cos1142o2c k) + cos1142o2c 854 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 853) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_853
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 854 - ((-8660751/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_854).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_855 : ((111280017/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 855, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 855, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 854, cos1142o2c k) + cos1142o2c 855 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 854) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_854
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 855 - ((-1236929/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_855).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_856 : ((104399867/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 856, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 856, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 855, cos1142o2c k) + cos1142o2c 856 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 855) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_855
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 856 - ((-137583/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_856).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_857 : ((12935129/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 857, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 857, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 856, cos1142o2c k) + cos1142o2c 857 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 856) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_856
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 857 - ((-183567/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_857).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_858 : ((544547/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 858, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 858, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 857, cos1142o2c k) + cos1142o2c 858 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 857) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_857
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 858 - ((678671/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_858).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_859 : ((59181637/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 859, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 859, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 858, cos1142o2c k) + cos1142o2c 859 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 858) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_858
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 859 - ((4727437/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_859).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_860 : ((63907131/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 860, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 860, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 859, cos1142o2c k) + cos1142o2c 860 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 859) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_859
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 860 - ((2362997/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_860).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_861 : ((133248143/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 861, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 861, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 860, cos1142o2c k) + cos1142o2c 861 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 860) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_860
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 861 - ((5434881/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_861).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_862 : ((132366557/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 862, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 862, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 861, cos1142o2c k) + cos1142o2c 862 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 861) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_861
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 862 - ((-440293/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_862).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_863 : ((62773889/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 863, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 863, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 862, cos1142o2c k) + cos1142o2c 863 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 862) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_862
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 863 - ((-6817779/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_863).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_864 : ((57836721/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 864, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 864, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 863, cos1142o2c k) + cos1142o2c 864 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 863) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_863
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 864 - ((-1234167/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_864).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_865 : ((6681399/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 865, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 865, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 864, cos1142o2c k) + cos1142o2c 865 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 864) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_864
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 865 - ((-4385029/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_865).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_866 : ((25729141/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 866, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 866, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 865, cos1142o2c k) + cos1142o2c 866 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 865) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_865
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 866 - ((-199241/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_866).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_867 : ((105380619/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 867, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 867, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 866, cos1142o2c k) + cos1142o2c 867 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 866) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_866
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 867 - ((493011/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_867).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_868 : ((11325819/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 868, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 868, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 867, cos1142o2c k) + cos1142o2c 868 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 867) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_867
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 868 - ((7878571/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_868).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_869 : ((7703563/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 869, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 869, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 868, cos1142o2c k) + cos1142o2c 869 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 868) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_868
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 869 - ((4999909/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_869).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_870 : ((65606359/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 870, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 870, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 869, cos1142o2c k) + cos1142o2c 870 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 869) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_869
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 870 - ((795671/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_870).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_871 : ((26764631/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 871, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 871, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 870, cos1142o2c k) + cos1142o2c 871 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 870) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_870
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 871 - ((2611437/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_871).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_872 : ((65005439/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 872, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 872, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 871, cos1142o2c k) + cos1142o2c 872 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 871) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_871
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 872 - ((-3811277/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_872).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_873 : ((121358431/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 873, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 873, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 872, cos1142o2c k) + cos1142o2c 873 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 872) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_872
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 873 - ((-8651447/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_873).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_874 : ((27859913/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 874, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 874, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 873, cos1142o2c k) + cos1142o2c 874 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 873) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_873
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 874 - ((-9917779/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_874).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_875 : ((26084599/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 875, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 875, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 874, cos1142o2c k) + cos1142o2c 875 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 874) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_874
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 875 - ((-221883/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_875).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_876 : ((51484163/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 876, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 876, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 875, cos1142o2c k) + cos1142o2c 876 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 875) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_875
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 876 - ((-136907/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_876).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_877 : ((4315399/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 877, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 877, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 876, cos1142o2c k) + cos1142o2c 877 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 876) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_876
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 877 - ((4917649/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_877).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_878 : ((14633897/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 878, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 878, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 877, cos1142o2c k) + cos1142o2c 878 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 877) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_877
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 878 - ((9187201/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_878).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_879 : ((12677397/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 879, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 879, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 878, cos1142o2c k) + cos1142o2c 879 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 878) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_878
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 879 - ((4851897/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_879).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_880 : ((26608307/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 880, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 880, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 879, cos1142o2c k) + cos1142o2c 880 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 879) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_879
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 880 - ((1253713/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_880).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_881 : ((8333173/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 881, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 881, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 880, cos1142o2c k) + cos1142o2c 881 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 880) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_880
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 881 - ((290233/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_881).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_882 : ((3188247/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 882, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 882, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 881, cos1142o2c k) + cos1142o2c 882 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 881) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_881
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 882 - ((-362493/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_882).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_883 : ((117990483/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 883, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 883, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 882, cos1142o2c k) + cos1142o2c 883 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 882) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_882
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 883 - ((-9538397/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_883).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_884 : ((54283029/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 884, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 884, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 883, cos1142o2c k) + cos1142o2c 884 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 883) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_883
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 884 - ((-376937/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_884).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_885 : ((103051487/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 885, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 885, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 884, cos1142o2c k) + cos1142o2c 885 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 884) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_884
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 885 - ((-5513571/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_885).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_886 : ((51829257/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 886, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 886, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 885, cos1142o2c k) + cos1142o2c 886 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 885) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_885
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 886 - ((608027/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_886).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_887 : ((55068653/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 887, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 887, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 886, cos1142o2c k) + cos1142o2c 887 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 886) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_886
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 887 - ((404987/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_887).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_888 : ((119889871/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 888, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 888, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 887, cos1142o2c k) + cos1142o2c 888 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 887) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_887
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 888 - ((1950713/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_888).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_889 : ((32254741/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 889, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 889, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 888, cos1142o2c k) + cos1142o2c 889 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 888) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_888
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 889 - ((9130093/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_889).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_890 : ((133888237/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 890, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 890, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 889, cos1142o2c k) + cos1142o2c 890 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 889) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_889
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 890 - ((4870273/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_890).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_891 : ((66282807/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 891, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 891, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 890, cos1142o2c k) + cos1142o2c 891 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 890) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_890
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 891 - ((-1321623/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_891).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_892 : ((15697683/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 892, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 892, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 891, cos1142o2c k) + cos1142o2c 892 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 891) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_891
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 892 - ((-139663/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_892).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_893 : ((28926259/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 893, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 893, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 892, cos1142o2c k) + cos1142o2c 893 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 892) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_892
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 893 - ((-2468857/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_893).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_894 : ((13354871/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 894, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 894, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 893, cos1142o2c k) + cos1142o2c 894 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 893) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_893
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 894 - ((-2216267/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_894).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_895 : ((2049521/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 895, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 895, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 894, cos1142o2c k) + cos1142o2c 895 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 894) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_894
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 895 - ((-2180959/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_895).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_896 : ((104327031/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 896, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 896, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 895, cos1142o2c k) + cos1142o2c 896 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 895) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_895
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 896 - ((1851981/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_896).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_897 : ((111659057/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 897, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 897, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 896, cos1142o2c k) + cos1142o2c 897 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 896) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_896
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 897 - ((3666513/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_897).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_898 : ((7599753/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 898, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 898, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 897, cos1142o2c k) + cos1142o2c 898 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 897) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_897
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 898 - ((9937991/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_898).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_899 : ((65126393/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 899, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 899, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 898, cos1142o2c k) + cos1142o2c 899 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 898) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_898
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 899 - ((4328869/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_899).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_900 : ((5370217/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 900, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 900, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 899, cos1142o2c k) + cos1142o2c 900 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 899) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_899
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 900 - ((4003639/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_900).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_901 : ((33012711/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 901, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 901, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 900, cos1142o2c k) + cos1142o2c 901 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 900) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_900
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 901 - ((-2203581/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_901).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_902 : ((31125063/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 902, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 902, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 901, cos1142o2c k) + cos1142o2c 902 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 901) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_901
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 902 - ((-943699/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_902).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_903 : ((57266647/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 903, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 903, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 902, cos1142o2c k) + cos1142o2c 903 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 902) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_902
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 903 - ((-4982979/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_903).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_904 : ((26501039/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 904, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 904, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 903, cos1142o2c k) + cos1142o2c 904 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 903) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_903
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 904 - ((-4264069/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_904).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_905 : ((25550197/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 905, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 905, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 904, cos1142o2c k) + cos1142o2c 905 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 904) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_904
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 905 - ((-29706/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_905).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_906 : ((52291127/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 906, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 906, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 905, cos1142o2c k) + cos1142o2c 906 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 905) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_905
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 906 - ((1191233/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_906).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_907 : ((28056829/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 907, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 907, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 906, cos1142o2c k) + cos1142o2c 907 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 906) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_906
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 907 - ((3823031/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_907).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_908 : ((122200993/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 908, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 908, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 907, cos1142o2c k) + cos1142o2c 908 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 907) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_907
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 908 - ((9974677/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_908).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_909 : ((65343379/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 909, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 909, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 908, cos1142o2c k) + cos1142o2c 909 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 908) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_908
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 909 - ((1697353/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_909).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_910 : ((134447497/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 910, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 910, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 909, cos1142o2c k) + cos1142o2c 910 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 909) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_909
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 910 - ((3761739/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_910).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_911 : ((26411047/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 911, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 911, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 910, cos1142o2c k) + cos1142o2c 911 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 910) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_910
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 911 - ((-1195631/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_911).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_912 : ((124424439/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 912, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 912, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 911, cos1142o2c k) + cos1142o2c 912 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 911) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_911
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 912 - ((-1907449/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_912).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_913 : ((114453167/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 913, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 913, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 912, cos1142o2c k) + cos1142o2c 913 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 912) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_912
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 913 - ((-311571/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_913).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_914 : ((21183241/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 914, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 914, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 913, cos1142o2c k) + cos1142o2c 914 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 913) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_913
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 914 - ((-4267981/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_914).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_915 : ((25508799/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 915, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 915, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 914, cos1142o2c k) + cos1142o2c 915 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 914) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_914
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 915 - ((-3880009/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_915).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_916 : ((3258363/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 916, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 916, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 915, cos1142o2c k) + cos1142o2c 916 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 915) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_915
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 916 - ((111671/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_916).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_917 : ((27941981/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 917, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 917, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 916, cos1142o2c k) + cos1142o2c 917 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 916) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_916
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 917 - ((1875327/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_917).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_918 : ((60858381/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 918, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 918, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 917, cos1142o2c k) + cos1142o2c 918 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 917) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_917
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 918 - ((4974919/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_918).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_919 : ((26077297/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 919, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 919, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 918, cos1142o2c k) + cos1142o2c 919 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 918) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_918
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 919 - ((8670723/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_919).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_920 : ((16817379/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 920, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 920, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 919, cos1142o2c k) + cos1142o2c 920 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 919) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_919
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 920 - ((4153547/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_920).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_921 : ((13262979/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 921, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 921, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 920, cos1142o2c k) + cos1142o2c 921 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 920) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_920
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 921 - ((-954121/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_921).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_922 : ((25074909/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 922, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 922, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 921, cos1142o2c k) + cos1142o2c 922 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 921) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_921
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 922 - ((-1450849/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_922).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_923 : ((57735819/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 923, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 923, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 922, cos1142o2c k) + cos1142o2c 923 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 922) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_922
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 923 - ((-9901907/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_923).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_924 : ((106591919/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 924, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 924, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 923, cos1142o2c k) + cos1142o2c 924 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 923) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_923
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 924 - ((-8878719/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_924).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_925 : ((51008553/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 925, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 925, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 924, cos1142o2c k) + cos1142o2c 925 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 924) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_924
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 925 - ((-4573813/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_925).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_926 : ((2585763/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 926, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 926, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 925, cos1142o2c k) + cos1142o2c 926 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 925) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_925
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 926 - ((707207/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_926).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_927 : ((110305659/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 927, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 927, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 926, cos1142o2c k) + cos1142o2c 927 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 926) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_926
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 927 - ((6876139/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_927).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_928 : ((24022269/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 928, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 928, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 927, cos1142o2c k) + cos1142o2c 928 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 927) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_927
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 928 - ((4903343/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_928).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_929 : ((16156161/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 929, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 929, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 928, cos1142o2c k) + cos1142o2c 929 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 928) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_928
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 929 - ((9138943/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_929).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_930 : ((5375069/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 930, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 930, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 929, cos1142o2c k) + cos1142o2c 930 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 929) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_929
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 930 - ((5128437/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_930).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_931 : ((33406209/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 931, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 931, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 930, cos1142o2c k) + cos1142o2c 931 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 930) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_930
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 931 - ((-750889/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_931).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_932 : ((127272471/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 932, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 932, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 931, cos1142o2c k) + cos1142o2c 932 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 931) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_931
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 932 - ((-1270273/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_932).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_933 : ((29408621/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 933, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 933, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 932, cos1142o2c k) + cos1142o2c 933 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 932) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_932
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 933 - ((-9636987/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_933).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_934 : ((27052641/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 934, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 934, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 933, cos1142o2c k) + cos1142o2c 934 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 933) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_933
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 934 - ((-235573/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_934).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_935 : ((102412367/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 935, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 935, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 934, cos1142o2c k) + cos1142o2c 935 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 934) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_934
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 935 - ((-5797197/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_935).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_936 : ((5116547/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 936, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 936, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 935, cos1142o2c k) + cos1142o2c 936 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 935) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_935
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 936 - ((-80427/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_936).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_937 : ((26997537/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 937, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 937, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 936, cos1142o2c k) + cos1142o2c 937 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 936) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_936
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 937 - ((353763/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_937).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_938 : ((117347977/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 938, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 938, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 937, cos1142o2c k) + cos1142o2c 938 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 937) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_937
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 938 - ((9358829/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_938).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_939 : ((127040143/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 939, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 939, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 938, cos1142o2c k) + cos1142o2c 939 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 938) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_938
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 939 - ((4846583/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_939).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_940 : ((33398193/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 940, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 940, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 939, cos1142o2c k) + cos1142o2c 940 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 939) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_939
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 940 - ((6553629/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_940).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_941 : ((134664889/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 941, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 941, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 940, cos1142o2c k) + cos1142o2c 941 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 940) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_940
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 941 - ((1073117/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_941).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_942 : ((16234867/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 942, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 942, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 941, cos1142o2c k) + cos1142o2c 942 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 941) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_941
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 942 - ((-4784953/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_942).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_943 : ((120944321/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 943, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 943, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 942, cos1142o2c k) + cos1142o2c 943 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 942) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_942
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 943 - ((-1786723/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_943).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_944 : ((111040017/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 944, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 944, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 943, cos1142o2c k) + cos1142o2c 944 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 943) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_943
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 944 - ((-1237913/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_944).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_945 : ((12959961/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 945, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 945, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 944, cos1142o2c k) + cos1142o2c 945 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 944) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_944
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 945 - ((-7359329/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_945).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_946 : ((101465623/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 946, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 946, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 945, cos1142o2c k) + cos1142o2c 946 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 945) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_945
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 946 - ((-442613/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_946).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_947 : ((52587413/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 947, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 947, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 946, cos1142o2c k) + cos1142o2c 947 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 946) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_946
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 947 - ((3710203/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_947).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_948 : ((113494353/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 948, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 948, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 947, cos1142o2c k) + cos1142o2c 948 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 947) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_947
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 948 - ((8320527/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_948).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_949 : ((6174619/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 949, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 949, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 948, cos1142o2c k) + cos1142o2c 949 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 948) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_948
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 949 - ((9999027/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_949).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_950 : ((131657227/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 950, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 950, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 949, cos1142o2c k) + cos1142o2c 950 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 949) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_949
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 950 - ((8165847/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_950).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_951 : ((135129507/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 951, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 951, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 950, cos1142o2c k) + cos1142o2c 951 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 950) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_950
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 951 - ((5427/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_951).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_952 : ((26539811/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 952, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 952, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 951, cos1142o2c k) + cos1142o2c 952 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 951) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_951
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 952 - ((-607363/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_952).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_953 : ((125219049/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 953, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 953, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 952, cos1142o2c k) + cos1142o2c 953 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 952) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_952
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 953 - ((-3739503/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_953).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_954 : ((57649353/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 954, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 954, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 953, cos1142o2c k) + cos1142o2c 954 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 953) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_953
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 954 - ((-9919343/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_954).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_955 : ((33246/3125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 955, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 955, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 954, cos1142o2c k) + cos1142o2c 955 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 954) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_954
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 955 - ((-4455253/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_955).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_956 : ((50787/5000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 956, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 956, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 955, cos1142o2c k) + cos1142o2c 956 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 955) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_955
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 956 - ((-24061/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_956).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_957 : ((3203761/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 957, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 957, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 956, cos1142o2c k) + cos1142o2c 957 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 956) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_956
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 957 - ((118419/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_957).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_958 : ((27223551/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 958, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 958, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 957, cos1142o2c k) + cos1142o2c 958 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 957) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_957
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 958 - ((1593713/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_958).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_959 : ((11849307/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 959, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 959, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 958, cos1142o2c k) + cos1142o2c 959 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 958) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_958
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 959 - ((4799933/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_959).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_960 : ((128011573/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 960, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 960, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 959, cos1142o2c k) + cos1142o2c 960 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 959) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_959
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 960 - ((9519503/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_960).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_961 : ((67090649/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 961, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 961, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 960, cos1142o2c k) + cos1142o2c 961 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 960) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_960
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 961 - ((246829/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_961).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_962 : ((33722867/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 962, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 962, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 961, cos1142o2c k) + cos1142o2c 962 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 961) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_961
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 962 - ((71117/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_962).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_963 : ((129903523/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 963, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 963, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 962, cos1142o2c k) + cos1142o2c 963 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 962) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_962
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 963 - ((-997389/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_963).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_964 : ((120924843/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 964, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 964, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 963, cos1142o2c k) + cos1142o2c 964 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 963) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_963
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 964 - ((-112221/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_964).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_965 : ((6938507/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 965, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 965, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 964, cos1142o2c k) + cos1142o2c 965 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 964) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_964
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 965 - ((-9907731/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_965).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_966 : ((6471601/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 966, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 966, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 965, cos1142o2c k) + cos1142o2c 966 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 965) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_965
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 966 - ((-933687/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_966).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_967 : ((10104437/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 967, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 967, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 966, cos1142o2c k) + cos1142o2c 967 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 966) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_966
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 967 - ((-1250123/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_967).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_968 : ((13044309/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 968, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 968, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 967, cos1142o2c k) + cos1142o2c 968 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 967) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_967
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 968 - ((1655551/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_968).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_969 : ((112352267/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 969, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 969, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 968, cos1142o2c k) + cos1142o2c 969 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 968) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_968
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 969 - ((1599759/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_969).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_970 : ((122336271/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 970, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 970, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 969, cos1142o2c k) + cos1142o2c 970 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 969) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_969
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 970 - ((2496251/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_970).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_971 : ((65472579/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 971, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 971, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 970, cos1142o2c k) + cos1142o2c 971 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 970) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_970
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 971 - ((8609887/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_971).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_972 : ((135288617/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 972, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 972, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 971, cos1142o2c k) + cos1142o2c 972 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 971) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_971
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 972 - ((4344459/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_972).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_973 : ((13391517/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 973, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 973, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 972, cos1142o2c k) + cos1142o2c 973 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 972) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_972
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 973 - ((-1372447/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_973).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_974 : ((1272883/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 974, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 974, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 973, cos1142o2c k) + cos1142o2c 974 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 973) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_973
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 974 - ((-662587/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_974).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_975 : ((117625011/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 975, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 975, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 974, cos1142o2c k) + cos1142o2c 975 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 974) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_974
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 975 - ((-9662289/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_975).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_976 : ((108146567/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 976, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 976, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 975, cos1142o2c k) + cos1142o2c 976 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 975) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_975
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 976 - ((-2369361/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_976).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_977 : ((51001953/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 977, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 977, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 976, cos1142o2c k) + cos1142o2c 977 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 976) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_976
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 977 - ((-6141661/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_977).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_978 : ((50615857/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 978, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 978, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 977, cos1142o2c k) + cos1142o2c 978 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 977) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_977
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 978 - ((-96399/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_978).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_979 : ((5304037/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 979, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 979, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 978, cos1142o2c k) + cos1142o2c 979 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 978) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_978
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 979 - ((2425013/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_979).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_980 : ((11494277/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 980, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 980, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 979, cos1142o2c k) + cos1142o2c 980 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 979) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_979
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 980 - ((886303/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_980).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_981 : ((124890943/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 981, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 981, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 980, cos1142o2c k) + cos1142o2c 981 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 980) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_980
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 981 - ((9949173/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_981).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_982 : ((66324463/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 982, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 982, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 981, cos1142o2c k) + cos1142o2c 982 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 981) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_981
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 982 - ((7758983/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_982).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_983 : ((135669681/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 983, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 983, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 982, cos1142o2c k) + cos1142o2c 983 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 982) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_982
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 983 - ((604351/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_983).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_984 : ((132967057/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 984, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 984, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 983, cos1142o2c k) + cos1142o2c 984 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 983) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_983
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 984 - ((-337703/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_984).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_985 : ((125429651/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 985, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 985, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 984, cos1142o2c k) + cos1142o2c 985 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 984) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_984
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 985 - ((-3768203/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_985).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_986 : ((115523471/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 986, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 986, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 985, cos1142o2c k) + cos1142o2c 986 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 985) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_985
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 986 - ((-495259/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_986).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_987 : ((53239617/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 987, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 987, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 986, cos1142o2c k) + cos1142o2c 987 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 986) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_986
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 987 - ((-9043237/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_987).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_988 : ((6327359/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 988, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 988, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 987, cos1142o2c k) + cos1142o2c 988 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 987) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_987
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 988 - ((-524049/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_988).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_989 : ((5074877/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 989, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 989, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 988, cos1142o2c k) + cos1142o2c 989 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 988) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_988
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 989 - ((65199/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_989).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_990 : ((107168813/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 990, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 990, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 989, cos1142o2c k) + cos1142o2c 990 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 989) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_989
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 990 - ((5672273/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_990).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_991 : ((116412413/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 991, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 991, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 990, cos1142o2c k) + cos1142o2c 991 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 990) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_990
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 991 - ((46223/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_991).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_992 : ((12624127/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 992, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 992, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 991, cos1142o2c k) + cos1142o2c 992 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 991) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_991
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 992 - ((9829857/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_992).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_993 : ((133488537/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 993, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 993, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 992, cos1142o2c k) + cos1142o2c 993 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 992) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_992
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 993 - ((7248267/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_993).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_994 : ((135825829/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 994, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 994, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 993, cos1142o2c k) + cos1142o2c 994 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 993) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_993
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 994 - ((584573/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_994).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_995 : ((33126907/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 995, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 995, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 994, cos1142o2c k) + cos1142o2c 995 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 994) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_994
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 995 - ((-3317201/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_995).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_996 : ((62300597/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 996, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 996, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 995, cos1142o2c k) + cos1142o2c 996 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 995) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_995
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 996 - ((-3952717/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_996).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_997 : ((114637239/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 997, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 997, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 996, cos1142o2c k) + cos1142o2c 997 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 996) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_996
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 997 - ((-1992591/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_997).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_998 : ((105795677/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 998, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 998, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 997, cos1142o2c k) + cos1142o2c 998 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 997) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_997
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 998 - ((-4420281/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_998).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_999 : ((20178021/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 999, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 999, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 998, cos1142o2c k) + cos1142o2c 999 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 998) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_998
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 999 - ((-1226143/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_999).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum1142o2_1000 : ((2536887/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 1000, cos1142o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 1000, cos1142o2c k)
      = (∑ k ∈ Finset.Icc 11 999, cos1142o2c k) + cos1142o2c 1000 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 999) (by norm_num) cos1142o2c
    simpa using h
  have hprev := psum1142o2_999
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos1142o2c 1000 - ((4691/80000 : ℚ) : ℝ) :=
    (abs_le.mp cos1142o2_br_1000).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 32768 in
theorem psum1142o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 1000 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos1142o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum1142o2_11
  · exact le_trans (by norm_num) psum1142o2_12
  · exact le_trans (by norm_num) psum1142o2_13
  · exact le_trans (by norm_num) psum1142o2_14
  · exact le_trans (by norm_num) psum1142o2_15
  · exact le_trans (by norm_num) psum1142o2_16
  · exact le_trans (by norm_num) psum1142o2_17
  · exact le_trans (by norm_num) psum1142o2_18
  · exact le_trans (by norm_num) psum1142o2_19
  · exact le_trans (by norm_num) psum1142o2_20
  · exact le_trans (by norm_num) psum1142o2_21
  · exact le_trans (by norm_num) psum1142o2_22
  · exact le_trans (by norm_num) psum1142o2_23
  · exact le_trans (by norm_num) psum1142o2_24
  · exact le_trans (by norm_num) psum1142o2_25
  · exact le_trans (by norm_num) psum1142o2_26
  · exact le_trans (by norm_num) psum1142o2_27
  · exact le_trans (by norm_num) psum1142o2_28
  · exact le_trans (by norm_num) psum1142o2_29
  · exact le_trans (by norm_num) psum1142o2_30
  · exact le_trans (by norm_num) psum1142o2_31
  · exact le_trans (by norm_num) psum1142o2_32
  · exact le_trans (by norm_num) psum1142o2_33
  · exact le_trans (by norm_num) psum1142o2_34
  · exact le_trans (by norm_num) psum1142o2_35
  · exact le_trans (by norm_num) psum1142o2_36
  · exact le_trans (by norm_num) psum1142o2_37
  · exact le_trans (by norm_num) psum1142o2_38
  · exact le_trans (by norm_num) psum1142o2_39
  · exact le_trans (by norm_num) psum1142o2_40
  · exact le_trans (by norm_num) psum1142o2_41
  · exact le_trans (by norm_num) psum1142o2_42
  · exact le_trans (by norm_num) psum1142o2_43
  · exact le_trans (by norm_num) psum1142o2_44
  · exact le_trans (by norm_num) psum1142o2_45
  · exact le_trans (by norm_num) psum1142o2_46
  · exact le_trans (by norm_num) psum1142o2_47
  · exact le_trans (by norm_num) psum1142o2_48
  · exact le_trans (by norm_num) psum1142o2_49
  · exact le_trans (by norm_num) psum1142o2_50
  · exact le_trans (by norm_num) psum1142o2_51
  · exact le_trans (by norm_num) psum1142o2_52
  · exact le_trans (by norm_num) psum1142o2_53
  · exact le_trans (by norm_num) psum1142o2_54
  · exact le_trans (by norm_num) psum1142o2_55
  · exact le_trans (by norm_num) psum1142o2_56
  · exact le_trans (by norm_num) psum1142o2_57
  · exact le_trans (by norm_num) psum1142o2_58
  · exact le_trans (by norm_num) psum1142o2_59
  · exact le_trans (by norm_num) psum1142o2_60
  · exact le_trans (by norm_num) psum1142o2_61
  · exact le_trans (by norm_num) psum1142o2_62
  · exact le_trans (by norm_num) psum1142o2_63
  · exact le_trans (by norm_num) psum1142o2_64
  · exact le_trans (by norm_num) psum1142o2_65
  · exact le_trans (by norm_num) psum1142o2_66
  · exact le_trans (by norm_num) psum1142o2_67
  · exact le_trans (by norm_num) psum1142o2_68
  · exact le_trans (by norm_num) psum1142o2_69
  · exact le_trans (by norm_num) psum1142o2_70
  · exact le_trans (by norm_num) psum1142o2_71
  · exact le_trans (by norm_num) psum1142o2_72
  · exact le_trans (by norm_num) psum1142o2_73
  · exact le_trans (by norm_num) psum1142o2_74
  · exact le_trans (by norm_num) psum1142o2_75
  · exact le_trans (by norm_num) psum1142o2_76
  · exact le_trans (by norm_num) psum1142o2_77
  · exact le_trans (by norm_num) psum1142o2_78
  · exact le_trans (by norm_num) psum1142o2_79
  · exact le_trans (by norm_num) psum1142o2_80
  · exact le_trans (by norm_num) psum1142o2_81
  · exact le_trans (by norm_num) psum1142o2_82
  · exact le_trans (by norm_num) psum1142o2_83
  · exact le_trans (by norm_num) psum1142o2_84
  · exact le_trans (by norm_num) psum1142o2_85
  · exact le_trans (by norm_num) psum1142o2_86
  · exact le_trans (by norm_num) psum1142o2_87
  · exact le_trans (by norm_num) psum1142o2_88
  · exact le_trans (by norm_num) psum1142o2_89
  · exact le_trans (by norm_num) psum1142o2_90
  · exact le_trans (by norm_num) psum1142o2_91
  · exact le_trans (by norm_num) psum1142o2_92
  · exact le_trans (by norm_num) psum1142o2_93
  · exact le_trans (by norm_num) psum1142o2_94
  · exact le_trans (by norm_num) psum1142o2_95
  · exact le_trans (by norm_num) psum1142o2_96
  · exact le_trans (by norm_num) psum1142o2_97
  · exact le_trans (by norm_num) psum1142o2_98
  · exact le_trans (by norm_num) psum1142o2_99
  · exact le_trans (by norm_num) psum1142o2_100
  · exact le_trans (by norm_num) psum1142o2_101
  · exact le_trans (by norm_num) psum1142o2_102
  · exact le_trans (by norm_num) psum1142o2_103
  · exact le_trans (by norm_num) psum1142o2_104
  · exact le_trans (by norm_num) psum1142o2_105
  · exact le_trans (by norm_num) psum1142o2_106
  · exact le_trans (by norm_num) psum1142o2_107
  · exact le_trans (by norm_num) psum1142o2_108
  · exact le_trans (by norm_num) psum1142o2_109
  · exact le_trans (by norm_num) psum1142o2_110
  · exact le_trans (by norm_num) psum1142o2_111
  · exact le_trans (by norm_num) psum1142o2_112
  · exact le_trans (by norm_num) psum1142o2_113
  · exact le_trans (by norm_num) psum1142o2_114
  · exact le_trans (by norm_num) psum1142o2_115
  · exact le_trans (by norm_num) psum1142o2_116
  · exact le_trans (by norm_num) psum1142o2_117
  · exact le_trans (by norm_num) psum1142o2_118
  · exact le_trans (by norm_num) psum1142o2_119
  · exact le_trans (by norm_num) psum1142o2_120
  · exact le_trans (by norm_num) psum1142o2_121
  · exact le_trans (by norm_num) psum1142o2_122
  · exact le_trans (by norm_num) psum1142o2_123
  · exact le_trans (by norm_num) psum1142o2_124
  · exact le_trans (by norm_num) psum1142o2_125
  · exact le_trans (by norm_num) psum1142o2_126
  · exact le_trans (by norm_num) psum1142o2_127
  · exact le_trans (by norm_num) psum1142o2_128
  · exact le_trans (by norm_num) psum1142o2_129
  · exact le_trans (by norm_num) psum1142o2_130
  · exact le_trans (by norm_num) psum1142o2_131
  · exact le_trans (by norm_num) psum1142o2_132
  · exact le_trans (by norm_num) psum1142o2_133
  · exact le_trans (by norm_num) psum1142o2_134
  · exact le_trans (by norm_num) psum1142o2_135
  · exact le_trans (by norm_num) psum1142o2_136
  · exact le_trans (by norm_num) psum1142o2_137
  · exact le_trans (by norm_num) psum1142o2_138
  · exact le_trans (by norm_num) psum1142o2_139
  · exact le_trans (by norm_num) psum1142o2_140
  · exact le_trans (by norm_num) psum1142o2_141
  · exact le_trans (by norm_num) psum1142o2_142
  · exact le_trans (by norm_num) psum1142o2_143
  · exact le_trans (by norm_num) psum1142o2_144
  · exact le_trans (by norm_num) psum1142o2_145
  · exact le_trans (by norm_num) psum1142o2_146
  · exact le_trans (by norm_num) psum1142o2_147
  · exact le_trans (by norm_num) psum1142o2_148
  · exact le_trans (by norm_num) psum1142o2_149
  · exact le_trans (by norm_num) psum1142o2_150
  · exact le_trans (by norm_num) psum1142o2_151
  · exact le_trans (by norm_num) psum1142o2_152
  · exact le_trans (by norm_num) psum1142o2_153
  · exact le_trans (by norm_num) psum1142o2_154
  · exact le_trans (by norm_num) psum1142o2_155
  · exact le_trans (by norm_num) psum1142o2_156
  · exact le_trans (by norm_num) psum1142o2_157
  · exact le_trans (by norm_num) psum1142o2_158
  · exact le_trans (by norm_num) psum1142o2_159
  · exact le_trans (by norm_num) psum1142o2_160
  · exact le_trans (by norm_num) psum1142o2_161
  · exact le_trans (by norm_num) psum1142o2_162
  · exact le_trans (by norm_num) psum1142o2_163
  · exact le_trans (by norm_num) psum1142o2_164
  · exact le_trans (by norm_num) psum1142o2_165
  · exact le_trans (by norm_num) psum1142o2_166
  · exact le_trans (by norm_num) psum1142o2_167
  · exact le_trans (by norm_num) psum1142o2_168
  · exact le_trans (by norm_num) psum1142o2_169
  · exact le_trans (by norm_num) psum1142o2_170
  · exact le_trans (by norm_num) psum1142o2_171
  · exact le_trans (by norm_num) psum1142o2_172
  · exact le_trans (by norm_num) psum1142o2_173
  · exact le_trans (by norm_num) psum1142o2_174
  · exact le_trans (by norm_num) psum1142o2_175
  · exact le_trans (by norm_num) psum1142o2_176
  · exact le_trans (by norm_num) psum1142o2_177
  · exact le_trans (by norm_num) psum1142o2_178
  · exact le_trans (by norm_num) psum1142o2_179
  · exact le_trans (by norm_num) psum1142o2_180
  · exact le_trans (by norm_num) psum1142o2_181
  · exact le_trans (by norm_num) psum1142o2_182
  · exact le_trans (by norm_num) psum1142o2_183
  · exact le_trans (by norm_num) psum1142o2_184
  · exact le_trans (by norm_num) psum1142o2_185
  · exact le_trans (by norm_num) psum1142o2_186
  · exact le_trans (by norm_num) psum1142o2_187
  · exact le_trans (by norm_num) psum1142o2_188
  · exact le_trans (by norm_num) psum1142o2_189
  · exact le_trans (by norm_num) psum1142o2_190
  · exact le_trans (by norm_num) psum1142o2_191
  · exact le_trans (by norm_num) psum1142o2_192
  · exact le_trans (by norm_num) psum1142o2_193
  · exact le_trans (by norm_num) psum1142o2_194
  · exact le_trans (by norm_num) psum1142o2_195
  · exact le_trans (by norm_num) psum1142o2_196
  · exact le_trans (by norm_num) psum1142o2_197
  · exact le_trans (by norm_num) psum1142o2_198
  · exact le_trans (by norm_num) psum1142o2_199
  · exact le_trans (by norm_num) psum1142o2_200
  · exact le_trans (by norm_num) psum1142o2_201
  · exact le_trans (by norm_num) psum1142o2_202
  · exact le_trans (by norm_num) psum1142o2_203
  · exact le_trans (by norm_num) psum1142o2_204
  · exact le_trans (by norm_num) psum1142o2_205
  · exact le_trans (by norm_num) psum1142o2_206
  · exact le_trans (by norm_num) psum1142o2_207
  · exact le_trans (by norm_num) psum1142o2_208
  · exact le_trans (by norm_num) psum1142o2_209
  · exact le_trans (by norm_num) psum1142o2_210
  · exact le_trans (by norm_num) psum1142o2_211
  · exact le_trans (by norm_num) psum1142o2_212
  · exact le_trans (by norm_num) psum1142o2_213
  · exact le_trans (by norm_num) psum1142o2_214
  · exact le_trans (by norm_num) psum1142o2_215
  · exact le_trans (by norm_num) psum1142o2_216
  · exact le_trans (by norm_num) psum1142o2_217
  · exact le_trans (by norm_num) psum1142o2_218
  · exact le_trans (by norm_num) psum1142o2_219
  · exact le_trans (by norm_num) psum1142o2_220
  · exact le_trans (by norm_num) psum1142o2_221
  · exact le_trans (by norm_num) psum1142o2_222
  · exact le_trans (by norm_num) psum1142o2_223
  · exact le_trans (by norm_num) psum1142o2_224
  · exact le_trans (by norm_num) psum1142o2_225
  · exact le_trans (by norm_num) psum1142o2_226
  · exact le_trans (by norm_num) psum1142o2_227
  · exact le_trans (by norm_num) psum1142o2_228
  · exact le_trans (by norm_num) psum1142o2_229
  · exact le_trans (by norm_num) psum1142o2_230
  · exact le_trans (by norm_num) psum1142o2_231
  · exact le_trans (by norm_num) psum1142o2_232
  · exact le_trans (by norm_num) psum1142o2_233
  · exact le_trans (by norm_num) psum1142o2_234
  · exact le_trans (by norm_num) psum1142o2_235
  · exact le_trans (by norm_num) psum1142o2_236
  · exact le_trans (by norm_num) psum1142o2_237
  · exact le_trans (by norm_num) psum1142o2_238
  · exact le_trans (by norm_num) psum1142o2_239
  · exact le_trans (by norm_num) psum1142o2_240
  · exact le_trans (by norm_num) psum1142o2_241
  · exact le_trans (by norm_num) psum1142o2_242
  · exact le_trans (by norm_num) psum1142o2_243
  · exact le_trans (by norm_num) psum1142o2_244
  · exact le_trans (by norm_num) psum1142o2_245
  · exact le_trans (by norm_num) psum1142o2_246
  · exact le_trans (by norm_num) psum1142o2_247
  · exact le_trans (by norm_num) psum1142o2_248
  · exact le_trans (by norm_num) psum1142o2_249
  · exact le_trans (by norm_num) psum1142o2_250
  · exact le_trans (by norm_num) psum1142o2_251
  · exact le_trans (by norm_num) psum1142o2_252
  · exact le_trans (by norm_num) psum1142o2_253
  · exact le_trans (by norm_num) psum1142o2_254
  · exact le_trans (by norm_num) psum1142o2_255
  · exact le_trans (by norm_num) psum1142o2_256
  · exact le_trans (by norm_num) psum1142o2_257
  · exact le_trans (by norm_num) psum1142o2_258
  · exact le_trans (by norm_num) psum1142o2_259
  · exact le_trans (by norm_num) psum1142o2_260
  · exact le_trans (by norm_num) psum1142o2_261
  · exact le_trans (by norm_num) psum1142o2_262
  · exact le_trans (by norm_num) psum1142o2_263
  · exact le_trans (by norm_num) psum1142o2_264
  · exact le_trans (by norm_num) psum1142o2_265
  · exact le_trans (by norm_num) psum1142o2_266
  · exact le_trans (by norm_num) psum1142o2_267
  · exact le_trans (by norm_num) psum1142o2_268
  · exact le_trans (by norm_num) psum1142o2_269
  · exact le_trans (by norm_num) psum1142o2_270
  · exact le_trans (by norm_num) psum1142o2_271
  · exact le_trans (by norm_num) psum1142o2_272
  · exact le_trans (by norm_num) psum1142o2_273
  · exact le_trans (by norm_num) psum1142o2_274
  · exact le_trans (by norm_num) psum1142o2_275
  · exact le_trans (by norm_num) psum1142o2_276
  · exact le_trans (by norm_num) psum1142o2_277
  · exact le_trans (by norm_num) psum1142o2_278
  · exact le_trans (by norm_num) psum1142o2_279
  · exact le_trans (by norm_num) psum1142o2_280
  · exact le_trans (by norm_num) psum1142o2_281
  · exact le_trans (by norm_num) psum1142o2_282
  · exact le_trans (by norm_num) psum1142o2_283
  · exact le_trans (by norm_num) psum1142o2_284
  · exact le_trans (by norm_num) psum1142o2_285
  · exact le_trans (by norm_num) psum1142o2_286
  · exact le_trans (by norm_num) psum1142o2_287
  · exact le_trans (by norm_num) psum1142o2_288
  · exact le_trans (by norm_num) psum1142o2_289
  · exact le_trans (by norm_num) psum1142o2_290
  · exact le_trans (by norm_num) psum1142o2_291
  · exact le_trans (by norm_num) psum1142o2_292
  · exact le_trans (by norm_num) psum1142o2_293
  · exact le_trans (by norm_num) psum1142o2_294
  · exact le_trans (by norm_num) psum1142o2_295
  · exact le_trans (by norm_num) psum1142o2_296
  · exact le_trans (by norm_num) psum1142o2_297
  · exact le_trans (by norm_num) psum1142o2_298
  · exact le_trans (by norm_num) psum1142o2_299
  · exact le_trans (by norm_num) psum1142o2_300
  · exact le_trans (by norm_num) psum1142o2_301
  · exact le_trans (by norm_num) psum1142o2_302
  · exact le_trans (by norm_num) psum1142o2_303
  · exact le_trans (by norm_num) psum1142o2_304
  · exact le_trans (by norm_num) psum1142o2_305
  · exact le_trans (by norm_num) psum1142o2_306
  · exact le_trans (by norm_num) psum1142o2_307
  · exact le_trans (by norm_num) psum1142o2_308
  · exact le_trans (by norm_num) psum1142o2_309
  · exact le_trans (by norm_num) psum1142o2_310
  · exact le_trans (by norm_num) psum1142o2_311
  · exact le_trans (by norm_num) psum1142o2_312
  · exact le_trans (by norm_num) psum1142o2_313
  · exact le_trans (by norm_num) psum1142o2_314
  · exact le_trans (by norm_num) psum1142o2_315
  · exact le_trans (by norm_num) psum1142o2_316
  · exact le_trans (by norm_num) psum1142o2_317
  · exact le_trans (by norm_num) psum1142o2_318
  · exact le_trans (by norm_num) psum1142o2_319
  · exact le_trans (by norm_num) psum1142o2_320
  · exact le_trans (by norm_num) psum1142o2_321
  · exact le_trans (by norm_num) psum1142o2_322
  · exact le_trans (by norm_num) psum1142o2_323
  · exact le_trans (by norm_num) psum1142o2_324
  · exact le_trans (by norm_num) psum1142o2_325
  · exact le_trans (by norm_num) psum1142o2_326
  · exact le_trans (by norm_num) psum1142o2_327
  · exact le_trans (by norm_num) psum1142o2_328
  · exact le_trans (by norm_num) psum1142o2_329
  · exact le_trans (by norm_num) psum1142o2_330
  · exact le_trans (by norm_num) psum1142o2_331
  · exact le_trans (by norm_num) psum1142o2_332
  · exact le_trans (by norm_num) psum1142o2_333
  · exact le_trans (by norm_num) psum1142o2_334
  · exact le_trans (by norm_num) psum1142o2_335
  · exact le_trans (by norm_num) psum1142o2_336
  · exact le_trans (by norm_num) psum1142o2_337
  · exact le_trans (by norm_num) psum1142o2_338
  · exact le_trans (by norm_num) psum1142o2_339
  · exact le_trans (by norm_num) psum1142o2_340
  · exact le_trans (by norm_num) psum1142o2_341
  · exact le_trans (by norm_num) psum1142o2_342
  · exact le_trans (by norm_num) psum1142o2_343
  · exact le_trans (by norm_num) psum1142o2_344
  · exact le_trans (by norm_num) psum1142o2_345
  · exact le_trans (by norm_num) psum1142o2_346
  · exact le_trans (by norm_num) psum1142o2_347
  · exact le_trans (by norm_num) psum1142o2_348
  · exact le_trans (by norm_num) psum1142o2_349
  · exact le_trans (by norm_num) psum1142o2_350
  · exact le_trans (by norm_num) psum1142o2_351
  · exact le_trans (by norm_num) psum1142o2_352
  · exact le_trans (by norm_num) psum1142o2_353
  · exact le_trans (by norm_num) psum1142o2_354
  · exact le_trans (by norm_num) psum1142o2_355
  · exact le_trans (by norm_num) psum1142o2_356
  · exact le_trans (by norm_num) psum1142o2_357
  · exact le_trans (by norm_num) psum1142o2_358
  · exact le_trans (by norm_num) psum1142o2_359
  · exact le_trans (by norm_num) psum1142o2_360
  · exact le_trans (by norm_num) psum1142o2_361
  · exact le_trans (by norm_num) psum1142o2_362
  · exact le_trans (by norm_num) psum1142o2_363
  · exact le_trans (by norm_num) psum1142o2_364
  · exact le_trans (by norm_num) psum1142o2_365
  · exact le_trans (by norm_num) psum1142o2_366
  · exact le_trans (by norm_num) psum1142o2_367
  · exact le_trans (by norm_num) psum1142o2_368
  · exact le_trans (by norm_num) psum1142o2_369
  · exact le_trans (by norm_num) psum1142o2_370
  · exact le_trans (by norm_num) psum1142o2_371
  · exact le_trans (by norm_num) psum1142o2_372
  · exact le_trans (by norm_num) psum1142o2_373
  · exact le_trans (by norm_num) psum1142o2_374
  · exact le_trans (by norm_num) psum1142o2_375
  · exact le_trans (by norm_num) psum1142o2_376
  · exact le_trans (by norm_num) psum1142o2_377
  · exact le_trans (by norm_num) psum1142o2_378
  · exact le_trans (by norm_num) psum1142o2_379
  · exact le_trans (by norm_num) psum1142o2_380
  · exact le_trans (by norm_num) psum1142o2_381
  · exact le_trans (by norm_num) psum1142o2_382
  · exact le_trans (by norm_num) psum1142o2_383
  · exact le_trans (by norm_num) psum1142o2_384
  · exact le_trans (by norm_num) psum1142o2_385
  · exact le_trans (by norm_num) psum1142o2_386
  · exact le_trans (by norm_num) psum1142o2_387
  · exact le_trans (by norm_num) psum1142o2_388
  · exact le_trans (by norm_num) psum1142o2_389
  · exact le_trans (by norm_num) psum1142o2_390
  · exact le_trans (by norm_num) psum1142o2_391
  · exact le_trans (by norm_num) psum1142o2_392
  · exact le_trans (by norm_num) psum1142o2_393
  · exact le_trans (by norm_num) psum1142o2_394
  · exact le_trans (by norm_num) psum1142o2_395
  · exact le_trans (by norm_num) psum1142o2_396
  · exact le_trans (by norm_num) psum1142o2_397
  · exact le_trans (by norm_num) psum1142o2_398
  · exact le_trans (by norm_num) psum1142o2_399
  · exact le_trans (by norm_num) psum1142o2_400
  · exact le_trans (by norm_num) psum1142o2_401
  · exact le_trans (by norm_num) psum1142o2_402
  · exact le_trans (by norm_num) psum1142o2_403
  · exact le_trans (by norm_num) psum1142o2_404
  · exact le_trans (by norm_num) psum1142o2_405
  · exact le_trans (by norm_num) psum1142o2_406
  · exact le_trans (by norm_num) psum1142o2_407
  · exact le_trans (by norm_num) psum1142o2_408
  · exact le_trans (by norm_num) psum1142o2_409
  · exact le_trans (by norm_num) psum1142o2_410
  · exact le_trans (by norm_num) psum1142o2_411
  · exact le_trans (by norm_num) psum1142o2_412
  · exact le_trans (by norm_num) psum1142o2_413
  · exact le_trans (by norm_num) psum1142o2_414
  · exact le_trans (by norm_num) psum1142o2_415
  · exact le_trans (by norm_num) psum1142o2_416
  · exact le_trans (by norm_num) psum1142o2_417
  · exact le_trans (by norm_num) psum1142o2_418
  · exact le_trans (by norm_num) psum1142o2_419
  · exact le_trans (by norm_num) psum1142o2_420
  · exact le_trans (by norm_num) psum1142o2_421
  · exact le_trans (by norm_num) psum1142o2_422
  · exact le_trans (by norm_num) psum1142o2_423
  · exact le_trans (by norm_num) psum1142o2_424
  · exact le_trans (by norm_num) psum1142o2_425
  · exact le_trans (by norm_num) psum1142o2_426
  · exact le_trans (by norm_num) psum1142o2_427
  · exact le_trans (by norm_num) psum1142o2_428
  · exact le_trans (by norm_num) psum1142o2_429
  · exact le_trans (by norm_num) psum1142o2_430
  · exact le_trans (by norm_num) psum1142o2_431
  · exact le_trans (by norm_num) psum1142o2_432
  · exact le_trans (by norm_num) psum1142o2_433
  · exact le_trans (by norm_num) psum1142o2_434
  · exact le_trans (by norm_num) psum1142o2_435
  · exact le_trans (by norm_num) psum1142o2_436
  · exact le_trans (by norm_num) psum1142o2_437
  · exact le_trans (by norm_num) psum1142o2_438
  · exact le_trans (by norm_num) psum1142o2_439
  · exact le_trans (by norm_num) psum1142o2_440
  · exact le_trans (by norm_num) psum1142o2_441
  · exact le_trans (by norm_num) psum1142o2_442
  · exact le_trans (by norm_num) psum1142o2_443
  · exact le_trans (by norm_num) psum1142o2_444
  · exact le_trans (by norm_num) psum1142o2_445
  · exact le_trans (by norm_num) psum1142o2_446
  · exact le_trans (by norm_num) psum1142o2_447
  · exact le_trans (by norm_num) psum1142o2_448
  · exact le_trans (by norm_num) psum1142o2_449
  · exact le_trans (by norm_num) psum1142o2_450
  · exact le_trans (by norm_num) psum1142o2_451
  · exact le_trans (by norm_num) psum1142o2_452
  · exact le_trans (by norm_num) psum1142o2_453
  · exact le_trans (by norm_num) psum1142o2_454
  · exact le_trans (by norm_num) psum1142o2_455
  · exact le_trans (by norm_num) psum1142o2_456
  · exact le_trans (by norm_num) psum1142o2_457
  · exact le_trans (by norm_num) psum1142o2_458
  · exact le_trans (by norm_num) psum1142o2_459
  · exact le_trans (by norm_num) psum1142o2_460
  · exact le_trans (by norm_num) psum1142o2_461
  · exact le_trans (by norm_num) psum1142o2_462
  · exact le_trans (by norm_num) psum1142o2_463
  · exact le_trans (by norm_num) psum1142o2_464
  · exact le_trans (by norm_num) psum1142o2_465
  · exact le_trans (by norm_num) psum1142o2_466
  · exact le_trans (by norm_num) psum1142o2_467
  · exact le_trans (by norm_num) psum1142o2_468
  · exact le_trans (by norm_num) psum1142o2_469
  · exact le_trans (by norm_num) psum1142o2_470
  · exact le_trans (by norm_num) psum1142o2_471
  · exact le_trans (by norm_num) psum1142o2_472
  · exact le_trans (by norm_num) psum1142o2_473
  · exact le_trans (by norm_num) psum1142o2_474
  · exact le_trans (by norm_num) psum1142o2_475
  · exact le_trans (by norm_num) psum1142o2_476
  · exact le_trans (by norm_num) psum1142o2_477
  · exact le_trans (by norm_num) psum1142o2_478
  · exact le_trans (by norm_num) psum1142o2_479
  · exact le_trans (by norm_num) psum1142o2_480
  · exact le_trans (by norm_num) psum1142o2_481
  · exact le_trans (by norm_num) psum1142o2_482
  · exact le_trans (by norm_num) psum1142o2_483
  · exact le_trans (by norm_num) psum1142o2_484
  · exact le_trans (by norm_num) psum1142o2_485
  · exact le_trans (by norm_num) psum1142o2_486
  · exact le_trans (by norm_num) psum1142o2_487
  · exact le_trans (by norm_num) psum1142o2_488
  · exact le_trans (by norm_num) psum1142o2_489
  · exact le_trans (by norm_num) psum1142o2_490
  · exact le_trans (by norm_num) psum1142o2_491
  · exact le_trans (by norm_num) psum1142o2_492
  · exact le_trans (by norm_num) psum1142o2_493
  · exact le_trans (by norm_num) psum1142o2_494
  · exact le_trans (by norm_num) psum1142o2_495
  · exact le_trans (by norm_num) psum1142o2_496
  · exact le_trans (by norm_num) psum1142o2_497
  · exact le_trans (by norm_num) psum1142o2_498
  · exact le_trans (by norm_num) psum1142o2_499
  · exact le_trans (by norm_num) psum1142o2_500
  · exact le_trans (by norm_num) psum1142o2_501
  · exact le_trans (by norm_num) psum1142o2_502
  · exact le_trans (by norm_num) psum1142o2_503
  · exact le_trans (by norm_num) psum1142o2_504
  · exact le_trans (by norm_num) psum1142o2_505
  · exact le_trans (by norm_num) psum1142o2_506
  · exact le_trans (by norm_num) psum1142o2_507
  · exact le_trans (by norm_num) psum1142o2_508
  · exact le_trans (by norm_num) psum1142o2_509
  · exact le_trans (by norm_num) psum1142o2_510
  · exact le_trans (by norm_num) psum1142o2_511
  · exact le_trans (by norm_num) psum1142o2_512
  · exact le_trans (by norm_num) psum1142o2_513
  · exact le_trans (by norm_num) psum1142o2_514
  · exact le_trans (by norm_num) psum1142o2_515
  · exact le_trans (by norm_num) psum1142o2_516
  · exact le_trans (by norm_num) psum1142o2_517
  · exact le_trans (by norm_num) psum1142o2_518
  · exact le_trans (by norm_num) psum1142o2_519
  · exact le_trans (by norm_num) psum1142o2_520
  · exact le_trans (by norm_num) psum1142o2_521
  · exact le_trans (by norm_num) psum1142o2_522
  · exact le_trans (by norm_num) psum1142o2_523
  · exact le_trans (by norm_num) psum1142o2_524
  · exact le_trans (by norm_num) psum1142o2_525
  · exact le_trans (by norm_num) psum1142o2_526
  · exact le_trans (by norm_num) psum1142o2_527
  · exact le_trans (by norm_num) psum1142o2_528
  · exact le_trans (by norm_num) psum1142o2_529
  · exact le_trans (by norm_num) psum1142o2_530
  · exact le_trans (by norm_num) psum1142o2_531
  · exact le_trans (by norm_num) psum1142o2_532
  · exact le_trans (by norm_num) psum1142o2_533
  · exact le_trans (by norm_num) psum1142o2_534
  · exact le_trans (by norm_num) psum1142o2_535
  · exact le_trans (by norm_num) psum1142o2_536
  · exact le_trans (by norm_num) psum1142o2_537
  · exact le_trans (by norm_num) psum1142o2_538
  · exact le_trans (by norm_num) psum1142o2_539
  · exact le_trans (by norm_num) psum1142o2_540
  · exact le_trans (by norm_num) psum1142o2_541
  · exact le_trans (by norm_num) psum1142o2_542
  · exact le_trans (by norm_num) psum1142o2_543
  · exact le_trans (by norm_num) psum1142o2_544
  · exact le_trans (by norm_num) psum1142o2_545
  · exact le_trans (by norm_num) psum1142o2_546
  · exact le_trans (by norm_num) psum1142o2_547
  · exact le_trans (by norm_num) psum1142o2_548
  · exact le_trans (by norm_num) psum1142o2_549
  · exact le_trans (by norm_num) psum1142o2_550
  · exact le_trans (by norm_num) psum1142o2_551
  · exact le_trans (by norm_num) psum1142o2_552
  · exact le_trans (by norm_num) psum1142o2_553
  · exact le_trans (by norm_num) psum1142o2_554
  · exact le_trans (by norm_num) psum1142o2_555
  · exact le_trans (by norm_num) psum1142o2_556
  · exact le_trans (by norm_num) psum1142o2_557
  · exact le_trans (by norm_num) psum1142o2_558
  · exact le_trans (by norm_num) psum1142o2_559
  · exact le_trans (by norm_num) psum1142o2_560
  · exact le_trans (by norm_num) psum1142o2_561
  · exact le_trans (by norm_num) psum1142o2_562
  · exact le_trans (by norm_num) psum1142o2_563
  · exact le_trans (by norm_num) psum1142o2_564
  · exact le_trans (by norm_num) psum1142o2_565
  · exact le_trans (by norm_num) psum1142o2_566
  · exact le_trans (by norm_num) psum1142o2_567
  · exact le_trans (by norm_num) psum1142o2_568
  · exact le_trans (by norm_num) psum1142o2_569
  · exact le_trans (by norm_num) psum1142o2_570
  · exact le_trans (by norm_num) psum1142o2_571
  · exact le_trans (by norm_num) psum1142o2_572
  · exact le_trans (by norm_num) psum1142o2_573
  · exact le_trans (by norm_num) psum1142o2_574
  · exact le_trans (by norm_num) psum1142o2_575
  · exact le_trans (by norm_num) psum1142o2_576
  · exact le_trans (by norm_num) psum1142o2_577
  · exact le_trans (by norm_num) psum1142o2_578
  · exact le_trans (by norm_num) psum1142o2_579
  · exact le_trans (by norm_num) psum1142o2_580
  · exact le_trans (by norm_num) psum1142o2_581
  · exact le_trans (by norm_num) psum1142o2_582
  · exact le_trans (by norm_num) psum1142o2_583
  · exact le_trans (by norm_num) psum1142o2_584
  · exact le_trans (by norm_num) psum1142o2_585
  · exact le_trans (by norm_num) psum1142o2_586
  · exact le_trans (by norm_num) psum1142o2_587
  · exact le_trans (by norm_num) psum1142o2_588
  · exact le_trans (by norm_num) psum1142o2_589
  · exact le_trans (by norm_num) psum1142o2_590
  · exact le_trans (by norm_num) psum1142o2_591
  · exact le_trans (by norm_num) psum1142o2_592
  · exact le_trans (by norm_num) psum1142o2_593
  · exact le_trans (by norm_num) psum1142o2_594
  · exact le_trans (by norm_num) psum1142o2_595
  · exact le_trans (by norm_num) psum1142o2_596
  · exact le_trans (by norm_num) psum1142o2_597
  · exact le_trans (by norm_num) psum1142o2_598
  · exact le_trans (by norm_num) psum1142o2_599
  · exact le_trans (by norm_num) psum1142o2_600
  · exact le_trans (by norm_num) psum1142o2_601
  · exact le_trans (by norm_num) psum1142o2_602
  · exact le_trans (by norm_num) psum1142o2_603
  · exact le_trans (by norm_num) psum1142o2_604
  · exact le_trans (by norm_num) psum1142o2_605
  · exact le_trans (by norm_num) psum1142o2_606
  · exact le_trans (by norm_num) psum1142o2_607
  · exact le_trans (by norm_num) psum1142o2_608
  · exact le_trans (by norm_num) psum1142o2_609
  · exact le_trans (by norm_num) psum1142o2_610
  · exact le_trans (by norm_num) psum1142o2_611
  · exact le_trans (by norm_num) psum1142o2_612
  · exact le_trans (by norm_num) psum1142o2_613
  · exact le_trans (by norm_num) psum1142o2_614
  · exact le_trans (by norm_num) psum1142o2_615
  · exact le_trans (by norm_num) psum1142o2_616
  · exact le_trans (by norm_num) psum1142o2_617
  · exact le_trans (by norm_num) psum1142o2_618
  · exact le_trans (by norm_num) psum1142o2_619
  · exact le_trans (by norm_num) psum1142o2_620
  · exact le_trans (by norm_num) psum1142o2_621
  · exact le_trans (by norm_num) psum1142o2_622
  · exact le_trans (by norm_num) psum1142o2_623
  · exact le_trans (by norm_num) psum1142o2_624
  · exact le_trans (by norm_num) psum1142o2_625
  · exact le_trans (by norm_num) psum1142o2_626
  · exact le_trans (by norm_num) psum1142o2_627
  · exact le_trans (by norm_num) psum1142o2_628
  · exact le_trans (by norm_num) psum1142o2_629
  · exact le_trans (by norm_num) psum1142o2_630
  · exact le_trans (by norm_num) psum1142o2_631
  · exact le_trans (by norm_num) psum1142o2_632
  · exact le_trans (by norm_num) psum1142o2_633
  · exact le_trans (by norm_num) psum1142o2_634
  · exact le_trans (by norm_num) psum1142o2_635
  · exact le_trans (by norm_num) psum1142o2_636
  · exact le_trans (by norm_num) psum1142o2_637
  · exact le_trans (by norm_num) psum1142o2_638
  · exact le_trans (by norm_num) psum1142o2_639
  · exact le_trans (by norm_num) psum1142o2_640
  · exact le_trans (by norm_num) psum1142o2_641
  · exact le_trans (by norm_num) psum1142o2_642
  · exact le_trans (by norm_num) psum1142o2_643
  · exact le_trans (by norm_num) psum1142o2_644
  · exact le_trans (by norm_num) psum1142o2_645
  · exact le_trans (by norm_num) psum1142o2_646
  · exact le_trans (by norm_num) psum1142o2_647
  · exact le_trans (by norm_num) psum1142o2_648
  · exact le_trans (by norm_num) psum1142o2_649
  · exact le_trans (by norm_num) psum1142o2_650
  · exact le_trans (by norm_num) psum1142o2_651
  · exact le_trans (by norm_num) psum1142o2_652
  · exact le_trans (by norm_num) psum1142o2_653
  · exact le_trans (by norm_num) psum1142o2_654
  · exact le_trans (by norm_num) psum1142o2_655
  · exact le_trans (by norm_num) psum1142o2_656
  · exact le_trans (by norm_num) psum1142o2_657
  · exact le_trans (by norm_num) psum1142o2_658
  · exact le_trans (by norm_num) psum1142o2_659
  · exact le_trans (by norm_num) psum1142o2_660
  · exact le_trans (by norm_num) psum1142o2_661
  · exact le_trans (by norm_num) psum1142o2_662
  · exact le_trans (by norm_num) psum1142o2_663
  · exact le_trans (by norm_num) psum1142o2_664
  · exact le_trans (by norm_num) psum1142o2_665
  · exact le_trans (by norm_num) psum1142o2_666
  · exact le_trans (by norm_num) psum1142o2_667
  · exact le_trans (by norm_num) psum1142o2_668
  · exact le_trans (by norm_num) psum1142o2_669
  · exact le_trans (by norm_num) psum1142o2_670
  · exact le_trans (by norm_num) psum1142o2_671
  · exact le_trans (by norm_num) psum1142o2_672
  · exact le_trans (by norm_num) psum1142o2_673
  · exact le_trans (by norm_num) psum1142o2_674
  · exact le_trans (by norm_num) psum1142o2_675
  · exact le_trans (by norm_num) psum1142o2_676
  · exact le_trans (by norm_num) psum1142o2_677
  · exact le_trans (by norm_num) psum1142o2_678
  · exact le_trans (by norm_num) psum1142o2_679
  · exact le_trans (by norm_num) psum1142o2_680
  · exact le_trans (by norm_num) psum1142o2_681
  · exact le_trans (by norm_num) psum1142o2_682
  · exact le_trans (by norm_num) psum1142o2_683
  · exact le_trans (by norm_num) psum1142o2_684
  · exact le_trans (by norm_num) psum1142o2_685
  · exact le_trans (by norm_num) psum1142o2_686
  · exact le_trans (by norm_num) psum1142o2_687
  · exact le_trans (by norm_num) psum1142o2_688
  · exact le_trans (by norm_num) psum1142o2_689
  · exact le_trans (by norm_num) psum1142o2_690
  · exact le_trans (by norm_num) psum1142o2_691
  · exact le_trans (by norm_num) psum1142o2_692
  · exact le_trans (by norm_num) psum1142o2_693
  · exact le_trans (by norm_num) psum1142o2_694
  · exact le_trans (by norm_num) psum1142o2_695
  · exact le_trans (by norm_num) psum1142o2_696
  · exact le_trans (by norm_num) psum1142o2_697
  · exact le_trans (by norm_num) psum1142o2_698
  · exact le_trans (by norm_num) psum1142o2_699
  · exact le_trans (by norm_num) psum1142o2_700
  · exact le_trans (by norm_num) psum1142o2_701
  · exact le_trans (by norm_num) psum1142o2_702
  · exact le_trans (by norm_num) psum1142o2_703
  · exact le_trans (by norm_num) psum1142o2_704
  · exact le_trans (by norm_num) psum1142o2_705
  · exact le_trans (by norm_num) psum1142o2_706
  · exact le_trans (by norm_num) psum1142o2_707
  · exact le_trans (by norm_num) psum1142o2_708
  · exact le_trans (by norm_num) psum1142o2_709
  · exact le_trans (by norm_num) psum1142o2_710
  · exact le_trans (by norm_num) psum1142o2_711
  · exact le_trans (by norm_num) psum1142o2_712
  · exact le_trans (by norm_num) psum1142o2_713
  · exact le_trans (by norm_num) psum1142o2_714
  · exact le_trans (by norm_num) psum1142o2_715
  · exact le_trans (by norm_num) psum1142o2_716
  · exact le_trans (by norm_num) psum1142o2_717
  · exact le_trans (by norm_num) psum1142o2_718
  · exact le_trans (by norm_num) psum1142o2_719
  · exact le_trans (by norm_num) psum1142o2_720
  · exact le_trans (by norm_num) psum1142o2_721
  · exact le_trans (by norm_num) psum1142o2_722
  · exact le_trans (by norm_num) psum1142o2_723
  · exact le_trans (by norm_num) psum1142o2_724
  · exact le_trans (by norm_num) psum1142o2_725
  · exact le_trans (by norm_num) psum1142o2_726
  · exact le_trans (by norm_num) psum1142o2_727
  · exact le_trans (by norm_num) psum1142o2_728
  · exact le_trans (by norm_num) psum1142o2_729
  · exact le_trans (by norm_num) psum1142o2_730
  · exact le_trans (by norm_num) psum1142o2_731
  · exact le_trans (by norm_num) psum1142o2_732
  · exact le_trans (by norm_num) psum1142o2_733
  · exact le_trans (by norm_num) psum1142o2_734
  · exact le_trans (by norm_num) psum1142o2_735
  · exact le_trans (by norm_num) psum1142o2_736
  · exact le_trans (by norm_num) psum1142o2_737
  · exact le_trans (by norm_num) psum1142o2_738
  · exact le_trans (by norm_num) psum1142o2_739
  · exact le_trans (by norm_num) psum1142o2_740
  · exact le_trans (by norm_num) psum1142o2_741
  · exact le_trans (by norm_num) psum1142o2_742
  · exact le_trans (by norm_num) psum1142o2_743
  · exact le_trans (by norm_num) psum1142o2_744
  · exact le_trans (by norm_num) psum1142o2_745
  · exact le_trans (by norm_num) psum1142o2_746
  · exact le_trans (by norm_num) psum1142o2_747
  · exact le_trans (by norm_num) psum1142o2_748
  · exact le_trans (by norm_num) psum1142o2_749
  · exact le_trans (by norm_num) psum1142o2_750
  · exact le_trans (by norm_num) psum1142o2_751
  · exact le_trans (by norm_num) psum1142o2_752
  · exact le_trans (by norm_num) psum1142o2_753
  · exact le_trans (by norm_num) psum1142o2_754
  · exact le_trans (by norm_num) psum1142o2_755
  · exact le_trans (by norm_num) psum1142o2_756
  · exact le_trans (by norm_num) psum1142o2_757
  · exact le_trans (by norm_num) psum1142o2_758
  · exact le_trans (by norm_num) psum1142o2_759
  · exact le_trans (by norm_num) psum1142o2_760
  · exact le_trans (by norm_num) psum1142o2_761
  · exact le_trans (by norm_num) psum1142o2_762
  · exact le_trans (by norm_num) psum1142o2_763
  · exact le_trans (by norm_num) psum1142o2_764
  · exact le_trans (by norm_num) psum1142o2_765
  · exact le_trans (by norm_num) psum1142o2_766
  · exact le_trans (by norm_num) psum1142o2_767
  · exact le_trans (by norm_num) psum1142o2_768
  · exact le_trans (by norm_num) psum1142o2_769
  · exact le_trans (by norm_num) psum1142o2_770
  · exact le_trans (by norm_num) psum1142o2_771
  · exact le_trans (by norm_num) psum1142o2_772
  · exact le_trans (by norm_num) psum1142o2_773
  · exact le_trans (by norm_num) psum1142o2_774
  · exact le_trans (by norm_num) psum1142o2_775
  · exact le_trans (by norm_num) psum1142o2_776
  · exact le_trans (by norm_num) psum1142o2_777
  · exact le_trans (by norm_num) psum1142o2_778
  · exact le_trans (by norm_num) psum1142o2_779
  · exact le_trans (by norm_num) psum1142o2_780
  · exact le_trans (by norm_num) psum1142o2_781
  · exact le_trans (by norm_num) psum1142o2_782
  · exact le_trans (by norm_num) psum1142o2_783
  · exact le_trans (by norm_num) psum1142o2_784
  · exact le_trans (by norm_num) psum1142o2_785
  · exact le_trans (by norm_num) psum1142o2_786
  · exact le_trans (by norm_num) psum1142o2_787
  · exact le_trans (by norm_num) psum1142o2_788
  · exact le_trans (by norm_num) psum1142o2_789
  · exact le_trans (by norm_num) psum1142o2_790
  · exact le_trans (by norm_num) psum1142o2_791
  · exact le_trans (by norm_num) psum1142o2_792
  · exact le_trans (by norm_num) psum1142o2_793
  · exact le_trans (by norm_num) psum1142o2_794
  · exact le_trans (by norm_num) psum1142o2_795
  · exact le_trans (by norm_num) psum1142o2_796
  · exact le_trans (by norm_num) psum1142o2_797
  · exact le_trans (by norm_num) psum1142o2_798
  · exact le_trans (by norm_num) psum1142o2_799
  · exact le_trans (by norm_num) psum1142o2_800
  · exact le_trans (by norm_num) psum1142o2_801
  · exact le_trans (by norm_num) psum1142o2_802
  · exact le_trans (by norm_num) psum1142o2_803
  · exact le_trans (by norm_num) psum1142o2_804
  · exact le_trans (by norm_num) psum1142o2_805
  · exact le_trans (by norm_num) psum1142o2_806
  · exact le_trans (by norm_num) psum1142o2_807
  · exact le_trans (by norm_num) psum1142o2_808
  · exact le_trans (by norm_num) psum1142o2_809
  · exact le_trans (by norm_num) psum1142o2_810
  · exact le_trans (by norm_num) psum1142o2_811
  · exact le_trans (by norm_num) psum1142o2_812
  · exact le_trans (by norm_num) psum1142o2_813
  · exact le_trans (by norm_num) psum1142o2_814
  · exact le_trans (by norm_num) psum1142o2_815
  · exact le_trans (by norm_num) psum1142o2_816
  · exact le_trans (by norm_num) psum1142o2_817
  · exact le_trans (by norm_num) psum1142o2_818
  · exact le_trans (by norm_num) psum1142o2_819
  · exact le_trans (by norm_num) psum1142o2_820
  · exact le_trans (by norm_num) psum1142o2_821
  · exact le_trans (by norm_num) psum1142o2_822
  · exact le_trans (by norm_num) psum1142o2_823
  · exact le_trans (by norm_num) psum1142o2_824
  · exact le_trans (by norm_num) psum1142o2_825
  · exact le_trans (by norm_num) psum1142o2_826
  · exact le_trans (by norm_num) psum1142o2_827
  · exact le_trans (by norm_num) psum1142o2_828
  · exact le_trans (by norm_num) psum1142o2_829
  · exact le_trans (by norm_num) psum1142o2_830
  · exact le_trans (by norm_num) psum1142o2_831
  · exact le_trans (by norm_num) psum1142o2_832
  · exact le_trans (by norm_num) psum1142o2_833
  · exact le_trans (by norm_num) psum1142o2_834
  · exact le_trans (by norm_num) psum1142o2_835
  · exact le_trans (by norm_num) psum1142o2_836
  · exact le_trans (by norm_num) psum1142o2_837
  · exact le_trans (by norm_num) psum1142o2_838
  · exact le_trans (by norm_num) psum1142o2_839
  · exact le_trans (by norm_num) psum1142o2_840
  · exact le_trans (by norm_num) psum1142o2_841
  · exact le_trans (by norm_num) psum1142o2_842
  · exact le_trans (by norm_num) psum1142o2_843
  · exact le_trans (by norm_num) psum1142o2_844
  · exact le_trans (by norm_num) psum1142o2_845
  · exact le_trans (by norm_num) psum1142o2_846
  · exact le_trans (by norm_num) psum1142o2_847
  · exact le_trans (by norm_num) psum1142o2_848
  · exact le_trans (by norm_num) psum1142o2_849
  · exact le_trans (by norm_num) psum1142o2_850
  · exact le_trans (by norm_num) psum1142o2_851
  · exact le_trans (by norm_num) psum1142o2_852
  · exact le_trans (by norm_num) psum1142o2_853
  · exact le_trans (by norm_num) psum1142o2_854
  · exact le_trans (by norm_num) psum1142o2_855
  · exact le_trans (by norm_num) psum1142o2_856
  · exact le_trans (by norm_num) psum1142o2_857
  · exact le_trans (by norm_num) psum1142o2_858
  · exact le_trans (by norm_num) psum1142o2_859
  · exact le_trans (by norm_num) psum1142o2_860
  · exact le_trans (by norm_num) psum1142o2_861
  · exact le_trans (by norm_num) psum1142o2_862
  · exact le_trans (by norm_num) psum1142o2_863
  · exact le_trans (by norm_num) psum1142o2_864
  · exact le_trans (by norm_num) psum1142o2_865
  · exact le_trans (by norm_num) psum1142o2_866
  · exact le_trans (by norm_num) psum1142o2_867
  · exact le_trans (by norm_num) psum1142o2_868
  · exact le_trans (by norm_num) psum1142o2_869
  · exact le_trans (by norm_num) psum1142o2_870
  · exact le_trans (by norm_num) psum1142o2_871
  · exact le_trans (by norm_num) psum1142o2_872
  · exact le_trans (by norm_num) psum1142o2_873
  · exact le_trans (by norm_num) psum1142o2_874
  · exact le_trans (by norm_num) psum1142o2_875
  · exact le_trans (by norm_num) psum1142o2_876
  · exact le_trans (by norm_num) psum1142o2_877
  · exact le_trans (by norm_num) psum1142o2_878
  · exact le_trans (by norm_num) psum1142o2_879
  · exact le_trans (by norm_num) psum1142o2_880
  · exact le_trans (by norm_num) psum1142o2_881
  · exact le_trans (by norm_num) psum1142o2_882
  · exact le_trans (by norm_num) psum1142o2_883
  · exact le_trans (by norm_num) psum1142o2_884
  · exact le_trans (by norm_num) psum1142o2_885
  · exact le_trans (by norm_num) psum1142o2_886
  · exact le_trans (by norm_num) psum1142o2_887
  · exact le_trans (by norm_num) psum1142o2_888
  · exact le_trans (by norm_num) psum1142o2_889
  · exact le_trans (by norm_num) psum1142o2_890
  · exact le_trans (by norm_num) psum1142o2_891
  · exact le_trans (by norm_num) psum1142o2_892
  · exact le_trans (by norm_num) psum1142o2_893
  · exact le_trans (by norm_num) psum1142o2_894
  · exact le_trans (by norm_num) psum1142o2_895
  · exact le_trans (by norm_num) psum1142o2_896
  · exact le_trans (by norm_num) psum1142o2_897
  · exact le_trans (by norm_num) psum1142o2_898
  · exact le_trans (by norm_num) psum1142o2_899
  · exact le_trans (by norm_num) psum1142o2_900
  · exact le_trans (by norm_num) psum1142o2_901
  · exact le_trans (by norm_num) psum1142o2_902
  · exact le_trans (by norm_num) psum1142o2_903
  · exact le_trans (by norm_num) psum1142o2_904
  · exact le_trans (by norm_num) psum1142o2_905
  · exact le_trans (by norm_num) psum1142o2_906
  · exact le_trans (by norm_num) psum1142o2_907
  · exact le_trans (by norm_num) psum1142o2_908
  · exact le_trans (by norm_num) psum1142o2_909
  · exact le_trans (by norm_num) psum1142o2_910
  · exact le_trans (by norm_num) psum1142o2_911
  · exact le_trans (by norm_num) psum1142o2_912
  · exact le_trans (by norm_num) psum1142o2_913
  · exact le_trans (by norm_num) psum1142o2_914
  · exact le_trans (by norm_num) psum1142o2_915
  · exact le_trans (by norm_num) psum1142o2_916
  · exact le_trans (by norm_num) psum1142o2_917
  · exact le_trans (by norm_num) psum1142o2_918
  · exact le_trans (by norm_num) psum1142o2_919
  · exact le_trans (by norm_num) psum1142o2_920
  · exact le_trans (by norm_num) psum1142o2_921
  · exact le_trans (by norm_num) psum1142o2_922
  · exact le_trans (by norm_num) psum1142o2_923
  · exact le_trans (by norm_num) psum1142o2_924
  · exact le_trans (by norm_num) psum1142o2_925
  · exact le_trans (by norm_num) psum1142o2_926
  · exact le_trans (by norm_num) psum1142o2_927
  · exact le_trans (by norm_num) psum1142o2_928
  · exact le_trans (by norm_num) psum1142o2_929
  · exact le_trans (by norm_num) psum1142o2_930
  · exact le_trans (by norm_num) psum1142o2_931
  · exact le_trans (by norm_num) psum1142o2_932
  · exact le_trans (by norm_num) psum1142o2_933
  · exact le_trans (by norm_num) psum1142o2_934
  · exact le_trans (by norm_num) psum1142o2_935
  · exact le_trans (by norm_num) psum1142o2_936
  · exact le_trans (by norm_num) psum1142o2_937
  · exact le_trans (by norm_num) psum1142o2_938
  · exact le_trans (by norm_num) psum1142o2_939
  · exact le_trans (by norm_num) psum1142o2_940
  · exact le_trans (by norm_num) psum1142o2_941
  · exact le_trans (by norm_num) psum1142o2_942
  · exact le_trans (by norm_num) psum1142o2_943
  · exact le_trans (by norm_num) psum1142o2_944
  · exact le_trans (by norm_num) psum1142o2_945
  · exact le_trans (by norm_num) psum1142o2_946
  · exact le_trans (by norm_num) psum1142o2_947
  · exact le_trans (by norm_num) psum1142o2_948
  · exact le_trans (by norm_num) psum1142o2_949
  · exact le_trans (by norm_num) psum1142o2_950
  · exact le_trans (by norm_num) psum1142o2_951
  · exact le_trans (by norm_num) psum1142o2_952
  · exact le_trans (by norm_num) psum1142o2_953
  · exact le_trans (by norm_num) psum1142o2_954
  · exact le_trans (by norm_num) psum1142o2_955
  · exact le_trans (by norm_num) psum1142o2_956
  · exact le_trans (by norm_num) psum1142o2_957
  · exact le_trans (by norm_num) psum1142o2_958
  · exact le_trans (by norm_num) psum1142o2_959
  · exact le_trans (by norm_num) psum1142o2_960
  · exact le_trans (by norm_num) psum1142o2_961
  · exact le_trans (by norm_num) psum1142o2_962
  · exact le_trans (by norm_num) psum1142o2_963
  · exact le_trans (by norm_num) psum1142o2_964
  · exact le_trans (by norm_num) psum1142o2_965
  · exact le_trans (by norm_num) psum1142o2_966
  · exact le_trans (by norm_num) psum1142o2_967
  · exact le_trans (by norm_num) psum1142o2_968
  · exact le_trans (by norm_num) psum1142o2_969
  · exact le_trans (by norm_num) psum1142o2_970
  · exact le_trans (by norm_num) psum1142o2_971
  · exact le_trans (by norm_num) psum1142o2_972
  · exact le_trans (by norm_num) psum1142o2_973
  · exact le_trans (by norm_num) psum1142o2_974
  · exact le_trans (by norm_num) psum1142o2_975
  · exact le_trans (by norm_num) psum1142o2_976
  · exact le_trans (by norm_num) psum1142o2_977
  · exact le_trans (by norm_num) psum1142o2_978
  · exact le_trans (by norm_num) psum1142o2_979
  · exact le_trans (by norm_num) psum1142o2_980
  · exact le_trans (by norm_num) psum1142o2_981
  · exact le_trans (by norm_num) psum1142o2_982
  · exact le_trans (by norm_num) psum1142o2_983
  · exact le_trans (by norm_num) psum1142o2_984
  · exact le_trans (by norm_num) psum1142o2_985
  · exact le_trans (by norm_num) psum1142o2_986
  · exact le_trans (by norm_num) psum1142o2_987
  · exact le_trans (by norm_num) psum1142o2_988
  · exact le_trans (by norm_num) psum1142o2_989
  · exact le_trans (by norm_num) psum1142o2_990
  · exact le_trans (by norm_num) psum1142o2_991
  · exact le_trans (by norm_num) psum1142o2_992
  · exact le_trans (by norm_num) psum1142o2_993
  · exact le_trans (by norm_num) psum1142o2_994
  · exact le_trans (by norm_num) psum1142o2_995
  · exact le_trans (by norm_num) psum1142o2_996
  · exact le_trans (by norm_num) psum1142o2_997
  · exact le_trans (by norm_num) psum1142o2_998
  · exact le_trans (by norm_num) psum1142o2_999
  · exact le_trans (by norm_num) psum1142o2_1000

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum1142o2_floor
#print axioms CriticalLinePhasor.DVP.psum1142o2_1000
end AxiomAudit
