import RequestProject.DVPCos995o2Table

/-!
# The cosine partial-sum floor, `t = 995/2` (N = 1000)
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 995/2` segment certificate. -/
def cos995o2c (n : ℕ) : ℝ := Real.cos (((995:ℕ):ℝ) * (Real.log n / 2))

theorem psum995o2_11 : ((6581373/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos995o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 11 - ((6582373/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum995o2_12 : ((6823841/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos995o2c k) + cos995o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_11
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 12 - ((60867/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_13 : ((15211041/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos995o2c k) + cos995o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_12
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 13 - ((41941/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_14 : ((6221859/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos995o2c k) + cos995o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_13
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 14 - ((1935479/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_15 : ((100343/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos995o2c k) + cos995o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_14
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 15 - ((-2207889/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_16 : ((6260689/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos995o2c k) + cos995o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_15
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 16 - ((-9793191/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_17 : ((1296647/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos995o2c k) + cos995o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_16
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 17 - ((-2481521/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_18 : ((1898433/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos995o2c k) + cos995o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_17
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 18 - ((1259617/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_19 : ((13993477/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos995o2c k) + cos995o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_18
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 19 - ((1280149/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_20 : ((8516387/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos995o2c k) + cos995o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_19
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 20 - ((3040297/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_21 : ((655839/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos995o2c k) + cos995o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_20
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 21 - ((4600893/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_22 : ((6518179/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos995o2c k) + cos995o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_21
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 22 - ((-39961/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_23 : ((1562339/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos995o2c k) + cos995o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_22
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 23 - ((-268573/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_24 : ((18477247/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos995o2c k) + cos995o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_23
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 24 - ((-6519177/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_25 : ((25287353/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos995o2c k) + cos995o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_24
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 25 - ((3405553/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_26 : ((35160569/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos995o2c k) + cos995o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_25
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 26 - ((1234277/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_27 : ((44890429/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos995o2c k) + cos995o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_26
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 27 - ((486543/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_28 : ((50383369/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos995o2c k) + cos995o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_27
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 28 - ((274697/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_29 : ((4313953/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos995o2c k) + cos995o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_28
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 29 - ((-7242839/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_30 : ((4965999/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos995o2c k) + cos995o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_29
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 30 - ((-1705269/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_31 : ((748107/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos995o2c k) + cos995o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_30
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 31 - ((509491/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_32 : ((39253479/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos995o2c k) + cos995o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_31
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 32 - ((-8624369/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_33 : ((4523223/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos995o2c k) + cos995o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_32
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 33 - ((5979751/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_34 : ((4736591/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos995o2c k) + cos995o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_33
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 34 - ((53367/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_35 : ((37388699/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos995o2c k) + cos995o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_34
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 35 - ((-9976211/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_36 : ((36856417/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos995o2c k) + cos995o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_35
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 36 - ((-265641/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_37 : ((4533159/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos995o2c k) + cos995o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_36
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 37 - ((8476173/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_38 : ((11046061/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos995o2c k) + cos995o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_37
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 38 - ((1979943/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_39 : ((64013833/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos995o2c k) + cos995o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_38
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 39 - ((549033/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_40 : ((36326967/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos995o2c k) + cos995o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_39
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 40 - ((8641101/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_41 : ((16470563/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos995o2c k) + cos995o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_40
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 41 - ((9699881/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_42 : ((45902543/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos995o2c k) + cos995o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_41
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 42 - ((9453271/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_43 : ((19100149/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos995o2c k) + cos995o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_42
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 43 - ((3696659/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_44 : ((44340051/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos995o2c k) + cos995o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_43
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 44 - ((-6819643/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_45 : ((80237509/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos995o2c k) + cos995o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_44
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 45 - ((-8441593/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_46 : ((86102659/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos995o2c k) + cos995o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_45
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 46 - ((117323/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_47 : ((18427093/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos995o2c k) + cos995o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_46
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 47 - ((3016903/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_48 : ((10276753/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos995o2c k) + cos995o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_47
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 48 - ((-9920441/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_49 : ((87952321/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos995o2c k) + cos995o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_48
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 49 - ((5739297/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_50 : ((176199/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos995o2c k) + cos995o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_49
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 50 - ((148179/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_51 : ((83822519/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos995o2c k) + cos995o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_50
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 51 - ((-4275981/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_52 : ((2815327/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos995o2c k) + cos995o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_51
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 52 - ((1253789/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_53 : ((41713133/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos995o2c k) + cos995o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_52
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 53 - ((-3331599/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_54 : ((89103047/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos995o2c k) + cos995o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_53
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 54 - ((5677781/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_55 : ((4303667/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos995o2c k) + cos995o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_54
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 55 - ((-3028707/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_56 : ((84549579/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos995o2c k) + cos995o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_55
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 56 - ((-1522761/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_57 : ((5720311/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos995o2c k) + cos995o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_56
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 57 - ((6976397/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_58 : ((16305489/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos995o2c k) + cos995o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_57
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 58 - ((-9996531/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_59 : ((21947411/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos995o2c k) + cos995o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_58
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 59 - ((6263199/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_60 : ((91557413/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos995o2c k) + cos995o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_59
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 60 - ((3768769/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_61 : ((81557871/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos995o2c k) + cos995o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_60
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 61 - ((-4999271/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_62 : ((83724917/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos995o2c k) + cos995o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_61
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 62 - ((1084023/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_63 : ((93201199/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos995o2c k) + cos995o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_62
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 63 - ((4738641/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_64 : ((45095987/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos995o2c k) + cos995o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_63
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 64 - ((-120329/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_65 : ((80326647/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos995o2c k) + cos995o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_64
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 65 - ((-9864327/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_66 : ((79392133/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos995o2c k) + cos995o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_65
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 66 - ((-466757/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_67 : ((22081087/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos995o2c k) + cos995o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_66
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 67 - ((1786643/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_68 : ((48227539/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos995o2c k) + cos995o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_67
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 68 - ((813173/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_69 : ((4807639/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos995o2c k) + cos995o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_68
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 69 - ((-150649/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_70 : ((88285507/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos995o2c k) + cos995o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_69
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 70 - ((-7866273/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_71 : ((78342969/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos995o2c k) + cos995o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_70
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 71 - ((-4970769/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_72 : ((8906907/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos995o2c k) + cos995o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_71
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 72 - ((-7086713/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_73 : ((69183041/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos995o2c k) + cos995o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_72
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 73 - ((-414243/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_74 : ((14383291/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos995o2c k) + cos995o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_73
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 74 - ((1367207/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_75 : ((3125569/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos995o2c k) + cos995o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_74
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 75 - ((622377/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_76 : ((3457299/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos995o2c k) + cos995o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_75
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 76 - ((33177/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_77 : ((47872777/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos995o2c k) + cos995o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_76
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 77 - ((9314079/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_78 : ((105466713/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos995o2c k) + cos995o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_77
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 78 - ((9722159/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_79 : ((28825223/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos995o2c k) + cos995o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_78
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 79 - ((9835179/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_80 : ((62543161/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos995o2c k) + cos995o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_79
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 80 - ((978643/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_81 : ((16826069/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos995o2c k) + cos995o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_80
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 81 - ((952323/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_82 : ((143436309/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos995o2c k) + cos995o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_81
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 82 - ((8828757/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_83 : ((75404483/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos995o2c k) + cos995o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_82
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 83 - ((7373657/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_84 : ((77819131/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos995o2c k) + cos995o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_83
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 84 - ((603787/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_85 : ((156720781/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos995o2c k) + cos995o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_84
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 85 - ((1083519/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_86 : ((153235813/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos995o2c k) + cos995o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_85
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 86 - ((-54437/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_87 : ((145479869/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos995o2c k) + cos995o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_86
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 87 - ((-121171/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_88 : ((135515733/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos995o2c k) + cos995o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_87
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 88 - ((-77837/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_89 : ((127127123/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos995o2c k) + cos995o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_88
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 89 - ((-838761/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_90 : ((124453651/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos995o2c k) + cos995o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_89
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 90 - ((-334059/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_91 : ((129381043/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos995o2c k) + cos995o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_90
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 91 - ((616049/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_92 : ((139161469/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos995o2c k) + cos995o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_91
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 92 - ((4890713/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_93 : ((146839091/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos995o2c k) + cos995o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_92
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 93 - ((3839311/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_94 : ((145971419/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos995o2c k) + cos995o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_93
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 94 - ((-54167/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_95 : ((137034131/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos995o2c k) + cos995o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_94
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 95 - ((-279259/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_96 : ((8051677/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos995o2c k) + cos995o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_95
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 96 - ((-8206299/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_97 : ((13047013/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos995o2c k) + cos995o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_96
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 97 - ((822149/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_98 : ((70108491/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos995o2c k) + cos995o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_97
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 98 - ((2436963/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_99 : ((145557211/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos995o2c k) + cos995o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_98
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 99 - ((5341229/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_100 : ((138964687/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos995o2c k) + cos995o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_99
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 100 - ((-1647881/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_101 : ((130101861/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos995o2c k) + cos995o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_100
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 101 - ((-4430913/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_102 : ((2077899/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos995o2c k) + cos995o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_101
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 102 - ((115387/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_103 : ((142870213/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos995o2c k) + cos995o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_102
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 103 - ((9885677/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_104 : ((1111719/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos995o2c k) + cos995o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_103
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 104 - ((-569181/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_105 : ((66149697/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos995o2c k) + cos995o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_104
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 105 - ((-4999819/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_106 : ((132350867/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos995o2c k) + cos995o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_105
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 106 - ((52473/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_107 : ((17792399/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos995o2c k) + cos995o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_106
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 107 - ((399573/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_108 : ((141035349/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos995o2c k) + cos995o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_107
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 108 - ((-1302843/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_109 : ((65682391/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos995o2c k) + cos995o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_108
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 109 - ((-9669567/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_110 : ((67751493/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos995o2c k) + cos995o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_109
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 110 - ((1034801/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_111 : ((143541893/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos995o2c k) + cos995o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_110
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 111 - ((8039907/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_112 : ((33946751/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos995o2c k) + cos995o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_111
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 112 - ((-7753889/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_113 : ((65976559/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos995o2c k) + cos995o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_112
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 113 - ((-1916443/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_114 : ((35482873/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos995o2c k) + cos995o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_113
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 114 - ((4989687/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_115 : ((138945359/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos995o2c k) + cos995o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_114
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 115 - ((-2985133/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_116 : ((26269763/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos995o2c k) + cos995o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_115
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 116 - ((-949443/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_117 : ((35118983/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos995o2c k) + cos995o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_116
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 117 - ((9128117/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_118 : ((139898887/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos995o2c k) + cos995o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_117
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 118 - ((-115209/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_119 : ((16436023/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos995o2c k) + cos995o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_118
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 119 - ((-8409703/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_120 : ((35123007/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos995o2c k) + cos995o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_119
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 120 - ((2251211/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_121 : ((139156801/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos995o2c k) + cos995o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_120
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 121 - ((-1334227/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_122 : ((65924699/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos995o2c k) + cos995o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_121
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 122 - ((-7306403/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_123 : ((70853711/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos995o2c k) + cos995o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_122
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 123 - ((616189/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_124 : ((13677307/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos995o2c k) + cos995o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_123
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 124 - ((-616669/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_125 : ((133451279/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos995o2c k) + cos995o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_124
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 125 - ((-3320791/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_126 : ((142622673/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos995o2c k) + cos995o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_125
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 126 - ((4586197/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_127 : ((133340571/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos995o2c k) + cos995o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_126
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 127 - ((-4640551/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_128 : ((137498323/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos995o2c k) + cos995o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_127
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 128 - ((129961/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_129 : ((3511587/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos995o2c k) + cos995o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_128
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 129 - ((2966157/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_130 : ((132041027/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos995o2c k) + cos995o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_129
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 130 - ((-8421453/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_131 : ((141988911/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos995o2c k) + cos995o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_130
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 131 - ((2487221/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_132 : ((26924493/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos995o2c k) + cos995o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_131
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 132 - ((-3682723/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_133 : ((17094133/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos995o2c k) + cos995o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_132
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 133 - ((2131599/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_134 : ((140370061/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos995o2c k) + cos995o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_133
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 134 - ((3617997/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_135 : ((132367877/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos995o2c k) + cos995o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_134
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 135 - ((-250037/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_136 : ((28460553/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos995o2c k) + cos995o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_135
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 136 - ((620993/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_137 : ((133052087/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos995o2c k) + cos995o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_136
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 137 - ((-4624839/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_138 : ((69763333/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos995o2c k) + cos995o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_137
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 138 - ((6475579/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_139 : ((137014161/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos995o2c k) + cos995o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_138
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 139 - ((-502301/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_140 : ((135312789/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos995o2c k) + cos995o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_139
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 140 - ((-425093/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_141 : ((35177409/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos995o2c k) + cos995o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_140
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 141 - ((5397847/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_142 : ((5304259/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos995o2c k) + cos995o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_141
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 142 - ((-8102161/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_143 : ((17778167/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos995o2c k) + cos995o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_142
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 143 - ((9619861/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_144 : ((132236179/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos995o2c k) + cos995o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_143
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 144 - ((-9988157/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_145 : ((28325761/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos995o2c k) + cos995o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_144
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 145 - ((4696813/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_146 : ((133534029/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos995o2c k) + cos995o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_145
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 146 - ((-505861/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_147 : ((69944567/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos995o2c k) + cos995o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_146
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 147 - ((1271221/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_148 : ((135471149/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos995o2c k) + cos995o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_147
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 148 - ((-883397/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_149 : ((137933227/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos995o2c k) + cos995o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_148
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 149 - ((1231539/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_150 : ((137305301/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos995o2c k) + cos995o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_149
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 150 - ((-313463/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_151 : ((27258483/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos995o2c k) + cos995o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_150
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 151 - ((-505943/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_152 : ((69351783/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos995o2c k) + cos995o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_151
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 152 - ((2412151/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_153 : ((67569659/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos995o2c k) + cos995o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_152
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 153 - ((-222703/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_154 : ((34902959/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos995o2c k) + cos995o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_153
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 154 - ((2236759/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_155 : ((134449949/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos995o2c k) + cos995o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_154
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 155 - ((-5160887/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_156 : ((28019171/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos995o2c k) + cos995o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_155
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 156 - ((2823453/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_157 : ((67071923/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos995o2c k) + cos995o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_156
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 157 - ((-5951009/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_158 : ((5609227/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos995o2c k) + cos995o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_157
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 158 - ((6087829/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_159 : ((13416381/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos995o2c k) + cos995o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_158
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 159 - ((-1213173/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_160 : ((28009709/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos995o2c k) + cos995o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_159
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 160 - ((1177147/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_161 : ((33626443/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos995o2c k) + cos995o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_160
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 161 - ((-5541773/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_162 : ((139528161/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos995o2c k) + cos995o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_161
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 162 - ((5023389/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_163 : ((33802771/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos995o2c k) + cos995o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_162
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 163 - ((-4316077/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_164 : ((138615483/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos995o2c k) + cos995o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_163
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 164 - ((3405399/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_165 : ((136332751/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos995o2c k) + cos995o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_164
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 165 - ((-570433/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_166 : ((2144951/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos995o2c k) + cos995o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_165
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 166 - ((945113/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_167 : ((137864577/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos995o2c k) + cos995o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_166
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 167 - ((588713/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_168 : ((135580167/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos995o2c k) + cos995o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_167
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 168 - ((-228341/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_169 : ((139651319/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos995o2c k) + cos995o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_168
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 169 - ((509019/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_170 : ((33448023/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos995o2c k) + cos995o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_169
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 170 - ((-5858227/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_171 : ((141301257/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos995o2c k) + cos995o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_170
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 171 - ((1502033/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_172 : ((33108127/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos995o2c k) + cos995o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_171
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 172 - ((-8867749/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_173 : ((142184023/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos995o2c k) + cos995o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_172
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 173 - ((1950503/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_174 : ((132196133/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos995o2c k) + cos995o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_173
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 174 - ((-998689/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_175 : ((141616727/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos995o2c k) + cos995o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_174
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 175 - ((4710797/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_176 : ((66823267/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos995o2c k) + cos995o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_175
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 176 - ((-7969193/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_177 : ((139286353/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos995o2c k) + cos995o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_176
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 177 - ((5640819/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_178 : ((34177323/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos995o2c k) + cos995o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_177
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 178 - ((-2576061/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_179 : ((67885313/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos995o2c k) + cos995o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_178
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 179 - ((-468833/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_180 : ((1753053/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos995o2c k) + cos995o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_179
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 180 - ((2237307/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_181 : ((13273527/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos995o2c k) + cos995o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_180
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 181 - ((-750797/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_182 : ((71111797/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos995o2c k) + cos995o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_181
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 182 - ((2372331/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_183 : ((132267287/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos995o2c k) + cos995o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_182
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 183 - ((-9955307/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_184 : ((28183909/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos995o2c k) + cos995o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_183
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 184 - ((4326629/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_185 : ((27053257/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos995o2c k) + cos995o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_184
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 185 - ((-282613/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_186 : ((136670989/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos995o2c k) + cos995o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_185
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 186 - ((175713/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_187 : ((139938409/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos995o2c k) + cos995o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_186
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 187 - ((163421/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_188 : ((33154381/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos995o2c k) + cos995o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_187
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 188 - ((-1463977/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_189 : ((142312403/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos995o2c k) + cos995o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_188
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 189 - ((9695879/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_190 : ((16583889/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos995o2c k) + cos995o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_189
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 190 - ((-9640291/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_191 : ((139644017/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos995o2c k) + cos995o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_190
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 191 - ((1394781/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_192 : ((2146597/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos995o2c k) + cos995o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_191
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 192 - ((-2260809/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_193 : ((33537259/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos995o2c k) + cos995o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_192
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 193 - ((-808043/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_194 : ((70989533/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos995o2c k) + cos995o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_193
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 194 - ((783103/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_195 : ((26403249/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos995o2c k) + cos995o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_194
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 195 - ((-9961821/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_196 : ((1759319/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos995o2c k) + cos995o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_195
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 196 - ((349211/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_197 : ((27276073/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos995o2c k) + cos995o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_196
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 197 - ((-872831/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_198 : ((26935557/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos995o2c k) + cos995o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_197
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 198 - ((-85079/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_199 : ((70946969/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos995o2c k) + cos995o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_198
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 199 - ((7217153/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_200 : ((131960891/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos995o2c k) + cos995o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_199
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 200 - ((-9932047/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_201 : ((140518329/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos995o2c k) + cos995o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_200
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 201 - ((4279219/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_202 : ((34261457/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos995o2c k) + cos995o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_201
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 202 - ((-3471501/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_203 : ((66900979/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos995o2c k) + cos995o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_202
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 203 - ((-324287/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_204 : ((71179583/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos995o2c k) + cos995o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_203
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 204 - ((66861/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_205 : ((828089/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos995o2c k) + cos995o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_204
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 205 - ((-4931963/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_206 : ((69409913/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos995o2c k) + cos995o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_205
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 206 - ((3163293/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_207 : ((139292827/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos995o2c k) + cos995o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_206
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 207 - ((474001/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_208 : ((66089193/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos995o2c k) + cos995o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_207
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 208 - ((-7113441/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_209 : ((142174529/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos995o2c k) + cos995o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_208
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 209 - ((9997143/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_210 : ((8425557/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos995o2c k) + cos995o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_209
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 210 - ((-7364617/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_211 : ((27060853/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos995o2c k) + cos995o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_210
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 211 - ((496353/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_212 : ((71021991/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos995o2c k) + cos995o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_211
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 212 - ((6740717/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_213 : ((16505961/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos995o2c k) + cos995o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_212
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 213 - ((-4997647/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_214 : ((27830221/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos995o2c k) + cos995o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_213
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 214 - ((7104417/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_215 : ((13947127/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos995o2c k) + cos995o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_214
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 215 - ((64233/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_216 : ((131858567/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos995o2c k) + cos995o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_215
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 216 - ((-7611703/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_217 : ((28352497/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos995o2c k) + cos995o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_216
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 217 - ((4952459/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_218 : ((68146689/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos995o2c k) + cos995o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_217
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 218 - ((-5468107/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_219 : ((834187/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos995o2c k) + cos995o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_218
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 219 - ((-1411229/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_220 : ((71320901/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos995o2c k) + cos995o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_219
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 220 - ((4586441/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_221 : ((13375131/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos995o2c k) + cos995o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_220
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 221 - ((-2222373/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_222 : ((67865887/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos995o2c k) + cos995o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_221
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 222 - ((247683/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_223 : ((142219959/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos995o2c k) + cos995o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_222
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 223 - ((1297837/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_224 : ((66115979/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos995o2c k) + cos995o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_223
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 224 - ((-9987001/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_225 : ((137830027/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos995o2c k) + cos995o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_224
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 225 - ((5599069/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_226 : ((28234911/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos995o2c k) + cos995o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_225
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 226 - ((418191/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_227 : ((16446963/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos995o2c k) + cos995o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_226
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 227 - ((-9597851/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_228 : ((139411547/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos995o2c k) + cos995o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_227
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 228 - ((7836843/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_229 : ((1400477/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos995o2c k) + cos995o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_228
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 229 - ((637153/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_230 : ((6571743/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos995o2c k) + cos995o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_229
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 230 - ((-13456/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_231 : ((140438171/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos995o2c k) + cos995o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_230
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 231 - ((9004311/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_232 : ((69579499/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos995o2c k) + cos995o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_231
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 232 - ((-1278173/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_233 : ((16436421/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos995o2c k) + cos995o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_232
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 233 - ((-766663/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_234 : ((141002103/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos995o2c k) + cos995o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_233
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 234 - ((1902347/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_235 : ((34663399/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos995o2c k) + cos995o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_234
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 235 - ((-2347507/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_236 : ((32883581/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos995o2c k) + cos995o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_235
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 236 - ((-111223/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_237 : ((141198987/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos995o2c k) + cos995o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_236
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 237 - ((9665663/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_238 : ((138582619/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos995o2c k) + cos995o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_237
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 238 - ((-326921/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_239 : ((5258839/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos995o2c k) + cos995o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_238
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 239 - ((-1777661/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_240 : ((35266967/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos995o2c k) + cos995o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_239
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 240 - ((9597893/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_241 : ((138950367/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos995o2c k) + cos995o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_240
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 241 - ((-2116501/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_242 : ((131317169/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos995o2c k) + cos995o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_241
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 242 - ((-3816099/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_243 : ((28114919/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos995o2c k) + cos995o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_242
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 243 - ((4629213/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_244 : ((139726617/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos995o2c k) + cos995o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_243
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 244 - ((-423489/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_245 : ((65596931/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos995o2c k) + cos995o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_244
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 245 - ((-1706351/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_246 : ((34907881/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos995o2c k) + cos995o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_245
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 246 - ((4219331/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_247 : ((140816587/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos995o2c k) + cos995o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_246
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 247 - ((1186063/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_248 : ((1025973/78125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos995o2c k) + cos995o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_247
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 248 - ((-9491043/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_249 : ((138151703/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos995o2c k) + cos995o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_248
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 249 - ((6828159/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_250 : ((142007579/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos995o2c k) + cos995o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_249
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 250 - ((964219/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_251 : ((33002109/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 251, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 251, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 250, cos995o2c k) + cos995o2c 251 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 250) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_250
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 251 - ((-9998143/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_251).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_252 : ((136145071/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 252, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 252, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 251, cos995o2c k) + cos995o2c 252 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 251) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_251
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 252 - ((827527/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_252).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_253 : ((142921653/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 253, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 253, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 252, cos995o2c k) + cos995o2c 253 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 252) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_252
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 253 - ((3388791/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_253).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_254 : ((16692143/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 254, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 254, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 253, cos995o2c k) + cos995o2c 254 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 253) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_253
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 254 - ((-9383509/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_254).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_255 : ((418271/31250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 255, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 255, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 254, cos995o2c k) + cos995o2c 255 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 254) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_254
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 255 - ((19411/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_255).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_256 : ((2234799/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 256, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 256, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 255, cos995o2c k) + cos995o2c 256 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 255) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_255
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 256 - ((1147677/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_256).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_257 : ((17002561/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 257, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 257, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 256, cos995o2c k) + cos995o2c 257 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 256) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_256
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 257 - ((-437853/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_257).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_258 : ((65910119/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 258, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 258, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 257, cos995o2c k) + cos995o2c 258 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 257) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_257
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 258 - ((-16797/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_258).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_259 : ((14178759/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 259, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 259, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 258, cos995o2c k) + cos995o2c 259 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 258) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_258
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 259 - ((311511/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_259).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_260 : ((17393779/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 260, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 260, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 259, cos995o2c k) + cos995o2c 260 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 259) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_259
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 260 - ((-1318179/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_260).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_261 : ((130928741/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 261, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 261, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 260, cos995o2c k) + cos995o2c 261 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 260) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_260
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 261 - ((-8220491/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_261).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_262 : ((13898849/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 262, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 262, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 261, cos995o2c k) + cos995o2c 262 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 261) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_261
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 262 - ((8060749/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_262).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_263 : ((142027379/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 263, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 263, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 262, cos995o2c k) + cos995o2c 263 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 262) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_262
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 263 - ((3039889/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_263).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_264 : ((132026731/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 264, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 264, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 263, cos995o2c k) + cos995o2c 264 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 263) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_263
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 264 - ((-312489/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_264).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_265 : ((33789267/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 265, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 265, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 264, cos995o2c k) + cos995o2c 265 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 264) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_264
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 265 - ((3131337/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_265).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_266 : ((143285963/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 266, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 266, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 265, cos995o2c k) + cos995o2c 266 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 265) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_265
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 266 - ((1625979/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_266).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_267 : ((135344109/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 267, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 267, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 266, cos995o2c k) + cos995o2c 267 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 266) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_266
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 267 - ((-3970427/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_267).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_268 : ((32945069/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 268, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 268, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 267, cos995o2c k) + cos995o2c 268 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 267) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_267
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 268 - ((-3562833/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_268).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_269 : ((28349103/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 269, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 269, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 268, cos995o2c k) + cos995o2c 269 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 268) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_268
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 269 - ((9966239/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_269).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_270 : ((139826153/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 270, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 270, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 269, cos995o2c k) + cos995o2c 270 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 269) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_269
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 270 - ((-959181/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_270).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_271 : ((130871049/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 271, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 271, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 270, cos995o2c k) + cos995o2c 271 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 270) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_270
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 271 - ((-1119263/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_271).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_272 : ((137486719/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 272, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 272, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 271, cos995o2c k) + cos995o2c 272 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 271) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_271
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 272 - ((661667/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_272).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_273 : ((143073213/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 273, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 273, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 272, cos995o2c k) + cos995o2c 273 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 272) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_272
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 273 - ((2793747/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_273).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_274 : ((26732031/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 274, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 274, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 273, cos995o2c k) + cos995o2c 274 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 273) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_273
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 274 - ((-4706029/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_274).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_275 : ((132630299/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 275, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 275, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 274, cos995o2c k) + cos995o2c 275 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 274) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_274
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 275 - ((-128607/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_275).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_276 : ((35635589/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 276, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 276, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 275, cos995o2c k) + cos995o2c 276 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 275) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_275
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 276 - ((9913057/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_276).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_277 : ((69507093/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 277, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 277, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 276, cos995o2c k) + cos995o2c 277 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 276) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_276
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 277 - ((-352717/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_277).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_278 : ((130662109/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 278, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 278, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 277, cos995o2c k) + cos995o2c 278 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 277) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_277
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 278 - ((-8351077/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_278).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_279 : ((68910343/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 279, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 279, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 278, cos995o2c k) + cos995o2c 279 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 278) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_278
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 279 - ((7159577/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_279).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_280 : ((143161951/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 280, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 280, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 279, cos995o2c k) + cos995o2c 280 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 279) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_279
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 280 - ((1068453/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_280).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_281 : ((133804809/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 281, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 281, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 280, cos995o2c k) + cos995o2c 281 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 280) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_280
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 281 - ((-4678071/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_281).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_282 : ((66084201/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 282, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 282, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 281, cos995o2c k) + cos995o2c 282 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 281) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_281
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 282 - ((-1635407/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_282).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_283 : ((142164029/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 283, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 283, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 282, cos995o2c k) + cos995o2c 283 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 282) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_282
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 283 - ((9996627/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_283).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_284 : ((35019459/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 284, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 284, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 283, cos995o2c k) + cos995o2c 284 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 283) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_283
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 284 - ((-2085193/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_284).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_285 : ((26163977/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 285, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 285, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 284, cos995o2c k) + cos995o2c 285 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 284) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_284
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 285 - ((-9256951/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_285).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_286 : ((136128409/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 286, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 286, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 285, cos995o2c k) + cos995o2c 286 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 285) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_285
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 286 - ((1327381/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_286).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_287 : ((71804869/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 287, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 287, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 286, cos995o2c k) + cos995o2c 287 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 286) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_286
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 287 - ((7482329/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_287).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_288 : ((5434781/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 288, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 288, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 287, cos995o2c k) + cos995o2c 288 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 287) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_287
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 288 - ((-7739213/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_288).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_289 : ((32698667/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 289, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 289, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 288, cos995o2c k) + cos995o2c 289 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 288) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_288
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 289 - ((-5073857/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_289).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_290 : ((14006379/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 290, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 290, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 289, cos995o2c k) + cos995o2c 290 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 289) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_289
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 290 - ((4635061/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_290).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_291 : ((142465863/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 291, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 291, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 290, cos995o2c k) + cos995o2c 291 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 290) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_290
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 291 - ((2403073/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_291).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_292 : ((2070653/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 292, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 292, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 291, cos995o2c k) + cos995o2c 292 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 291) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_291
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 292 - ((-9943071/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_292).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_293 : ((66376893/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 293, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 293, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 292, cos995o2c k) + cos995o2c 293 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 292) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_292
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 293 - ((116497/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_293).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_294 : ((142644147/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 294, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 294, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 293, cos995o2c k) + cos995o2c 294 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 293) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_293
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 294 - ((9891361/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_294).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_295 : ((70006951/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 295, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 295, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 294, cos995o2c k) + cos995o2c 295 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 294) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_294
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 295 - ((-525849/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_295).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_296 : ((6536099/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 296, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 296, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 295, cos995o2c k) + cos995o2c 296 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 295) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_295
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 296 - ((-4645461/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_296).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_297 : ((6769581/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 297, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 297, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 296, cos995o2c k) + cos995o2c 297 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 296) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_296
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 297 - ((58383/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_297).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_298 : ((28742873/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 298, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 298, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 297, cos995o2c k) + cos995o2c 298 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 297) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_297
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 298 - ((1664749/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_298).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_299 : ((68699919/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 299, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 299, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 298, cos995o2c k) + cos995o2c 299 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 298) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_298
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 299 - ((-6313527/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_299).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_300 : ((130244857/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 300, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 300, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 299, cos995o2c k) + cos995o2c 300 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 299) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_299
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 300 - ((-7153981/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_300).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_301 : ((34452937/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 301, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 301, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 300, cos995o2c k) + cos995o2c 301 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 300) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_300
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 301 - ((7567891/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_301).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_302 : ((71863599/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 302, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 302, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 301, cos995o2c k) + cos995o2c 302 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 301) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_301
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 302 - ((118329/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_302).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_303 : ((135249711/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 303, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 303, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 302, cos995o2c k) + cos995o2c 303 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 302) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_302
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 303 - ((-8476487/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_303).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_304 : ((130535023/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 304, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 304, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 303, cos995o2c k) + cos995o2c 304 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 303) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_303
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 304 - ((-589211/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_304).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_305 : ((34908157/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 305, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 305, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 304, cos995o2c k) + cos995o2c 305 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 304) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_304
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 305 - ((1819721/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_305).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_306 : ((143248979/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 306, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 306, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 305, cos995o2c k) + cos995o2c 306 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 305) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_305
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 306 - ((3617351/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_306).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_307 : ((33437167/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 307, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 307, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 306, cos995o2c k) + cos995o2c 307 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 306) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_306
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 307 - ((-9499311/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_307).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_308 : ((26214707/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 308, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 308, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 307, cos995o2c k) + cos995o2c 308 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 307) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_307
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 308 - ((-2674133/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_308).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_309 : ((140811797/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 309, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 309, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 308, cos995o2c k) + cos995o2c 309 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 308) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_308
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 309 - ((4869631/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_309).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_310 : ((71360647/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 310, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 310, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 309, cos995o2c k) + cos995o2c 310 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 309) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_309
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 310 - ((1910497/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_310).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_311 : ((66424593/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 311, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 311, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 310, cos995o2c k) + cos995o2c 311 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 310) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_310
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 311 - ((-2467777/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_311).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_312 : ((3287693/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 312, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 312, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 311, cos995o2c k) + cos995o2c 312 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 311) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_311
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 312 - ((-670233/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_312).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_313 : ((141442663/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 313, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 313, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 312, cos995o2c k) + cos995o2c 313 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 312) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_312
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 313 - ((9935943/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_313).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_314 : ((71205661/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 314, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 314, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 313, cos995o2c k) + cos995o2c 314 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 313) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_313
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 314 - ((969659/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_314).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_315 : ((132447291/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 315, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 315, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 314, cos995o2c k) + cos995o2c 315 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 314) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_314
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 315 - ((-9963031/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_315).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_316 : ((65823899/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 316, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 316, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 315, cos995o2c k) + cos995o2c 316 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 315) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_315
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 316 - ((-798493/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_316).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_317 : ((17701963/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 317, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 317, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 316, cos995o2c k) + cos995o2c 317 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 316) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_316
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 317 - ((4984453/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_317).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_318 : ((71220629/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 318, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 318, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 317, cos995o2c k) + cos995o2c 318 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 317) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_317
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 318 - ((413277/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_318).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_319 : ((66241043/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 319, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 319, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 318, cos995o2c k) + cos995o2c 319 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 318) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_318
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 319 - ((-2489543/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_319).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_320 : ((65715431/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 320, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 320, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 319, cos995o2c k) + cos995o2c 320 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 319) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_319
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 320 - ((-65639/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_320).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_321 : ((28270687/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 321, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 321, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 320, cos995o2c k) + cos995o2c 321 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 320) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_320
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 321 - ((9923573/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_321).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_322 : ((142817993/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 322, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 322, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 321, cos995o2c k) + cos995o2c 322 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 321) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_321
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 322 - ((732779/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_322).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_323 : ((26594027/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 323, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 323, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 322, cos995o2c k) + cos995o2c 323 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 322) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_322
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 323 - ((-4923429/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_323).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_324 : ((130902553/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 324, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 324, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 323, cos995o2c k) + cos995o2c 324 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 323) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_323
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 324 - ((-1033291/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_324).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_325 : ((3515021/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 325, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 325, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 324, cos995o2c k) + cos995o2c 325 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 324) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_324
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 325 - ((9699287/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_325).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_326 : ((143442449/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 326, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 326, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 325, cos995o2c k) + cos995o2c 326 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 325) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_325
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 326 - ((2842609/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_326).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_327 : ((16749787/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 327, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 327, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 326, cos995o2c k) + cos995o2c 327 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 326) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_326
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 327 - ((-9443153/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_327).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_328 : ((26044693/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 328, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 328, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 327, cos995o2c k) + cos995o2c 328 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 327) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_327
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 328 - ((-3773831/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_328).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_329 : ((17406971/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 329, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 329, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 328, cos995o2c k) + cos995o2c 329 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 328) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_328
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 329 - ((9033303/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_329).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_330 : ((36021589/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 330, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 330, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 329, cos995o2c k) + cos995o2c 330 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 329) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_329
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 330 - ((1207897/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_330).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_331 : ((135665103/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 331, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 331, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 330, cos995o2c k) + cos995o2c 331 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 330) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_330
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 331 - ((-8420253/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_331).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_332 : ((64846847/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 332, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 332, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 331, cos995o2c k) + cos995o2c 332 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 331) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_331
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 332 - ((-5970409/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_332).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_333 : ((137247739/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 333, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 333, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 332, cos995o2c k) + cos995o2c 333 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 332) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_332
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 333 - ((1511009/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_333).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_334 : ((144374267/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 334, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 334, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 333, cos995o2c k) + cos995o2c 334 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 333) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_333
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 334 - ((890941/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_334).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_335 : ((137977781/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 335, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 335, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 334, cos995o2c k) + cos995o2c 335 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 334) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_334
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 335 - ((-3197743/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_335).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_336 : ((64878621/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 336, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 336, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 335, cos995o2c k) + cos995o2c 336 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 335) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_335
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 336 - ((-8219539/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_336).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_337 : ((134669727/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 337, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 337, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 336, cos995o2c k) + cos995o2c 337 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 336) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_336
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 337 - ((982697/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_337).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_338 : ((143812279/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 338, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 338, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 337, cos995o2c k) + cos995o2c 338 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 337) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_337
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 338 - ((71434/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_338).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_339 : ((70352509/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 339, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 339, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 338, cos995o2c k) + cos995o2c 339 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 338) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_338
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 339 - ((-3106261/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_339).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_340 : ((13092463/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 340, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 340, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 339, cos995o2c k) + cos995o2c 340 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 339) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_339
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 340 - ((-2444847/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_340).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_341 : ((65964481/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 341, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 341, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 340, cos995o2c k) + cos995o2c 341 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 340) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_340
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 341 - ((251333/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_341).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_342 : ((70963541/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 342, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 342, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 341, cos995o2c k) + cos995o2c 342 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 341) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_341
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 342 - ((124989/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_342).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_343 : ((35809347/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 343, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 343, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 342, cos995o2c k) + cos995o2c 343 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 342) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_342
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 343 - ((655653/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_343).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_344 : ((33389299/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 344, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 344, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 343, cos995o2c k) + cos995o2c 344 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 343) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_343
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 344 - ((-1209899/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_344).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_345 : ((32460269/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 345, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 345, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 344, cos995o2c k) + cos995o2c 345 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 344) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_344
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 345 - ((-46439/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_345).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_346 : ((27712019/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 346, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 346, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 345, cos995o2c k) + cos995o2c 346 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 345) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_345
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 346 - ((8720019/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_346).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_347 : ((72291651/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 347, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 347, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 346, cos995o2c k) + cos995o2c 347 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 346) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_346
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 347 - ((6024207/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_347).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_348 : ((34378291/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 348, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 348, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 347, cos995o2c k) + cos995o2c 348 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 347) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_347
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 348 - ((-3534569/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_348).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_349 : ((129502599/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 349, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 349, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 348, cos995o2c k) + cos995o2c 349 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 348) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_348
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 349 - ((-1601913/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_349).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_350 : ((134248007/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 350, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 350, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 349, cos995o2c k) + cos995o2c 350 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 349) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_349
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 350 - ((593301/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_350).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_351 : ((17957989/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 351, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 351, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 350, cos995o2c k) + cos995o2c 351 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 350) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_350
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 351 - ((1883381/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_351).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_352 : ((28359347/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 352, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 352, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 351, cos995o2c k) + cos995o2c 352 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 351) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_351
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 352 - ((-1866177/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_352).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_353 : ((131799733/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 353, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 353, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 352, cos995o2c k) + cos995o2c 353 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 352) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_352
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 353 - ((-4998001/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_353).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_354 : ((65225727/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 354, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 354, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 353, cos995o2c k) + cos995o2c 354 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 353) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_353
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 354 - ((-1347279/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_354).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_355 : ((139996141/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 355, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 355, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 354, cos995o2c k) + cos995o2c 355 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 354) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_354
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 355 - ((9545687/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_355).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_356 : ((144558883/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 356, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 356, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 355, cos995o2c k) + cos995o2c 356 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 355) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_355
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 356 - ((2281871/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_356).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_357 : ((34148089/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 357, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 357, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 356, cos995o2c k) + cos995o2c 357 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 356) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_356
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 357 - ((-7965527/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_357).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_358 : ((64611377/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 358, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 358, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 357, cos995o2c k) + cos995o2c 358 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 357) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_357
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 358 - ((-3684301/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_358).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_359 : ((33631947/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 359, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 359, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 358, cos995o2c k) + cos995o2c 359 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 358) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_358
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 359 - ((2653017/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_359).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_360 : ((143841313/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 360, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 360, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 359, cos995o2c k) + cos995o2c 360 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 359) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_359
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 360 - ((372581/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_360).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_361 : ((142033977/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 361, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 361, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 360, cos995o2c k) + cos995o2c 361 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 360) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_360
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 361 - ((-14112/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_361).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_362 : ((132033813/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 362, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 362, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 361, cos995o2c k) + cos995o2c 362 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 361) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_361
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 362 - ((-2499791/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_362).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_363 : ((4060477/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 363, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 363, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 362, cos995o2c k) + cos995o2c 363 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 362) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_362
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 363 - ((-2097549/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_363).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_364 : ((8693217/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 364, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 364, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 363, cos995o2c k) + cos995o2c 364 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 363) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_363
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 364 - ((1144651/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_364).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_365 : ((28979193/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 365, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 365, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 364, cos995o2c k) + cos995o2c 365 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 364) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_364
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 365 - ((5805493/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_365).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_366 : ((138139123/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 366, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 366, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 365, cos995o2c k) + cos995o2c 366 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 365) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_365
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 366 - ((-3377921/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_366).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_367 : ((129501921/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 367, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 367, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 366, cos995o2c k) + cos995o2c 367 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 366) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_366
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 367 - ((-4318101/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_367).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_368 : ((33141067/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 368, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 368, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 367, cos995o2c k) + cos995o2c 368 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 367) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_367
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 368 - ((3063347/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_368).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_369 : ((71261123/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 369, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 369, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 368, cos995o2c k) + cos995o2c 369 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 368) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_368
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 369 - ((4979489/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_369).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_370 : ((143854789/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 370, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 370, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 369, cos995o2c k) + cos995o2c 370 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 369) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_369
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 370 - ((1333543/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_370).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_371 : ((26900233/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 371, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 371, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 370, cos995o2c k) + cos995o2c 371 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 370) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_370
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 371 - ((-584539/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_371).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_372 : ((2578163/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 372, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 372, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 371, cos995o2c k) + cos995o2c 372 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 371) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_371
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 372 - ((-1118403/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_372).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_373 : ((135666009/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 373, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 373, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 372, cos995o2c k) + cos995o2c 373 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 372) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_372
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 373 - ((6758859/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_373).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_374 : ((72212419/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 374, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 374, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 373, cos995o2c k) + cos995o2c 374 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 373) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_373
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 374 - ((8759829/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_374).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_375 : ((141843327/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 375, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 375, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 374, cos995o2c k) + cos995o2c 375 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 374) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_374
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 375 - ((-2580511/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_375).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_376 : ((131843467/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 376, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 376, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 375, cos995o2c k) + cos995o2c 376 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 375) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_375
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 376 - ((-499943/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_376).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_377 : ((8095031/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 377, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 377, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 376, cos995o2c k) + cos995o2c 377 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 376) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_376
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 377 - ((-2321971/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_377).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_378 : ((138355711/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 378, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 378, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 377, cos995o2c k) + cos995o2c 378 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 377) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_377
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 378 - ((1767243/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_378).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_379 : ((72562089/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 379, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 379, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 378, cos995o2c k) + cos995o2c 379 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 378) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_378
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 379 - ((6769467/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_379).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_380 : ((34937389/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 380, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 380, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 379, cos995o2c k) + cos995o2c 380 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 379) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_379
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 380 - ((-2686811/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_380).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_381 : ((130207057/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 381, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 381, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 380, cos995o2c k) + cos995o2c 381 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 380) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_380
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 381 - ((-9541499/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_381).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_382 : ((130578871/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 382, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 382, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 381, cos995o2c k) + cos995o2c 382 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 381) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_381
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 382 - ((186407/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_382).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_383 : ((140307901/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 383, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 383, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 382, cos995o2c k) + cos995o2c 383 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 382) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_382
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 383 - ((973003/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_383).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_384 : ((18144661/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 384, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 384, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 383, cos995o2c k) + cos995o2c 384 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 383) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_383
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 384 - ((4850387/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_384).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_385 : ((3451761/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 385, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 385, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 384, cos995o2c k) + cos995o2c 385 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 384) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_384
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 385 - ((-885731/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_385).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_386 : ((25865681/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 386, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 386, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 385, cos995o2c k) + cos995o2c 386 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 385) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_385
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 386 - ((-1748207/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_386).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_387 : ((2055387/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 387, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 387, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 386, cos995o2c k) + cos995o2c 387 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 386) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_386
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 387 - ((2217363/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_387).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_388 : ((70761869/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 388, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 388, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 387, cos995o2c k) + cos995o2c 388 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 387) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_387
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 388 - ((997997/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_388).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_389 : ((72492449/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 389, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 389, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 388, cos995o2c k) + cos995o2c 389 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 388) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_388
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 389 - ((43277/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_389).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_390 : ((137005239/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 390, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 390, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 389, cos995o2c k) + cos995o2c 390 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 389) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_389
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 390 - ((-7978659/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_390).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_391 : ((16113253/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 391, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 391, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 390, cos995o2c k) + cos995o2c 391 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 390) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_390
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 391 - ((-1619643/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_391).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_392 : ((132116267/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 392, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 392, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 391, cos995o2c k) + cos995o2c 392 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 391) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_391
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 392 - ((3211243/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_392).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_393 : ((14211247/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 393, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 393, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 392, cos995o2c k) + cos995o2c 393 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 392) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_392
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 393 - ((9997203/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_393).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_394 : ((36225599/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 394, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 394, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 393, cos995o2c k) + cos995o2c 394 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 393) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_393
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 394 - ((1395463/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_394).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_395 : ((8537899/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 395, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 395, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 394, cos995o2c k) + cos995o2c 395 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 394) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_394
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 395 - ((-2073753/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_395).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_396 : ((64369177/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 396, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 396, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 395, cos995o2c k) + cos995o2c 396 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 395) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_395
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 396 - ((-786703/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_396).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_397 : ((3303981/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 397, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 397, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 396, cos995o2c k) + cos995o2c 397 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 396) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_396
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 397 - ((1710943/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_397).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_398 : ((142153723/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 398, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 398, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 397, cos995o2c k) + cos995o2c 398 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 397) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_397
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 398 - ((9995483/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_398).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_399 : ((72517189/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 399, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 399, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 398, cos995o2c k) + cos995o2c 399 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 398) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_398
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 399 - ((576331/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_399).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_400 : ((27376383/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 400, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 400, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 399, cos995o2c k) + cos995o2c 400 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 399) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_399
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 400 - ((-8151463/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_400).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_401 : ((25753547/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 401, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 401, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 400, cos995o2c k) + cos995o2c 401 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 400) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_400
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 401 - ((-405659/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_401).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_402 : ((26330367/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 402, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 402, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 401, cos995o2c k) + cos995o2c 402 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 401) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_401
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 402 - ((28851/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_402).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_403 : ((7082099/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 403, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 403, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 402, cos995o2c k) + cos995o2c 403 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 402) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_402
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 403 - ((1998229/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_403).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_404 : ((145349529/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 404, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 404, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 403, cos995o2c k) + cos995o2c 404 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 403) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_403
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 404 - ((3708549/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_404).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_405 : ((13783579/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 405, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 405, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 404, cos995o2c k) + cos995o2c 405 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 404) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_404
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 405 - ((-7512739/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_405).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_406 : ((129088269/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 406, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 406, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 405, cos995o2c k) + cos995o2c 406 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 405) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_405
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 406 - ((-8746521/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_406).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_407 : ((32667971/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 407, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 407, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 406, cos995o2c k) + cos995o2c 407 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 406) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_406
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 407 - ((316923/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_407).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_408 : ((70244707/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 408, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 408, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 407, cos995o2c k) + cos995o2c 408 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 407) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_407
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 408 - ((981853/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_408).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_409 : ((72830803/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 409, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 409, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 408, cos995o2c k) + cos995o2c 409 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 408) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_408
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 409 - ((646649/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_409).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_410 : ((27888301/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 410, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 410, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 409, cos995o2c k) + cos995o2c 410 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 409) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_409
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 410 - ((-6219101/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_410).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_411 : ((129924343/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 411, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 411, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 410, cos995o2c k) + cos995o2c 411 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 410) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_410
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 411 - ((-4758081/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_411).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_412 : ((129428759/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 412, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 412, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 411, cos995o2c k) + cos995o2c 412 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 411) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_411
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 412 - ((-61823/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_412).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_413 : ((69291001/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 413, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 413, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 412, cos995o2c k) + cos995o2c 413 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 412) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_412
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 413 - ((9154243/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_413).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_414 : ((145627133/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 414, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 414, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 413, cos995o2c k) + cos995o2c 414 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 413) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_413
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 414 - ((7046131/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_414).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_415 : ((141563227/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 415, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 415, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 414, cos995o2c k) + cos995o2c 415 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 414) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_414
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 415 - ((-2031453/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_415).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_416 : ((65786159/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 416, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 416, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 415, cos995o2c k) + cos995o2c 416 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 415) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_415
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 416 - ((-9989909/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_416).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_417 : ((128317919/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 417, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 417, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 416, cos995o2c k) + cos995o2c 417 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 416) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_416
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 417 - ((-3253399/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_417).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_418 : ((33974229/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 418, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 418, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 417, cos995o2c k) + cos995o2c 418 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 417) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_417
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 418 - ((7579997/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_418).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_419 : ((144774067/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 419, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 419, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 418, cos995o2c k) + cos995o2c 419 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 418) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_418
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 419 - ((8878151/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_419).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_420 : ((143840773/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 420, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 420, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 419, cos995o2c k) + cos995o2c 420 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 419) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_419
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 420 - ((-466147/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_420).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_421 : ((33567449/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 421, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 421, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 420, cos995o2c k) + cos995o2c 421 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 420) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_420
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 421 - ((-9569977/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_421).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_422 : ((63971791/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 422, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 422, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 421, cos995o2c k) + cos995o2c 422 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 421) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_421
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 422 - ((-3162607/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_422).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_423 : ((6633623/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 423, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 423, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 422, cos995o2c k) + cos995o2c 423 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 422) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_422
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 423 - ((2364939/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_423).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_424 : ((14262481/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 424, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 424, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 423, cos995o2c k) + cos995o2c 424 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 423) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_423
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 424 - ((199067/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_424).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_425 : ((145600083/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 425, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 425, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 424, cos995o2c k) + cos995o2c 425 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 424) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_424
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 425 - ((2976273/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_425).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_426 : ((27595011/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 426, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 426, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 425, cos995o2c k) + cos995o2c 426 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 425) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_425
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 426 - ((-1906007/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_426).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_427 : ((64512797/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 427, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 427, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 426, cos995o2c k) + cos995o2c 427 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 426) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_426
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 427 - ((-8948461/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_427).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_428 : ((129580467/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 428, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 428, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 427, cos995o2c k) + cos995o2c 428 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 427) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_427
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 428 - ((555873/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_428).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_429 : ((27791801/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 429, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 429, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 428, cos995o2c k) + cos995o2c 429 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 428) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_428
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 429 - ((4689769/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_429).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_430 : ((72947389/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 430, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 430, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 429, cos995o2c k) + cos995o2c 430 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 429) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_429
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 430 - ((6936773/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_430).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_431 : ((71050521/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 431, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 431, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 430, cos995o2c k) + cos995o2c 431 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 430) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_430
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 431 - ((-118523/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_431).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_432 : ((132104197/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 432, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 432, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 431, cos995o2c k) + cos995o2c 432 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 431) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_431
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 432 - ((-1999169/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_432).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_433 : ((63879897/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 433, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 433, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 432, cos995o2c k) + cos995o2c 433 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 432) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_432
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 433 - ((-4343403/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_433).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_434 : ((16773521/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 434, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 434, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 433, cos995o2c k) + cos995o2c 434 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 433) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_433
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 434 - ((3214687/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_434).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_435 : ((71909053/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 435, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 435, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 434, cos995o2c k) + cos995o2c 435 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 434) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_434
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 435 - ((4815469/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_435).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_436 : ((72684947/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 436, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 436, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 435, cos995o2c k) + cos995o2c 436 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 435) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_435
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 436 - ((388197/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_436).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_437 : ((137042741/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 437, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 437, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 436, cos995o2c k) + cos995o2c 437 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 436) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_436
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 437 - ((-8326153/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_437).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_438 : ((128517553/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 438, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 438, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 437, cos995o2c k) + cos995o2c 438 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 437) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_437
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 438 - ((-2131047/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_438).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_439 : ((25930727/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 439, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 439, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 438, cos995o2c k) + cos995o2c 439 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 438) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_438
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 439 - ((568541/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_439).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_440 : ((69564763/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 440, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 440, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 439, cos995o2c k) + cos995o2c 440 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 439) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_439
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 440 - ((9476891/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_440).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_441 : ((146063279/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 441, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 441, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 440, cos995o2c k) + cos995o2c 441 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 440) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_440
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 441 - ((6934753/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_441).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_442 : ((142534521/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 442, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 442, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 441, cos995o2c k) + cos995o2c 442 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 441) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_441
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 442 - ((-1763879/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_442).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_443 : ((33142611/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 443, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 443, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 442, cos995o2c k) + cos995o2c 443 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 442) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_442
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 443 - ((-9963077/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_443).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_444 : ((12747109/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 444, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 444, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 443, cos995o2c k) + cos995o2c 444 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 443) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_443
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 444 - ((-2549177/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_444).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_445 : ((66492841/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 445, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 445, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 444, cos995o2c k) + cos995o2c 445 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 444) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_444
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 445 - ((689449/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_445).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_446 : ((5716003/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 446, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 446, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 445, cos995o2c k) + cos995o2c 446 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 445) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_445
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 446 - ((9915393/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_446).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_447 : ((146105627/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 447, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 447, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 446, cos995o2c k) + cos995o2c 447 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 446) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_446
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 447 - ((400819/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_447).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_448 : ((27806791/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 448, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 448, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 447, cos995o2c k) + cos995o2c 448 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 447) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_447
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 448 - ((-441917/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_448).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_449 : ((129552533/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 449, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 449, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 448, cos995o2c k) + cos995o2c 449 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 448) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_448
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 449 - ((-4740211/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_449).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_450 : ((128153763/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 450, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 450, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 449, cos995o2c k) + cos995o2c 450 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 449) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_449
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 450 - ((-139777/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_450).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_451 : ((68184103/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 451, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 451, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 450, cos995o2c k) + cos995o2c 451 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 450) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_450
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 451 - ((8215443/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_451).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_452 : ((145166033/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 452, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 452, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 451, cos995o2c k) + cos995o2c 452 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 451) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_451
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 452 - ((8798827/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_452).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_453 : ((144926459/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 453, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 453, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 452, cos995o2c k) + cos995o2c 453 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 452) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_452
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 453 - ((-119287/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_453).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_454 : ((135920767/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 454, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 454, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 453, cos995o2c k) + cos995o2c 454 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 453) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_453
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 454 - ((-2251173/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_454).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_455 : ((63963483/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 455, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 455, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 454, cos995o2c k) + cos995o2c 455 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 454) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_454
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 455 - ((-7992801/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_455).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_456 : ((129579489/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 456, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 456, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 455, cos995o2c k) + cos995o2c 456 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 455) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_455
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 456 - ((1653523/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_456).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_457 : ((6954337/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 457, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 457, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 456, cos995o2c k) + cos995o2c 457 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 456) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_456
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 457 - ((9508251/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_457).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_458 : ((18280903/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 458, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 458, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 457, cos995o2c k) + cos995o2c 458 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 457) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_457
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 458 - ((1790371/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_458).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_459 : ((143417101/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 459, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 459, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 458, cos995o2c k) + cos995o2c 459 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 458) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_458
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 459 - ((-2829123/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_459).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_460 : ((66809021/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 460, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 460, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 459, cos995o2c k) + cos995o2c 460 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 459) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_459
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 460 - ((-9798059/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_460).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_461 : ((127238313/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 461, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 461, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 460, cos995o2c k) + cos995o2c 461 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 460) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_460
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 461 - ((-6378729/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_461).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_462 : ((65502243/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 462, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 462, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 461, cos995o2c k) + cos995o2c 462 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 461) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_461
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 462 - ((3767173/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_462).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_463 : ((140944301/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 463, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 463, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 462, cos995o2c k) + cos995o2c 463 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 462) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_462
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 463 - ((1988163/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_463).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_464 : ((18330193/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 464, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 464, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 463, cos995o2c k) + cos995o2c 464 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 463) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_463
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 464 - ((5698243/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_464).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_465 : ((1776979/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 465, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 465, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 464, cos995o2c k) + cos995o2c 465 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 464) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_464
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 465 - ((-280139/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_465).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_466 : ((8260267/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 466, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 466, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 465, cos995o2c k) + cos995o2c 466 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 465) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_465
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 466 - ((-1249131/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_466).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_467 : ((63503899/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 467, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 467, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 466, cos995o2c k) + cos995o2c 467 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 466) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_466
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 467 - ((-2577737/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_467).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_468 : ((32999333/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 468, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 468, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 467, cos995o2c k) + cos995o2c 468 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 467) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_467
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 468 - ((2495267/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_468).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_469 : ((35498851/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 469, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 469, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 468, cos995o2c k) + cos995o2c 469 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 468) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_468
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 469 - ((312471/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_469).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_470 : ((146767123/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 470, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 470, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 469, cos995o2c k) + cos995o2c 470 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 469) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_469
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 470 - ((4772719/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_470).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_471 : ((70727813/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 471, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 471, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 470, cos995o2c k) + cos995o2c 471 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 470) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_470
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 471 - ((-5310497/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_471).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_472 : ((32866097/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 472, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 472, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 471, cos995o2c k) + cos995o2c 472 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 471) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_471
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 472 - ((-4995119/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_472).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_473 : ((25380319/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 473, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 473, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 472, cos995o2c k) + cos995o2c 473 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 472) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_472
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 473 - ((-4561793/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_473).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_474 : ((132355909/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 474, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 474, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 473, cos995o2c k) + cos995o2c 474 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 473) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_473
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 474 - ((2727657/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_474).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_475 : ((35584987/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 475, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 475, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 474, cos995o2c k) + cos995o2c 475 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 474) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_474
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 475 - ((9985039/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_475).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_476 : ((36716609/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 476, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 476, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 475, cos995o2c k) + cos995o2c 476 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 475) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_475
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 476 - ((35371/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_476).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_477 : ((141433739/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 477, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 477, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 476, cos995o2c k) + cos995o2c 477 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 476) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_476
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 477 - ((-5431697/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_477).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_478 : ((131443009/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 478, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 478, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 477, cos995o2c k) + cos995o2c 478 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 477) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_477
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 478 - ((-998973/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_478).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_479 : ((126772891/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 479, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 479, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 478, cos995o2c k) + cos995o2c 479 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 478) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_478
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 479 - ((-2334559/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_479).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_480 : ((132014021/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 480, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 480, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 479, cos995o2c k) + cos995o2c 480 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 479) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_479
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 480 - ((524213/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_480).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_481 : ((71005843/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 481, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 481, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 480, cos995o2c k) + cos995o2c 481 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 480) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_480
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 481 - ((1999733/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_481).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_482 : ((146989871/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 482, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 482, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 481, cos995o2c k) + cos995o2c 482 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 481) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_481
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 482 - ((995837/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_482).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_483 : ((142108217/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 483, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 483, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 482, cos995o2c k) + cos995o2c 483 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 482) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_482
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 483 - ((-2440327/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_483).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_484 : ((132112319/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 484, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 484, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 483, cos995o2c k) + cos995o2c 484 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 483) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_483
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 484 - ((-4997449/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_484).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_485 : ((12666499/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 485, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 485, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 484, cos995o2c k) + cos995o2c 485 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 484) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_484
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 485 - ((-5446329/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_485).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_486 : ((131002829/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 486, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 486, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 485, cos995o2c k) + cos995o2c 486 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 485) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_485
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 486 - ((4338839/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_486).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_487 : ((70476241/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 487, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 487, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 486, cos995o2c k) + cos995o2c 487 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 486) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_486
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 487 - ((9950653/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_487).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_488 : ((147000643/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 488, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 488, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 487, cos995o2c k) + cos995o2c 488 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 487) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_487
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 488 - ((6049161/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_488).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_489 : ((71697703/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 489, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 489, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 488, cos995o2c k) + cos995o2c 489 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 488) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_488
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 489 - ((-3604237/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_489).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_490 : ((16695799/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 490, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 490, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 489, cos995o2c k) + cos995o2c 490 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 489) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_489
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 490 - ((-4914007/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_490).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_491 : ((1268061/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 491, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 491, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 490, cos995o2c k) + cos995o2c 491 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 490) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_490
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 491 - ((-1689823/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_491).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_492 : ((25894461/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 492, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 492, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 491, cos995o2c k) + cos995o2c 492 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 491) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_491
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 492 - ((533441/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_492).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_493 : ((69525893/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 493, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 493, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 492, cos995o2c k) + cos995o2c 493 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 492) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_492
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 493 - ((9580481/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_493).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_494 : ((146585631/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 494, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 494, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 493, cos995o2c k) + cos995o2c 494 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 493) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_493
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 494 - ((1506969/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_494).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_495 : ((145063573/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 495, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 495, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 494, cos995o2c k) + cos995o2c 495 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 494) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_494
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 495 - ((-760529/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_495).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_496 : ((135907557/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 496, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 496, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 495, cos995o2c k) + cos995o2c 496 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 495) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_495
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 496 - ((-1144377/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_496).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_497 : ((127585881/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 497, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 497, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 496, cos995o2c k) + cos995o2c 497 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 496) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_496
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 497 - ((-2080169/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_497).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_498 : ((127756373/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 498, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 498, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 497, cos995o2c k) + cos995o2c 498 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 497) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_497
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 498 - ((42873/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_498).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_499 : ((136250891/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 499, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 499, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 498, cos995o2c k) + cos995o2c 499 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 498) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_498
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 499 - ((4247759/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_499).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_500 : ((72647993/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 500, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 500, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 499, cos995o2c k) + cos995o2c 500 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 499) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_499
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 500 - ((1809219/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_500).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_501 : ((73327419/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 501, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 501, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 500, cos995o2c k) + cos995o2c 501 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 500) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_500
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 501 - ((339963/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_501).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_502 : ((69552073/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 502, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 502, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 501, cos995o2c k) + cos995o2c 502 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 501) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_501
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 502 - ((-1887423/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_502).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_503 : ((8092403/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 503, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 503, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 502, cos995o2c k) + cos995o2c 503 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 502) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_502
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 503 - ((-4812349/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_503).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_504 : ((63223549/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 504, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 504, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 503, cos995o2c k) + cos995o2c 504 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 503) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_503
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 504 - ((-60607/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_504).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_505 : ((132720557/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 505, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 505, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 504, cos995o2c k) + cos995o2c 505 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 504) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_504
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 505 - ((6274459/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_505).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_506 : ((142677609/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 506, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 506, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 505, cos995o2c k) + cos995o2c 506 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 505) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_505
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 506 - ((2489513/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_506).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_507 : ((36860921/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 507, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 507, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 506, cos995o2c k) + cos995o2c 507 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 506) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_506
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 507 - ((190683/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_507).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_508 : ((142795039/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 508, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 508, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 507, cos995o2c k) + cos995o2c 508 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 507) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_507
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 508 - ((-929529/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_508).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_509 : ((132853433/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 509, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 509, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 508, cos995o2c k) + cos995o2c 509 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 508) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_508
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 509 - ((-4970303/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_509).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_510 : ((126384309/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 510, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 510, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 509, cos995o2c k) + cos995o2c 510 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 509) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_509
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 510 - ((-1617031/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_510).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_511 : ((64530639/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 511, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 511, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 510, cos995o2c k) + cos995o2c 511 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 510) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_510
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 511 - ((2677969/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_511).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_512 : ((138530289/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 512, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 512, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 511, cos995o2c k) + cos995o2c 512 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 511) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_511
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 512 - ((9470011/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_512).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_513 : ((73264067/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 513, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 513, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 512, cos995o2c k) + cos995o2c 513 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 512) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_512
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 513 - ((1599769/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_513).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_514 : ((146109967/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 514, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 514, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 513, cos995o2c k) + cos995o2c 514 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 513) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_513
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 514 - ((-417167/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_514).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_515 : ((68823733/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 515, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 515, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 514, cos995o2c k) + cos995o2c 515 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 514) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_514
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 515 - ((-8461501/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_515).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_516 : ((128447477/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 516, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 516, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 515, cos995o2c k) + cos995o2c 516 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 515) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_515
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 516 - ((-9198989/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_516).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_517 : ((31603649/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 517, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 517, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 516, cos995o2c k) + cos995o2c 517 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 516) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_516
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 517 - ((-2031881/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_517).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_518 : ((66639631/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 518, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 518, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 517, cos995o2c k) + cos995o2c 518 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 517) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_517
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 518 - ((3432833/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_518).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_519 : ((143172687/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 519, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 519, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 518, cos995o2c k) + cos995o2c 519 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 518) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_518
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 519 - ((395777/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_519).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_520 : ((18459971/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 520, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 520, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 519, cos995o2c k) + cos995o2c 520 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 519) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_519
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 520 - ((4508081/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_520).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_521 : ((17873631/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 521, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 521, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 520, cos995o2c k) + cos995o2c 521 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 520) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_520
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 521 - ((-117243/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_521).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_522 : ((13307077/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 522, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 522, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 521, cos995o2c k) + cos995o2c 522 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 521) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_521
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 522 - ((-4958639/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_522).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_523 : ((25254567/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 523, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 523, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 522, cos995o2c k) + cos995o2c 523 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 522) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_522
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 523 - ((-1359387/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_523).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_524 : ((32071931/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 524, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 524, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 523, cos995o2c k) + cos995o2c 524 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 523) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_523
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 524 - ((2015889/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_524).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_525 : ((27484107/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 525, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 525, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 524, cos995o2c k) + cos995o2c 525 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 524) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_524
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 525 - ((9133811/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_525).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_526 : ((146060421/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 526, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 526, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 525, cos995o2c k) + cos995o2c 526 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 525) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_525
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 526 - ((4320443/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_526).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_527 : ((147042183/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 527, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 527, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 526, cos995o2c k) + cos995o2c 527 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 526) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_526
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 527 - ((491381/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_527).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_528 : ((1116509/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 528, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 528, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 527, cos995o2c k) + cos995o2c 528 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 527) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_527
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 528 - ((-3738779/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_528).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_529 : ((8112087/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 529, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 529, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 528, cos995o2c k) + cos995o2c 529 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 528) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_528
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 529 - ((-9769233/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_529).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_530 : ((31437907/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 530, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 530, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 529, cos995o2c k) + cos995o2c 530 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 529) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_529
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 530 - ((-1010191/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_530).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_531 : ((130735203/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 531, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 531, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 530, cos995o2c k) + cos995o2c 531 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 530) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_530
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 531 - ((199383/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_531).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_532 : ((140670447/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 532, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 532, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 531, cos995o2c k) + cos995o2c 532 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 531) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_531
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 532 - ((2484061/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_532).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_533 : ((5899279/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 533, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 533, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 532, cos995o2c k) + cos995o2c 533 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 532) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_532
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 533 - ((425783/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_533).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_534 : ((29132153/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 534, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 534, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 533, cos995o2c k) + cos995o2c 534 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 533) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_533
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 534 - ((-182021/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_534).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_535 : ((136685883/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 535, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 535, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 534, cos995o2c k) + cos995o2c 535 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 534) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_534
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 535 - ((-4486941/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_535).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_536 : ((255557/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 536, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 536, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 535, cos995o2c k) + cos995o2c 536 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 535) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_535
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 536 - ((-8906383/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_536).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_537 : ((3151783/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 537, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 537, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 536, cos995o2c k) + cos995o2c 537 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 536) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_536
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 537 - ((-85309/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_537).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_538 : ((26583391/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 538, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 538, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 537, cos995o2c k) + cos995o2c 538 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 537) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_537
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 538 - ((1369327/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_538).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_539 : ((142858547/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 539, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 539, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 538, cos995o2c k) + cos995o2c 539 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 538) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_538
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 539 - ((155353/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_539).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_540 : ((148011143/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 540, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 540, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 539, cos995o2c k) + cos995o2c 540 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 539) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_539
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 540 - ((1288399/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_540).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_541 : ((577241/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 541, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 541, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 540, cos995o2c k) + cos995o2c 541 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 540) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_540
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 541 - ((-3699893/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_541).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_542 : ((134679629/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 542, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 542, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 541, cos995o2c k) + cos995o2c 542 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 541) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_541
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 542 - ((-9629621/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_542).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_543 : ((6334089/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 543, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 543, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 542, cos995o2c k) + cos995o2c 543 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 542) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_542
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 543 - ((-7996849/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_543).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_544 : ((63283291/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 544, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 544, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 543, cos995o2c k) + cos995o2c 544 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 543) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_543
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 544 - ((-57099/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_544).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_545 : ((134412747/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 545, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 545, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 544, cos995o2c k) + cos995o2c 545 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 544) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_544
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 545 - ((1569433/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_545).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_546 : ((72058423/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 546, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 546, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 545, cos995o2c k) + cos995o2c 546 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 545) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_545
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 546 - ((9705099/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_546).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_547 : ((14816569/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 547, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 547, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 546, cos995o2c k) + cos995o2c 547 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 546) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_546
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 547 - ((1012461/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_547).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_548 : ((143443683/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 548, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 548, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 547, cos995o2c k) + cos995o2c 548 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 547) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_547
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 548 - ((-4721007/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_548).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_549 : ((133590379/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 549, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 549, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 548, cos995o2c k) + cos995o2c 549 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 548) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_548
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 549 - ((-615769/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_549).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_550 : ((126159471/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 550, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 550, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 549, cos995o2c k) + cos995o2c 550 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 549) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_549
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 550 - ((-1857477/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_550).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_551 : ((126820293/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 551, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 551, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 550, cos995o2c k) + cos995o2c 551 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 550) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_550
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 551 - ((330911/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_551).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_552 : ((27011703/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 552, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 552, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 551, cos995o2c k) + cos995o2c 552 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 551) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_551
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 552 - ((4119611/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_552).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_553 : ((144616841/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 553, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 553, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 552, cos995o2c k) + cos995o2c 553 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 552) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_552
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 553 - ((4779663/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_553).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_554 : ((148269599/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 554, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 554, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 553, cos995o2c k) + cos995o2c 554 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 553) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_553
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 554 - ((1826879/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_554).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_555 : ((35818003/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 555, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 555, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 554, cos995o2c k) + cos995o2c 555 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 554) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_554
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 555 - ((-4996587/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_555).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_556 : ((133386373/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 556, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 556, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 555, cos995o2c k) + cos995o2c 556 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 555) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_555
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 556 - ((-9884639/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_556).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_557 : ((31503489/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 557, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 557, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 556, cos995o2c k) + cos995o2c 557 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 556) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_556
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 557 - ((-7371417/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_557).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_558 : ((126647879/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 558, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 558, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 557, cos995o2c k) + cos995o2c 558 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 557) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_557
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 558 - ((634923/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_558).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_559 : ((67403011/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 559, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 559, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 558, cos995o2c k) + cos995o2c 559 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 558) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_558
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 559 - ((8159143/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_559).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_560 : ((14443551/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 560, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 560, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 559, cos995o2c k) + cos995o2c 560 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 559) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_559
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 560 - ((1203811/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_560).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_561 : ((74212423/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 561, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 561, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 560, cos995o2c k) + cos995o2c 561 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 560) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_560
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 561 - ((62349/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_561).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_562 : ((143845703/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 562, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 562, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 561, cos995o2c k) + cos995o2c 562 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 561) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_561
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 562 - ((-4578143/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_562).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_563 : ((134066077/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 563, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 563, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 562, cos995o2c k) + cos995o2c 563 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 562) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_562
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 563 - ((-4889313/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_563).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_564 : ((15779957/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 564, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 564, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 563, cos995o2c k) + cos995o2c 564 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 563) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_563
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 564 - ((-7825421/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_564).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_565 : ((31516123/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 565, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 565, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 564, cos995o2c k) + cos995o2c 565 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 564) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_564
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 565 - ((-43541/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_565).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_566 : ((66828491/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 566, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 566, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 565, cos995o2c k) + cos995o2c 566 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 565) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_565
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 566 - ((759349/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_566).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_567 : ((17939031/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 567, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 567, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 566, cos995o2c k) + cos995o2c 567 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 566) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_566
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 567 - ((4928133/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_567).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_568 : ((74259089/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 568, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 568, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 567, cos995o2c k) + cos995o2c 568 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 567) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_567
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 568 - ((500693/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_568).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_569 : ((72540797/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 569, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 569, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 568, cos995o2c k) + cos995o2c 569 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 568) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_568
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 569 - ((-53681/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_569).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_570 : ((67837517/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 570, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 570, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 569, cos995o2c k) + cos995o2c 570 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 569) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_569
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 570 - ((-235139/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_570).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_571 : ((127023477/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 571, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 571, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 570, cos995o2c k) + cos995o2c 571 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 570) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_570
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 571 - ((-8650557/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_571).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_572 : ((125283507/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 572, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 572, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 571, cos995o2c k) + cos995o2c 572 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 571) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_571
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 572 - ((-173897/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_572).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_573 : ((6584029/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 573, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 573, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 572, cos995o2c k) + cos995o2c 573 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 572) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_572
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 573 - ((6398073/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_573).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_574 : ((28335833/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 574, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 574, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 573, cos995o2c k) + cos995o2c 574 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 573) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_573
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 574 - ((1999917/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_574).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_575 : ((74113037/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 575, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 575, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 574, cos995o2c k) + cos995o2c 575 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 574) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_574
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 575 - ((6547909/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_575).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_576 : ((73362627/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 576, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 576, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 575, cos995o2c k) + cos995o2c 576 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 575) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_575
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 576 - ((-74991/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_576).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_577 : ((138237301/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 577, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 577, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 576, cos995o2c k) + cos995o2c 577 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 576) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_576
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 577 - ((-8486953/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_577).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_578 : ((128695397/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 578, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 578, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 577, cos995o2c k) + cos995o2c 578 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 577) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_577
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 578 - ((-1192613/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_578).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_579 : ((124739237/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 579, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 579, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 578, cos995o2c k) + cos995o2c 579 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 578) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_578
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 579 - ((-98879/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_579).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_580 : ((16138131/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 580, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 580, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 579, cos995o2c k) + cos995o2c 580 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 579) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_579
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 580 - ((4366811/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_580).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_581 : ((69381527/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 581, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 581, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 580, cos995o2c k) + cos995o2c 581 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 580) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_580
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 581 - ((4829503/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_581).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_582 : ((36762769/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 582, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 582, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 581, cos995o2c k) + cos995o2c 582 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 581) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_581
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 582 - ((4144511/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_582).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_583 : ((148277811/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 583, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 583, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 582, cos995o2c k) + cos995o2c 583 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 582) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_582
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 583 - ((245547/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_583).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_584 : ((141611607/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 584, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 584, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 583, cos995o2c k) + cos995o2c 584 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 583) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_583
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 584 - ((-1666301/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_584).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_585 : ((65805549/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 585, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 585, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 584, cos995o2c k) + cos995o2c 585 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 584) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_584
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 585 - ((-9999509/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_585).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_586 : ((125082603/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 586, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 586, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 585, cos995o2c k) + cos995o2c 586 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 585) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_585
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 586 - ((-1305499/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_586).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_587 : ((25289621/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 587, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 587, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 586, cos995o2c k) + cos995o2c 587 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 586) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_586
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 587 - ((683251/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_587).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_588 : ((67386797/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 588, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 588, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 587, cos995o2c k) + cos995o2c 588 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 587) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_587
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 588 - ((8326489/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_588).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_589 : ((144440519/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 589, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 589, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 588, cos995o2c k) + cos995o2c 589 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 588) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_588
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 589 - ((386717/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_589).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_590 : ((148954181/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 590, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 590, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 589, cos995o2c k) + cos995o2c 590 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 589) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_589
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 590 - ((2257331/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_590).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_591 : ((145298753/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 591, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 591, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 590, cos995o2c k) + cos995o2c 591 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 590) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_590
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 591 - ((-913607/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_591).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_592 : ((67961713/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 592, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 592, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 591, cos995o2c k) + cos995o2c 592 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 591) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_591
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 592 - ((-9374327/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_592).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_593 : ((25414219/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 593, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 593, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 592, cos995o2c k) + cos995o2c 593 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 592) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_592
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 593 - ((-8851331/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_593).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_594 : ((24922133/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 594, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 594, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 593, cos995o2c k) + cos995o2c 594 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 593) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_593
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 594 - ((-245943/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_594).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_595 : ((16269947/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 595, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 595, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 594, cos995o2c k) + cos995o2c 595 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 594) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_594
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 595 - ((5549911/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_595).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_596 : ((17506333/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 596, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 596, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 595, cos995o2c k) + cos995o2c 596 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 595) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_595
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 596 - ((1236511/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_596).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_597 : ((3694527/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 597, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 597, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 596, cos995o2c k) + cos995o2c 597 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 596) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_596
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 597 - ((966427/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_597).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_598 : ((148291493/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 598, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 598, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 597, cos995o2c k) + cos995o2c 598 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 597) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_597
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 598 - ((511413/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_598).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_599 : ((141257277/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 599, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 599, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 598, cos995o2c k) + cos995o2c 599 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 598) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_598
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 599 - ((-54947/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_599).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_600 : ((131263937/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 600, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 600, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 599, cos995o2c k) + cos995o2c 600 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 599) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_599
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 600 - ((-499617/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_600).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_601 : ((124796571/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 601, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 601, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 600, cos995o2c k) + cos995o2c 601 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 600) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_600
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 601 - ((-3233183/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_601).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_602 : ((126031671/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 602, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 602, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 601, cos995o2c k) + cos995o2c 602 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 601) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_601
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 602 - ((12361/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_602).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_603 : ((6708133/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 603, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 603, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 602, cos995o2c k) + cos995o2c 603 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 602) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_602
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 603 - ((8131989/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_603).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_604 : ((143955941/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 604, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 604, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 603, cos995o2c k) + cos995o2c 604 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 603) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_603
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 604 - ((9794281/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_604).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_605 : ((149135643/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 605, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 605, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 604, cos995o2c k) + cos995o2c 605 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 604) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_604
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 605 - ((2590351/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_605).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_606 : ((146399661/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 606, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 606, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 605, cos995o2c k) + cos995o2c 606 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 605) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_605
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 606 - ((-1367491/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_606).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_607 : ((137498839/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 607, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 607, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 606, cos995o2c k) + cos995o2c 607 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 606) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_606
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 607 - ((-4449911/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_607).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_608 : ((128088589/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 608, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 608, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 607, cos995o2c k) + cos995o2c 608 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 607) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_607
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 608 - ((-37637/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_608).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_609 : ((62061023/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 609, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 609, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 608, cos995o2c k) + cos995o2c 609 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 608) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_608
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 609 - ((-3965543/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_609).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_610 : ((128093267/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 610, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 610, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 609, cos995o2c k) + cos995o2c 610 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 609) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_609
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 610 - ((3972221/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_610).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_611 : ((68747433/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 611, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 611, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 610, cos995o2c k) + cos995o2c 611 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 610) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_610
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 611 - ((9402599/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_611).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_612 : ((146426881/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 612, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 612, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 611, cos995o2c k) + cos995o2c 612 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 611) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_611
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 612 - ((1786603/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_612).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_613 : ((149308103/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 613, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 613, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 612, cos995o2c k) + cos995o2c 613 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 612) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_612
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 613 - ((1441111/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_613).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_614 : ((28870169/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 614, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 614, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 613, cos995o2c k) + cos995o2c 614 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 613) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_613
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 614 - ((-2478129/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_614).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_615 : ((134642821/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 615, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 615, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 614, cos995o2c k) + cos995o2c 615 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 614) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_614
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 615 - ((-606689/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_615).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_616 : ((15774913/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 616, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 616, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 615, cos995o2c k) + cos995o2c 616 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 615) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_615
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 616 - ((-8442517/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_616).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_617 : ((124229523/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 617, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 617, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 616, cos995o2c k) + cos995o2c 617 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 616) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_616
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 617 - ((-1968781/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_617).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_618 : ((25987303/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 618, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 618, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 617, cos995o2c k) + cos995o2c 618 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 617) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_617
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 618 - ((713499/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_618).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_619 : ((873809/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 619, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 619, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 618, cos995o2c k) + cos995o2c 619 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 618) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_618
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 619 - ((394957/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_619).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_620 : ((29560963/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 620, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 620, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 619, cos995o2c k) + cos995o2c 620 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 619) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_619
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 620 - ((63971/80000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_620).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_621 : ((149049771/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 621, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 621, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 620, cos995o2c k) + cos995o2c 621 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 620) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_620
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 621 - ((311489/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_621).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_622 : ((142795449/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 622, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 622, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 621, cos995o2c k) + cos995o2c 622 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 621) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_621
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 622 - ((-3126661/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_622).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_623 : ((132840499/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 623, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 623, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 622, cos995o2c k) + cos995o2c 623 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 622) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_622
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 623 - ((-199079/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_623).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_624 : ((25040647/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 624, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 624, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 623, cos995o2c k) + cos995o2c 624 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 623) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_623
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 624 - ((-954533/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_624).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_625 : ((124480219/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 625, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 625, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 624, cos995o2c k) + cos995o2c 625 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 624) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_624
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 625 - ((-22563/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_625).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_626 : ((2048379/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 626, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 626, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 625, cos995o2c k) + cos995o2c 626 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 625) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_625
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 626 - ((6617037/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_626).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_627 : ((2204389/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 627, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 627, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 626, cos995o2c k) + cos995o2c 627 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 626) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_626
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 627 - ((249641/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_627).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_628 : ((148469853/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 628, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 628, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 627, cos995o2c k) + cos995o2c 628 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 627) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_627
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 628 - ((7389957/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_628).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_629 : ((18608601/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 629, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 629, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 628, cos995o2c k) + cos995o2c 629 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 628) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_628
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 629 - ((79991/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_629).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_630 : ((71024531/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 630, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 630, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 629, cos995o2c k) + cos995o2c 630 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 629) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_629
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 630 - ((-3409373/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_630).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_631 : ((33013251/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 631, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 631, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 630, cos995o2c k) + cos995o2c 631 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 630) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_630
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 631 - ((-4997529/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_631).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_632 : ((62389281/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 632, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 632, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 631, cos995o2c k) + cos995o2c 632 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 631) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_631
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 632 - ((-3636721/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_632).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_633 : ((12449913/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 633, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 633, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 632, cos995o2c k) + cos995o2c 633 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 632) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_632
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 633 - ((-8701/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_633).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_634 : ((131368889/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 634, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 634, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 633, cos995o2c k) + cos995o2c 634 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 633) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_633
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 634 - ((6870759/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_634).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_635 : ((141363603/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 635, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 635, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 634, cos995o2c k) + cos995o2c 635 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 634) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_634
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 635 - ((4997857/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_635).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_636 : ((148654997/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 636, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 636, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 635, cos995o2c k) + cos995o2c 636 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 635) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_635
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 636 - ((3646197/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_636).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_637 : ((37252449/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 637, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 637, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 636, cos995o2c k) + cos995o2c 637 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 636) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_636
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 637 - ((355799/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_637).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_638 : ((71115307/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 638, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 638, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 637, cos995o2c k) + cos995o2c 638 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 637) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_637
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 638 - ((-3389091/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_638).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_639 : ((132240573/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 639, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 639, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 638, cos995o2c k) + cos995o2c 639 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 638) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_638
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 639 - ((-9989041/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_639).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_640 : ((124795303/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 640, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 640, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 639, cos995o2c k) + cos995o2c 640 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 639) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_639
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 640 - ((-744427/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_640).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_641 : ((62082711/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 641, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 641, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 640, cos995o2c k) + cos995o2c 641 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 640) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_640
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 641 - ((-628881/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_641).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_642 : ((13070263/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 642, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 642, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 641, cos995o2c k) + cos995o2c 642 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 641) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_641
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 642 - ((204319/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_642).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_643 : ((28133297/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 643, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 643, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 642, cos995o2c k) + cos995o2c 643 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 642) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_642
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 643 - ((1992971/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_643).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_644 : ((18547839/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 644, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 644, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 643, cos995o2c k) + cos995o2c 644 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 643) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_643
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 644 - ((7717227/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_644).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_645 : ((74737881/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 645, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 645, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 644, cos995o2c k) + cos995o2c 645 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 644) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_644
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 645 - ((21881/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_645).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_646 : ((143334887/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 646, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 646, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 645, cos995o2c k) + cos995o2c 646 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 645) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_645
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 646 - ((-49119/80000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_646).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_647 : ((133432021/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 647, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 647, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 646, cos995o2c k) + cos995o2c 647 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 646) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_646
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 647 - ((-4950933/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_647).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_648 : ((62669867/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 648, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 648, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 647, cos995o2c k) + cos995o2c 648 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 647) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_647
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 648 - ((-8091287/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_648).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_649 : ((61796497/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 649, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 649, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 648, cos995o2c k) + cos995o2c 649 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 648) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_648
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 649 - ((-87287/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_649).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_650 : ((5166383/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 650, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 650, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 649, cos995o2c k) + cos995o2c 650 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 649) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_649
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 650 - ((5567581/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_650).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_651 : ((69463623/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 651, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 651, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 650, cos995o2c k) + cos995o2c 651 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 650) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_650
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 651 - ((9768671/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_651).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_652 : ((147461401/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 652, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 652, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 651, cos995o2c k) + cos995o2c 652 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 651) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_651
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 652 - ((1707031/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_652).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_653 : ((75016699/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 653, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 653, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 652, cos995o2c k) + cos995o2c 653 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 652) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_652
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 653 - ((2572997/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_653).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_654 : ((145228951/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 654, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 654, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 653, cos995o2c k) + cos995o2c 654 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 653) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_653
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 654 - ((-4803447/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_654).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_655 : ((33925863/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 655, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 655, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 654, cos995o2c k) + cos995o2c 655 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 654) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_654
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 655 - ((-9524499/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_655).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_656 : ((15836877/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 656, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 656, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 655, cos995o2c k) + cos995o2c 656 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 655) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_655
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 656 - ((-2251859/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_656).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_657 : ((61568631/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 657, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 657, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 656, cos995o2c k) + cos995o2c 657 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 656) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_656
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 657 - ((-1778377/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_657).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_658 : ((63482989/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 658, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 658, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 657, cos995o2c k) + cos995o2c 658 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 657) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_657
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 658 - ((957429/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_658).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_659 : ((6804327/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 659, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 659, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 658, cos995o2c k) + cos995o2c 659 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 658) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_658
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 659 - ((4560781/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_659).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_660 : ((145539211/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 660, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 660, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 659, cos995o2c k) + cos995o2c 660 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 659) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_659
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 660 - ((9453671/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_660).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_661 : ((150204751/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 661, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 661, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 660, cos995o2c k) + cos995o2c 661 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 660) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_660
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 661 - ((233327/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_661).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_662 : ((147569539/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 662, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 662, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 661, cos995o2c k) + cos995o2c 662 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 661) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_661
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 662 - ((-658553/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_662).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_663 : ((34765151/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 663, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 663, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 662, cos995o2c k) + cos995o2c 663 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 662) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_662
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 663 - ((-1701587/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_663).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_664 : ((64626051/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 664, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 664, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 663, cos995o2c k) + cos995o2c 664 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 663) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_663
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 664 - ((-4903751/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_664).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_665 : ((123395431/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 665, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 665, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 664, cos995o2c k) + cos995o2c 665 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 664) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_664
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 665 - ((-5855671/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_665).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_666 : ((2492221/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 666, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 666, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 665, cos995o2c k) + cos995o2c 666 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 665) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_665
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 666 - ((1216619/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_666).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_667 : ((16530387/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 667, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 667, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 666, cos995o2c k) + cos995o2c 667 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 666) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_666
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 667 - ((3816523/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_667).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_668 : ((71116443/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 668, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 668, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 667, cos995o2c k) + cos995o2c 668 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 667) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_667
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 668 - ((999079/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_668).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_669 : ((29858137/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 669, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 669, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 668, cos995o2c k) + cos995o2c 669 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 668) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_668
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 669 - ((7058799/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_669).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_670 : ((149695063/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 670, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 670, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 669, cos995o2c k) + cos995o2c 670 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 669) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_669
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 670 - ((202689/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_670).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_671 : ((35810253/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 671, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 671, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 670, cos995o2c k) + cos995o2c 671 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 670) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_670
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 671 - ((-6453051/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_671).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_672 : ((16665307/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 672, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 672, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 671, cos995o2c k) + cos995o2c 672 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 671) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_671
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 672 - ((-2479389/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_672).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_673 : ((31283087/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 673, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 673, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 672, cos995o2c k) + cos995o2c 673 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 672) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_672
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 673 - ((-2047277/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_673).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_674 : ((4917641/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 674, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 674, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 673, cos995o2c k) + cos995o2c 674 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 673) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_673
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 674 - ((-2190323/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_674).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_675 : ((63940173/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 675, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 675, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 674, cos995o2c k) + cos995o2c 675 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 674) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_674
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 675 - ((4940321/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_675).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_676 : ((137379297/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 676, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 676, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 675, cos995o2c k) + cos995o2c 676 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 675) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_675
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 676 - ((9499951/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_676).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_677 : ((7325901/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 677, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 677, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 676, cos995o2c k) + cos995o2c 677 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 676) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_676
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 677 - ((9139723/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_677).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_678 : ((150582367/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 678, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 678, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 677, cos995o2c k) + cos995o2c 678 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 677) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_677
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 678 - ((4065347/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_678).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_679 : ((18435867/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 679, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 679, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 678, cos995o2c k) + cos995o2c 679 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 678) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_678
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 679 - ((-3094431/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_679).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_680 : ((138828029/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 680, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 680, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 679, cos995o2c k) + cos995o2c 680 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 679) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_679
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 680 - ((-8657907/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_680).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_681 : ((129040629/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 681, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 681, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 680, cos995o2c k) + cos995o2c 681 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 680) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_680
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 681 - ((-12233/12500 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_681).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_682 : ((123117869/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 682, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 682, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 681, cos995o2c k) + cos995o2c 682 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 681) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_681
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 682 - ((-37011/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_682).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_683 : ((124067237/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 683, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 683, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 682, cos995o2c k) + cos995o2c 683 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 682) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_682
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 683 - ((29699/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_683).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_684 : ((131398623/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 684, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 684, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 683, cos995o2c k) + cos995o2c 684 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 683) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_683
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 684 - ((3666193/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_684).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_685 : ((70697717/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 685, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 685, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 684, cos995o2c k) + cos995o2c 685 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 684) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_684
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 685 - ((9997811/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_685).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_686 : ((14901167/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 686, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 686, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 685, cos995o2c k) + cos995o2c 686 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 685) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_685
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 686 - ((1904309/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_686).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_687 : ((150419079/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 687, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 687, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 686, cos995o2c k) + cos995o2c 687 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 686) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_686
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 687 - ((1408409/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_687).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_688 : ((5796727/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 688, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 688, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 687, cos995o2c k) + cos995o2c 688 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 687) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_687
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 688 - ((-42968/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_688).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_689 : ((2113571/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 689, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 689, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 688, cos995o2c k) + cos995o2c 689 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 688) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_688
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 689 - ((-9648631/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_689).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_690 : ((126287791/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 690, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 690, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 689, cos995o2c k) + cos995o2c 690 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 689) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_689
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 690 - ((-8979753/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_690).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_691 : ((191316/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 691, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 691, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 690, cos995o2c k) + cos995o2c 691 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 690) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_690
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 691 - ((-3844551/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_691).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_692 : ((125632597/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 692, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 692, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 691, cos995o2c k) + cos995o2c 692 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 691) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_691
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 692 - ((3191357/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_692).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_693 : ((134271831/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 693, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 693, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 692, cos995o2c k) + cos995o2c 693 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 692) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_692
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 693 - ((4320117/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_693).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_694 : ((3602281/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 694, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 694, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 693, cos995o2c k) + cos995o2c 694 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 693) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_693
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 694 - ((9820409/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_694).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_695 : ((150257999/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 695, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 695, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 694, cos995o2c k) + cos995o2c 695 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 694) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_694
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 695 - ((6167759/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_695).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_696 : ((149750561/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 696, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 696, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 695, cos995o2c k) + cos995o2c 696 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 695) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_695
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 696 - ((-253219/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_696).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_697 : ((28564873/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 697, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 697, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 696, cos995o2c k) + cos995o2c 697 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 696) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_696
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 697 - ((-1731299/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_697).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_698 : ((66433083/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 698, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 698, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 697, cos995o2c k) + cos995o2c 698 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 697) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_697
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 698 - ((-9957199/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_698).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_699 : ((124724443/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 699, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 699, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 698, cos995o2c k) + cos995o2c 699 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 698) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_698
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 699 - ((-8140723/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_699).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_700 : ((122347349/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 700, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 700, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 699, cos995o2c k) + cos995o2c 700 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 699) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_699
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 700 - ((-1188047/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_700).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_701 : ((31719421/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 701, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 701, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 700, cos995o2c k) + cos995o2c 701 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 700) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_700
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 701 - ((906267/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_701).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_702 : ((136120889/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 702, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 702, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 701, cos995o2c k) + cos995o2c 702 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 701) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_701
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 702 - ((1848841/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_702).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_703 : ((145622079/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 703, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 703, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 702, cos995o2c k) + cos995o2c 703 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 702) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_702
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 703 - ((950219/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_703).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_704 : ((30164029/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 704, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 704, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 703, cos995o2c k) + cos995o2c 704 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 703) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_703
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 704 - ((2599533/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_704).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_705 : ((74615649/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 705, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 705, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 704, cos995o2c k) + cos995o2c 705 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 704) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_704
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 705 - ((-1587847/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_705).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_706 : ((35405459/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 706, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 706, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 705, cos995o2c k) + cos995o2c 706 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 705) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_705
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 706 - ((-3804231/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_706).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_707 : ((16452607/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 707, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 707, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 706, cos995o2c k) + cos995o2c 707 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 706) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_706
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 707 - ((-499999/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_707).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_708 : ((61989417/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 708, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 708, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 707, cos995o2c k) + cos995o2c 708 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 707) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_707
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 708 - ((-3820511/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_708).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_709 : ((30577843/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 709, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 709, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 708, cos995o2c k) + cos995o2c 709 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 708) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_708
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 709 - ((-833231/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_709).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_710 : ((63699009/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 710, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 710, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 709, cos995o2c k) + cos995o2c 710 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 709) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_709
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 710 - ((2543823/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_710).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_711 : ((2138049/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 711, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 711, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 710, cos995o2c k) + cos995o2c 711 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 710) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_710
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 711 - ((4719059/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_711).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_712 : ((2923691/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 712, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 712, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 711, cos995o2c k) + cos995o2c 712 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 711) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_711
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 712 - ((4675207/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_712).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_713 : ((75533249/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 713, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 713, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 712, cos995o2c k) + cos995o2c 713 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 712) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_712
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 713 - ((1220737/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_713).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_714 : ((74602641/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 714, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 714, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 713, cos995o2c k) + cos995o2c 714 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 713) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_713
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 714 - ((-232527/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_714).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_715 : ((28295039/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 715, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 715, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 714, cos995o2c k) + cos995o2c 715 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 714) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_714
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 715 - ((-7729087/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_715).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_716 : ((131474509/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 716, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 716, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 715, cos995o2c k) + cos995o2c 716 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 715) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_715
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 716 - ((-4999843/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_716).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_717 : ((61919907/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 717, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 717, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 716, cos995o2c k) + cos995o2c 717 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 716) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_716
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 717 - ((-1526739/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_717).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_718 : ((122096279/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 718, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 718, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 717, cos995o2c k) + cos995o2c 718 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 717) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_717
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 718 - ((-348507/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_718).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_719 : ((31760099/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 719, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 719, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 718, cos995o2c k) + cos995o2c 719 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 718) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_718
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 719 - ((4945117/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_719).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_720 : ((136391129/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 720, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 720, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 719, cos995o2c k) + cos995o2c 720 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 719) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_719
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 720 - ((9351733/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_720).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_721 : ((72927811/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 721, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 721, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 720, cos995o2c k) + cos995o2c 721 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 720) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_720
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 721 - ((9465493/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_721).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_722 : ((151105593/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 722, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 722, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 721, cos995o2c k) + cos995o2c 722 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 721) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_721
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 722 - ((5250971/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_722).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_723 : ((74875577/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 723, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 723, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 722, cos995o2c k) + cos995o2c 723 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 722) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_722
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 723 - ((-1353439/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_723).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_724 : ((142415847/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 724, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 724, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 723, cos995o2c k) + cos995o2c 724 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 723) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_723
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 724 - ((-7334307/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_724).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_725 : ((132433289/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 725, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 725, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 724, cos995o2c k) + cos995o2c 725 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 724) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_724
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 725 - ((-4990779/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_725).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_726 : ((124322729/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 726, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 726, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 725, cos995o2c k) + cos995o2c 726 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 725) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_725
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 726 - ((-202739/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_726).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_727 : ((60870509/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 727, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 727, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 726, cos995o2c k) + cos995o2c 727 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 726) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_726
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 727 - ((-2580711/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_727).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_728 : ((125843523/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 728, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 728, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 727, cos995o2c k) + cos995o2c 728 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 727) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_727
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 728 - ((820701/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_728).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_729 : ((134780561/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 729, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 729, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 728, cos995o2c k) + cos995o2c 729 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 728) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_728
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 729 - ((4469019/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_729).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_730 : ((72272591/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 730, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 730, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 729, cos995o2c k) + cos995o2c 730 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 729) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_729
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 730 - ((9765621/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_730).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_731 : ((1884703/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 731, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 731, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 730, cos995o2c k) + cos995o2c 731 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 730) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_730
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 731 - ((3116029/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_731).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_732 : ((150702271/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 732, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 732, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 731, cos995o2c k) + cos995o2c 732 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 731) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_731
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 732 - ((-72969/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_732).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_733 : ((9022691/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 733, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 733, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 732, cos995o2c k) + cos995o2c 733 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 732) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_732
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 733 - ((-1267643/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_733).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_734 : ((134573631/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 734, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 734, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 733, cos995o2c k) + cos995o2c 734 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 733) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_733
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 734 - ((-391537/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_734).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_735 : ((125662507/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 735, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 735, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 734, cos995o2c k) + cos995o2c 735 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 734) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_734
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 735 - ((-2227531/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_735).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_736 : ((121555437/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 736, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 736, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 735, cos995o2c k) + cos995o2c 736 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 735) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_735
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 736 - ((-410607/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_736).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_737 : ((3876597/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 737, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 737, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 736, cos995o2c k) + cos995o2c 737 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 736) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_736
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 737 - ((2496667/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_737).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_738 : ((16506001/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 738, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 738, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 737, cos995o2c k) + cos995o2c 738 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 737) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_737
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 738 - ((499869/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_738).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_739 : ((35510641/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 739, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 739, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 738, cos995o2c k) + cos995o2c 739 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 738) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_738
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 739 - ((2498889/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_739).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_740 : ((149673637/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 740, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 740, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 739, cos995o2c k) + cos995o2c 740 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 739) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_739
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 740 - ((7632073/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_740).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_741 : ((151623923/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 741, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 741, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 740, cos995o2c k) + cos995o2c 741 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 740) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_740
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 741 - ((975643/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_741).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_742 : ((147053631/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 742, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 742, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 741, cos995o2c k) + cos995o2c 742 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 741) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_741
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 742 - ((-1142323/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_742).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_743 : ((27589459/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 743, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 743, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 742, cos995o2c k) + cos995o2c 743 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 742) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_742
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 743 - ((-1138167/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_743).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_744 : ((128239883/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 744, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 744, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 743, cos995o2c k) + cos995o2c 744 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 743) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_743
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 744 - ((-2426603/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_744).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_745 : ((122110557/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 745, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 745, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 744, cos995o2c k) + cos995o2c 745 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 744) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_744
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 745 - ((-3064163/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_745).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_746 : ((122186619/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 746, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 746, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 745, cos995o2c k) + cos995o2c 746 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 745) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_745
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 746 - ((38531/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_746).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_747 : ((64213811/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 747, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 747, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 746, cos995o2c k) + cos995o2c 747 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 746) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_746
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 747 - ((6242003/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_747).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_748 : ((17270087/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 748, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 748, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 747, cos995o2c k) + cos995o2c 748 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 747) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_747
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 748 - ((4867037/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_748).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_749 : ((29446919/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 749, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 749, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 748, cos995o2c k) + cos995o2c 749 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 748) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_748
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 749 - ((9074899/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_749).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_750 : ((75896619/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 750, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 750, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 749, cos995o2c k) + cos995o2c 750 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 749) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_749
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 750 - ((4559643/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_750).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_751 : ((4684669/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 751, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 751, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 750, cos995o2c k) + cos995o2c 751 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 750) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_750
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 751 - ((-188283/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_751).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_752 : ((142386129/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 752, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 752, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 751, cos995o2c k) + cos995o2c 752 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 751) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_751
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 752 - ((-7522279/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_752).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_753 : ((132402079/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 753, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 753, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 752, cos995o2c k) + cos995o2c 753 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 752) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_752
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 753 - ((-199661/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_753).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_754 : ((24831807/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 754, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 754, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 753, cos995o2c k) + cos995o2c 754 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 753) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_753
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 754 - ((-2060511/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_754).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_755 : ((60556537/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 755, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 755, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 754, cos995o2c k) + cos995o2c 755 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 754) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_754
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 755 - ((-3044961/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_755).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_756 : ((15566553/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 756, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 756, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 755, cos995o2c k) + cos995o2c 756 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 755) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_755
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 756 - ((68407/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_756).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_757 : ((132982289/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 757, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 757, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 756, cos995o2c k) + cos995o2c 757 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 756) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_756
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 757 - ((1690173/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_757).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_758 : ((142938371/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 758, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 758, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 757, cos995o2c k) + cos995o2c 758 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 757) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_757
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 758 - ((4978541/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_758).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_759 : ((75131951/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 759, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 759, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 758, cos995o2c k) + cos995o2c 759 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 758) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_758
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 759 - ((7326531/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_759).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_760 : ((75963333/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 760, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 760, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 759, cos995o2c k) + cos995o2c 760 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 759) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_759
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 760 - ((415941/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_760).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_761 : ((73622909/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 761, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 761, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 760, cos995o2c k) + cos995o2c 761 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 760) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_760
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 761 - ((-584981/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_761).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_762 : ((69078561/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 762, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 762, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 761, cos995o2c k) + cos995o2c 762 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 761) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_761
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 762 - ((-567981/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_762).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_763 : ((64200767/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 763, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 763, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 762, cos995o2c k) + cos995o2c 763 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 762) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_762
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 763 - ((-2438647/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_763).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_764 : ((121979647/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 764, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 764, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 763, cos995o2c k) + cos995o2c 764 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 763) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_763
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 764 - ((-6420887/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_764).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_765 : ((24302883/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 765, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 765, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 764, cos995o2c k) + cos995o2c 765 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 764) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_764
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 765 - ((-58029/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_765).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_766 : ((63594117/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 766, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 766, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 765, cos995o2c k) + cos995o2c 766 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 765) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_765
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 766 - ((5674819/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_766).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_767 : ((34171259/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 767, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 767, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 766, cos995o2c k) + cos995o2c 767 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 766) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_766
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 767 - ((4748901/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_767).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_768 : ((146144689/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 768, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 768, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 767, cos995o2c k) + cos995o2c 768 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 767) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_767
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 768 - ((9460653/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_768).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_769 : ((37934129/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 769, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 769, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 768, cos995o2c k) + cos995o2c 769 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 768) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_768
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 769 - ((5592827/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_769).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_770 : ((151205457/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 770, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 770, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 769, cos995o2c k) + cos995o2c 770 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 769) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_769
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 770 - ((-530059/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_770).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_771 : ((72386167/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 771, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 771, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 770, cos995o2c k) + cos995o2c 771 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 770) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_770
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 771 - ((-6432123/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_771).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_772 : ((135028439/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 772, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 772, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 771, cos995o2c k) + cos995o2c 772 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 771) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_771
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 772 - ((-1948579/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_772).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_773 : ((125883399/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 773, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 773, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 772, cos995o2c k) + cos995o2c 773 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 772) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_772
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 773 - ((-228601/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_773).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_774 : ((120993077/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 774, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 774, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 773, cos995o2c k) + cos995o2c 774 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 773) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_773
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 774 - ((-2444661/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_774).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_775 : ((61151679/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 775, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 775, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 774, cos995o2c k) + cos995o2c 775 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 774) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_774
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 775 - ((1311281/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_775).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_776 : ((129285453/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 776, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 776, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 775, cos995o2c k) + cos995o2c 776 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 775) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_775
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 776 - ((1396619/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_776).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_777 : ((34790333/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 777, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 777, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 776, cos995o2c k) + cos995o2c 777 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 776) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_776
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 777 - ((9876879/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_777).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_778 : ((37004327/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 778, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 778, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 777, cos995o2c k) + cos995o2c 778 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 777) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_777
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 778 - ((553561/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_778).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_779 : ((152356559/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 779, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 779, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 778, cos995o2c k) + cos995o2c 779 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 778) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_778
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 779 - ((4340251/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_779).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_780 : ((150473973/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 780, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 780, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 779, cos995o2c k) + cos995o2c 780 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 779) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_779
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 780 - ((-940793/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_780).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_781 : ((143116079/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 781, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 781, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 780, cos995o2c k) + cos995o2c 781 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 780) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_780
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 781 - ((-3678447/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_781).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_782 : ((133172817/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 782, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 782, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 781, cos995o2c k) + cos995o2c 782 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 781) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_781
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 782 - ((-4971131/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_782).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_783 : ((62267441/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 783, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 783, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 782, cos995o2c k) + cos995o2c 783 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 782) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_782
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 783 - ((-1727387/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_783).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_784 : ((12057033/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 784, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 784, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 783, cos995o2c k) + cos995o2c 784 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 783) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_783
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 784 - ((-123861/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_784).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_785 : ((6140809/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 785, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 785, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 784, cos995o2c k) + cos995o2c 785 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 784) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_784
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 785 - ((44937/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_785).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_786 : ((32598299/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 786, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 786, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 785, cos995o2c k) + cos995o2c 786 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 785) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_785
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 786 - ((236813/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_786).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_787 : ((140361567/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 787, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 787, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 786, cos995o2c k) + cos995o2c 787 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 786) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_786
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 787 - ((9969371/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_787).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_788 : ((74433897/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 788, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 788, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 787, cos995o2c k) + cos995o2c 788 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 787) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_787
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 788 - ((8507227/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_788).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_789 : ((76317583/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 789, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 789, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 788, cos995o2c k) + cos995o2c 789 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 788) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_788
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 789 - ((942093/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_789).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_790 : ((150220691/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 790, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 790, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 789, cos995o2c k) + cos995o2c 790 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 789) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_789
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 790 - ((-96539/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_790).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_791 : ((142556503/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 791, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 791, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 790, cos995o2c k) + cos995o2c 791 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 790) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_790
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 791 - ((-1915797/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_791).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_792 : ((132579411/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 792, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 792, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 791, cos995o2c k) + cos995o2c 792 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 791) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_791
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 792 - ((-2494023/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_792).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_793 : ((124098601/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 793, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 793, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 792, cos995o2c k) + cos995o2c 793 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 792) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_792
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 793 - ((-847981/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_793).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_794 : ((120340019/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 794, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 794, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 793, cos995o2c k) + cos995o2c 794 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 793) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_793
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 794 - ((-1878791/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_794).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_795 : ((24545129/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 795, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 795, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 794, cos995o2c k) + cos995o2c 795 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 794) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_794
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 795 - ((1193313/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_795).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_796 : ((130344321/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 796, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 796, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 795, cos995o2c k) + cos995o2c 796 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 795) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_795
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 796 - ((1904919/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_796).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_797 : ((140311467/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 797, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 797, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 796, cos995o2c k) + cos995o2c 797 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 796) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_796
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 797 - ((4984073/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_797).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_798 : ((148867043/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 798, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 798, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 797, cos995o2c k) + cos995o2c 798 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 797) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_797
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 798 - ((267393/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_798).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_799 : ((611179/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 799, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 799, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 798, cos995o2c k) + cos995o2c 799 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 798) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_798
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 799 - ((3928707/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_799).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_800 : ((75312941/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 800, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 800, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 799, cos995o2c k) + cos995o2c 800 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 799) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_799
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 800 - ((-541967/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_800).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_801 : ((143178459/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 801, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 801, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 800, cos995o2c k) + cos995o2c 801 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 800) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_800
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 801 - ((-7446423/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_801).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_802 : ((133237971/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 802, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 802, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 801, cos995o2c k) + cos995o2c 802 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 801) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_801
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 802 - ((-310609/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_802).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_803 : ((124508881/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 803, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 803, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 802, cos995o2c k) + cos995o2c 803 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 802) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_802
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 803 - ((-872809/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_803).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_804 : ((60116151/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 804, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 804, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 803, cos995o2c k) + cos995o2c 804 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 803) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_803
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 804 - ((-4275579/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_804).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_805 : ((24397633/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 805, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 805, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 804, cos995o2c k) + cos995o2c 805 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 804) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_804
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 805 - ((1756863/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_805).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_806 : ((129120541/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 806, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 806, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 805, cos995o2c k) + cos995o2c 806 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 805) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_805
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 806 - ((111459/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_806).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_807 : ((17374037/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 807, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 807, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 806, cos995o2c k) + cos995o2c 807 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 806) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_806
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 807 - ((1974551/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_807).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_808 : ((73983857/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 808, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 808, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 807, cos995o2c k) + cos995o2c 808 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 807) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_807
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 808 - ((4488209/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_808).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_809 : ((38188117/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 809, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 809, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 808, cos995o2c k) + cos995o2c 809 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 808) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_808
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 809 - ((2392877/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_809).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_810 : ((75799367/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 810, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 810, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 809, cos995o2c k) + cos995o2c 810 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 809) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_809
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 810 - ((-576367/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_810).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_811 : ((72466957/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 811, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 811, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 810, cos995o2c k) + cos995o2c 811 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 810) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_810
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 811 - ((-333191/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_811).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_812 : ((135192573/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 812, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 812, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 811, cos995o2c k) + cos995o2c 812 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 811) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_811
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 812 - ((-9740341/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_812).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_813 : ((125919619/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 813, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 813, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 812, cos995o2c k) + cos995o2c 813 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 812) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_812
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 813 - ((-4635977/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_813).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_814 : ((60238761/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 814, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 814, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 813, cos995o2c k) + cos995o2c 814 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 813) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_813
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 814 - ((-5441097/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_814).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_815 : ((30207869/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 815, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 815, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 814, cos995o2c k) + cos995o2c 815 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 814) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_814
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 815 - ((177477/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_815).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_816 : ((126846753/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 816, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 816, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 815, cos995o2c k) + cos995o2c 816 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 815) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_815
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 816 - ((6016277/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_816).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_817 : ((27270141/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 817, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 817, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 816, cos995o2c k) + cos995o2c 817 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 816) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_816
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 817 - ((1188119/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_817).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_818 : ((18240577/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 818, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 818, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 817, cos995o2c k) + cos995o2c 818 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 817) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_817
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 818 - ((9574911/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_818).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_819 : ((152136451/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 819, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 819, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 818, cos995o2c k) + cos995o2c 819 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 818) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_818
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 819 - ((1242567/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_819).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_820 : ((19095979/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 820, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 820, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 819, cos995o2c k) + cos995o2c 820 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 819) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_819
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 820 - ((632381/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_820).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_821 : ((73799571/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 821, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 821, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 820, cos995o2c k) + cos995o2c 821 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 820) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_820
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 821 - ((-516769/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_821).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_822 : ((138476109/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 822, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 822, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 821, cos995o2c k) + cos995o2c 822 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 821) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_821
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 822 - ((-9122033/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_822).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_823 : ((128641621/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 823, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 823, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 822, cos995o2c k) + cos995o2c 823 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 822) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_822
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 823 - ((-614593/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_823).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_824 : ((60789941/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 824, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 824, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 823, cos995o2c k) + cos995o2c 824 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 823) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_823
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 824 - ((-7060739/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_824).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_825 : ((59891487/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 825, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 825, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 824, cos995o2c k) + cos995o2c 825 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 824) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_824
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 825 - ((-448977/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_825).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_826 : ((61939377/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 826, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 826, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 825, cos995o2c k) + cos995o2c 826 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 825) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_825
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 826 - ((204839/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_826).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_827 : ((132419837/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 827, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 827, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 826, cos995o2c k) + cos995o2c 827 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 826) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_826
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 827 - ((8542083/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_827).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_828 : ((35601003/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 828, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 828, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 827, cos995o2c k) + cos995o2c 828 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 827) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_827
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 828 - ((399407/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_828).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_829 : ((150333849/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 829, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 829, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 828, cos995o2c k) + cos995o2c 829 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 828) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_828
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 829 - ((7930837/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_829).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_830 : ((153441177/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 830, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 830, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 829, cos995o2c k) + cos995o2c 830 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 829) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_829
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 830 - ((388541/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_830).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_831 : ((150648561/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 831, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 831, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 830, cos995o2c k) + cos995o2c 831 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 830) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_830
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 831 - ((-43619/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_831).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_832 : ((35733031/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 832, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 832, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 831, cos995o2c k) + cos995o2c 832 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 831) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_831
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 832 - ((-7715437/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_832).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_833 : ((26594671/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 833, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 833, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 832, cos995o2c k) + cos995o2c 833 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 832) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_832
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 833 - ((-9957769/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_833).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_834 : ((62110221/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 834, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 834, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 833, cos995o2c k) + cos995o2c 834 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 833) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_833
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 834 - ((-8751913/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_834).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_835 : ((119693461/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 835, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 835, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 834, cos995o2c k) + cos995o2c 835 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 834) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_834
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 835 - ((-4525981/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_835).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_836 : ((120946957/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 836, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 836, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 835, cos995o2c k) + cos995o2c 836 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 835) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_835
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 836 - ((39203/312500 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_836).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_837 : ((25508701/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 837, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 837, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 836, cos995o2c k) + cos995o2c 837 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 836) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_836
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 837 - ((1649387/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_837).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_838 : ((27443201/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 838, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 838, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 837, cos995o2c k) + cos995o2c 838 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 837) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_837
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 838 - ((19347/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_838).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_839 : ((146652251/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 839, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 839, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 838, cos995o2c k) + cos995o2c 839 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 838) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_838
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 839 - ((4718623/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_839).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_840 : ((152632383/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 840, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 840, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 839, cos995o2c k) + cos995o2c 840 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 839) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_839
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 840 - ((1495283/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_840).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_841 : ((9570211/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 841, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 841, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 840, cos995o2c k) + cos995o2c 841 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 840) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_840
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 841 - ((491993/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_841).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_842 : ((36990947/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 842, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 842, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 841, cos995o2c k) + cos995o2c 842 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 841) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_841
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 842 - ((-1289647/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_842).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_843 : ((138908059/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 843, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 843, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 842, cos995o2c k) + cos995o2c 843 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 842) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_842
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 843 - ((-9054729/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_843).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_844 : ((64510787/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 844, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 844, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 843, cos995o2c k) + cos995o2c 844 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 843) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_843
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 844 - ((-1977097/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_844).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_845 : ((30410021/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 845, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 845, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 844, cos995o2c k) + cos995o2c 845 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 844) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_844
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 845 - ((-738049/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_845).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_846 : ((119244761/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 846, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 846, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 845, cos995o2c k) + cos995o2c 846 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 845) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_845
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 846 - ((-2394323/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_846).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_847 : ((15329293/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 847, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 847, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 846, cos995o2c k) + cos995o2c 847 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 846) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_846
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 847 - ((3390583/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_847).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_848 : ((65333619/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 848, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 848, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 847, cos995o2c k) + cos995o2c 848 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 847) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_847
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 848 - ((4016947/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_848).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_849 : ((70326483/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 849, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 849, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 848, cos995o2c k) + cos995o2c 849 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 848) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_848
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 849 - ((1248341/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_849).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_850 : ((37314771/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 850, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 850, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 849, cos995o2c k) + cos995o2c 850 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 849) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_849
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 850 - ((4303559/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_850).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_851 : ((38405773/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 851, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 851, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 850, cos995o2c k) + cos995o2c 851 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 850) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_850
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 851 - ((272813/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_851).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_852 : ((38075097/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 852, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 852, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 851, cos995o2c k) + cos995o2c 852 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 851) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_851
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 852 - ((-165213/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_852).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_853 : ((72867359/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 853, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 853, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 852, cos995o2c k) + cos995o2c 853 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 852) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_852
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 853 - ((-656467/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_853).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_854 : ((5444033/400000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 854, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 854, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 853, cos995o2c k) + cos995o2c 854 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 853) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_853
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 854 - ((-9632893/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_854).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_855 : ((63288893/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 855, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 855, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 854, cos995o2c k) + cos995o2c 855 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 854) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_854
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 855 - ((-9522039/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_855).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_856 : ((2405957/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 856, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 856, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 855, cos995o2c k) + cos995o2c 856 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 855) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_855
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 856 - ((-784867/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_856).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_857 : ((119318787/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 857, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 857, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 856, cos995o2c k) + cos995o2c 857 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 856) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_856
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 857 - ((-978063/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_857).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_858 : ((7747177/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 858, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 858, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 857, cos995o2c k) + cos995o2c 858 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 857) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_857
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 858 - ((927409/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_858).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_859 : ((33171433/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 859, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 859, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 858, cos995o2c k) + cos995o2c 859 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 858) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_858
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 859 - ((87319/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_859).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_860 : ((4458139/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 860, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 860, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 859, cos995o2c k) + cos995o2c 860 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 859) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_859
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 860 - ((2493929/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_860).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_861 : ((75316491/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 861, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 861, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 860, cos995o2c k) + cos995o2c 861 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 860) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_860
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 861 - ((3986767/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_861).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_862 : ((38504543/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 862, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 862, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 861, cos995o2c k) + cos995o2c 862 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 861) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_861
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 862 - ((338619/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_862).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_863 : ((37931057/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 863, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 863, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 862, cos995o2c k) + cos995o2c 863 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 862) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_862
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 863 - ((-143309/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_863).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_864 : ((28899513/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 864, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 864, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 863, cos995o2c k) + cos995o2c 864 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 863) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_863
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 864 - ((-7225663/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_864).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_865 : ((33668089/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 865, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 865, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 864, cos995o2c k) + cos995o2c 865 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 864) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_864
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 865 - ((-9824209/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_865).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_866 : ((125411017/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 866, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 866, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 865, cos995o2c k) + cos995o2c 866 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 865) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_865
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 866 - ((-9260339/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_866).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_867 : ((59842103/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 867, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 867, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 866, cos995o2c k) + cos995o2c 867 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 866) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_866
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 867 - ((-5725811/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_867).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_868 : ((119321957/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 868, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 868, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 867, cos995o2c k) + cos995o2c 868 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 867) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_867
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 868 - ((-361249/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_868).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_869 : ((3888559/312500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 869, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 869, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 868, cos995o2c k) + cos995o2c 869 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 868) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_868
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 869 - ((5112931/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_869).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_870 : ((8336551/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 870, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 870, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 869, cos995o2c k) + cos995o2c 870 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 869) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_869
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 870 - ((1118991/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_870).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_871 : ((1146591/80000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 871, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 871, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 870, cos995o2c k) + cos995o2c 871 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 870) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_870
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 871 - ((9940059/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_871).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_872 : ((75547959/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 872, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 872, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 871, cos995o2c k) + cos995o2c 872 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 871) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_871
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 872 - ((7773043/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_872).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_873 : ((77121169/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 873, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 873, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 872, cos995o2c k) + cos995o2c 873 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 872) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_872
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 873 - ((157371/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_873).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_874 : ((75886783/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 874, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 874, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 873, cos995o2c k) + cos995o2c 874 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 873) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_873
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 874 - ((-616943/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_874).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_875 : ((18059137/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 875, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 875, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 874, cos995o2c k) + cos995o2c 875 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 874) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_874
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 875 - ((-729947/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_875).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_876 : ((67320731/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 876, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 876, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 875, cos995o2c k) + cos995o2c 876 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 875) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_875
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 876 - ((-4915317/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_876).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_877 : ((12536607/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 877, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 877, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 876, cos995o2c k) + cos995o2c 877 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 876) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_876
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 877 - ((-1159299/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_877).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_878 : ((59775101/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 878, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 878, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 877, cos995o2c k) + cos995o2c 878 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 877) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_877
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 878 - ((-1453717/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_878).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_879 : ((119006961/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 879, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 879, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 878, cos995o2c k) + cos995o2c 879 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 878) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_878
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 879 - ((-542241/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_879).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_880 : ((3097511/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 880, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 880, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 879, cos995o2c k) + cos995o2c 880 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 879) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_879
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 880 - ((4894479/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_880).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_881 : ((16587789/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 881, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 881, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 880, cos995o2c k) + cos995o2c 881 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 880) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_880
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 881 - ((1100359/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_881).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_882 : ((71338399/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 882, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 882, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 881, cos995o2c k) + cos995o2c 882 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 881) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_881
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 882 - ((4987743/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_882).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_883 : ((9420851/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 883, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 883, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 882, cos995o2c k) + cos995o2c 883 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 882) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_882
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 883 - ((4028909/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_883).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_884 : ((77192663/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 884, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 884, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 883, cos995o2c k) + cos995o2c 884 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 883) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_883
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 884 - ((365271/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_884).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_885 : ((76254991/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 885, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 885, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 884, cos995o2c k) + cos995o2c 885 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 884) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_884
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 885 - ((-234293/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_885).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_886 : ((145689841/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 886, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 886, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 885, cos995o2c k) + cos995o2c 886 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 885) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_885
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 886 - ((-6819141/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_886).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_887 : ((13602299/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 887, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 887, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 886, cos995o2c k) + cos995o2c 887 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 886) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_886
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 887 - ((-9665851/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_887).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_888 : ((126472603/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 888, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 888, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 887, cos995o2c k) + cos995o2c 888 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 887) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_887
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 888 - ((-9549387/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_888).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_889 : ((1874327/156250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 889, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 889, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 888, cos995o2c k) + cos995o2c 889 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 888) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_888
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 889 - ((-260587/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_889).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_890 : ((118459297/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 890, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 890, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 889, cos995o2c k) + cos995o2c 890 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 889) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_889
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 890 - ((-1496631/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_890).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_891 : ((122430307/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 891, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 891, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 890, cos995o2c k) + cos995o2c 891 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 890) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_890
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 891 - ((397201/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_891).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_892 : ((130658389/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 892, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 892, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 891, cos995o2c k) + cos995o2c 892 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 891) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_891
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 892 - ((4114541/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_892).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_893 : ((140646399/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 893, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 893, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 892, cos995o2c k) + cos995o2c 893 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 892) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_892
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 893 - ((998901/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_893).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_894 : ((149373257/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 894, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 894, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 893, cos995o2c k) + cos995o2c 894 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 893) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_893
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 894 - ((4363929/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_894).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_895 : ((30841499/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 895, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 895, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 894, cos995o2c k) + cos995o2c 895 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 894) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_894
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 895 - ((2417619/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_895).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_896 : ((38424473/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 896, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 896, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 895, cos995o2c k) + cos995o2c 896 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 895) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_895
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 896 - ((-508603/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_896).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_897 : ((18500343/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 897, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 897, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 896, cos995o2c k) + cos995o2c 897 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 896) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_896
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 897 - ((-1423537/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_897).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_898 : ((138833281/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 898, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 898, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 897, cos995o2c k) + cos995o2c 898 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 897) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_897
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 898 - ((-9168463/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_898).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_899 : ((64467197/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 899, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 899, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 898, cos995o2c k) + cos995o2c 899 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 898) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_898
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 899 - ((-9897887/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_899).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_900 : ((121259907/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 900, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 900, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 899, cos995o2c k) + cos995o2c 900 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 899) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_899
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 900 - ((-7673487/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_900).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_901 : ((59046077/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 901, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 901, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 900, cos995o2c k) + cos995o2c 901 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 900) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_900
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 901 - ((-3166753/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_901).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_902 : ((30091891/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 902, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 902, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 901, cos995o2c k) + cos995o2c 902 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 901) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_901
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 902 - ((227641/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_902).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_903 : ((127405643/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 903, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 903, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 902, cos995o2c k) + cos995o2c 903 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 902) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_902
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 903 - ((7039079/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_903).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_904 : ((68559867/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 904, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 904, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 903, cos995o2c k) + cos995o2c 904 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 903) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_903
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 904 - ((9715091/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_904).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_905 : ((73319879/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 905, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 905, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 904, cos995o2c k) + cos995o2c 905 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 904) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_904
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 905 - ((74383/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_905).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_906 : ((153161647/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 906, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 906, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 905, cos995o2c k) + cos995o2c 906 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 905) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_905
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 906 - ((6522889/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_906).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_907 : ((38692919/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 907, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 907, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 906, cos995o2c k) + cos995o2c 907 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 906) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_906
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 907 - ((1611029/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_907).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_908 : ((151002231/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 908, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 908, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 907, cos995o2c k) + cos995o2c 908 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 907) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_907
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 908 - ((-753689/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_908).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_909 : ((142961269/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 909, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 909, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 908, cos995o2c k) + cos995o2c 909 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 908) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_908
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 909 - ((-4019981/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_909).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_910 : ((133000571/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 910, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 910, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 909, cos995o2c k) + cos995o2c 910 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 909) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_909
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 910 - ((-4979849/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_910).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_911 : ((6201199/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 911, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 911, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 910, cos995o2c k) + cos995o2c 911 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 910) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_910
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 911 - ((-8975591/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_911).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_912 : ((14830023/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 912, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 912, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 911, cos995o2c k) + cos995o2c 912 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 911) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_911
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 912 - ((-1345699/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_912).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_913 : ((118407363/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 913, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 913, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 912, cos995o2c k) + cos995o2c 913 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 912) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_912
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 913 - ((-231821/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_913).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_914 : ((123387561/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 914, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 914, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 913, cos995o2c k) + cos995o2c 914 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 913) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_913
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 914 - ((2490599/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_914).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_915 : ((132136607/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 915, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 915, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 914, cos995o2c k) + cos995o2c 915 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 914) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_914
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 915 - ((4375023/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_915).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_916 : ((71064181/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 916, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 916, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 915, cos995o2c k) + cos995o2c 916 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 915) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_915
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 916 - ((1998551/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_916).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_917 : ((30097421/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 917, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 917, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 916, cos995o2c k) + cos995o2c 917 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 916) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_916
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 917 - ((8359743/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_917).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_918 : ((154814863/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 918, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 918, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 917, cos995o2c k) + cos995o2c 918 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 917) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_917
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 918 - ((2164379/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_918).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_919 : ((19234409/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 919, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 919, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 918, cos995o2c k) + cos995o2c 919 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 918) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_918
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 919 - ((-938591/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_919).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_920 : ((73971133/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 920, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 920, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 919, cos995o2c k) + cos995o2c 920 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 919) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_919
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 920 - ((-2966003/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_920).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_921 : ((17339049/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 921, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 921, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 920, cos995o2c k) + cos995o2c 921 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 920) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_920
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 921 - ((-4614437/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_921).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_922 : ((128815761/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 922, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 922, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 921, cos995o2c k) + cos995o2c 922 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 921) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_921
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 922 - ((-9895631/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_922).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_923 : ((60531787/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 923, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 923, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 922, cos995o2c k) + cos995o2c 923 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 922) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_922
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 923 - ((-7751187/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_923).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_924 : ((7353151/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 924, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 924, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 923, cos995o2c k) + cos995o2c 924 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 923) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_923
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 924 - ((-1706079/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_924).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_925 : ((59768687/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 925, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 925, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 924, cos995o2c k) + cos995o2c 925 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 924) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_924
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 925 - ((943979/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_925).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_926 : ((25237261/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 926, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 926, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 925, cos995o2c k) + cos995o2c 926 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 925) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_925
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 926 - ((6649931/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_926).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_927 : ((67859841/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 927, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 927, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 926, cos995o2c k) + cos995o2c 927 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 926) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_926
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 927 - ((9534377/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_927).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_928 : ((29091049/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 928, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 928, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 927, cos995o2c k) + cos995o2c 928 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 927) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_927
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 928 - ((9736563/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_928).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_929 : ((76331083/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 929, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 929, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 928, cos995o2c k) + cos995o2c 929 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 928) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_928
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 929 - ((7207921/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_929).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_930 : ((38831479/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 930, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 930, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 929, cos995o2c k) + cos995o2c 930 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 929) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_929
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 930 - ((10659/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_930).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_931 : ((30541301/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 931, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 931, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 930, cos995o2c k) + cos995o2c 931 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 930) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_930
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 931 - ((-2618411/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_931).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_932 : ((72769299/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 932, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 932, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 931, cos995o2c k) + cos995o2c 932 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 931) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_931
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 932 - ((-7166907/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_932).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_933 : ((135820031/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 933, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 933, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 932, cos995o2c k) + cos995o2c 933 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 932) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_932
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 933 - ((-9717567/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_933).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_934 : ((126250109/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 934, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 934, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 933, cos995o2c k) + cos995o2c 934 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 933) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_933
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 934 - ((-4784461/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_934).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_935 : ((119478721/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 935, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 935, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 934, cos995o2c k) + cos995o2c 935 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 934) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_934
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 935 - ((-1692597/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_935).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_936 : ((117374017/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 936, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 936, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 935, cos995o2c k) + cos995o2c 936 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 935) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_935
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 936 - ((-262963/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_936).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_937 : ((15063977/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 937, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 937, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 936, cos995o2c k) + cos995o2c 937 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 936) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_936
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 937 - ((3138799/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_937).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_938 : ((32005839/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 938, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 938, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 937, cos995o2c k) + cos995o2c 938 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 937) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_937
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 938 - ((375627/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_938).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_939 : ((137840979/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 939, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 939, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 938, cos995o2c k) + cos995o2c 939 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 938) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_938
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 939 - ((9818623/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_939).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_940 : ((73635779/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 940, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 940, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 939, cos995o2c k) + cos995o2c 940 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 939) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_939
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 940 - ((9431579/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_940).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_941 : ((153735771/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 941, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 941, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 940, cos995o2c k) + cos995o2c 941 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 940) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_940
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 941 - ((6465213/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_941).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_942 : ((155472119/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 942, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 942, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 941, cos995o2c k) + cos995o2c 942 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 941) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_941
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 942 - ((434337/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_942).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_943 : ((152011849/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 943, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 943, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 942, cos995o2c k) + cos995o2c 943 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 942) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_942
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 943 - ((-345927/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_943).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_944 : ((28860021/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 944, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 944, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 943, cos995o2c k) + cos995o2c 944 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 943) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_943
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 944 - ((-963843/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_944).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_945 : ((8402031/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 945, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 945, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 944, cos995o2c k) + cos995o2c 945 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 944) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_944
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 945 - ((-9866609/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_945).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_946 : ((125081859/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 946, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 946, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 945, cos995o2c k) + cos995o2c 946 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 945) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_945
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 946 - ((-9349637/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_946).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_947 : ((7423321/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 947, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 947, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 946, cos995o2c k) + cos995o2c 947 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 946) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_946
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 947 - ((-6307723/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_947).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_948 : ((117204263/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 948, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 948, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 947, cos995o2c k) + cos995o2c 948 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 947) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_947
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 948 - ((-1567873/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_948).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_949 : ((120791689/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 949, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 949, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 948, cos995o2c k) + cos995o2c 949 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 948) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_948
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 949 - ((1794213/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_949).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_950 : ((128567663/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 950, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 950, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 949, cos995o2c k) + cos995o2c 950 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 949) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_949
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 950 - ((3888487/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_950).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_951 : ((27688927/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 951, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 951, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 950, cos995o2c k) + cos995o2c 951 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 950) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_950
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 951 - ((2469493/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_951).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_952 : ((73889771/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 952, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 952, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 951, cos995o2c k) + cos995o2c 952 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 951) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_951
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 952 - ((9335907/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_952).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_953 : ((7704093/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 953, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 953, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 952, cos995o2c k) + cos995o2c 953 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 952) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_952
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 953 - ((3151659/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_953).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_954 : ((38919133/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 954, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 954, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 953, cos995o2c k) + cos995o2c 954 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 953) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_953
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 954 - ((199459/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_954).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_955 : ((152143633/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 955, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 955, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 954, cos995o2c k) + cos995o2c 955 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 954) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_954
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 955 - ((-3531899/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_955).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_956 : ((28884933/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 956, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 956, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 955, cos995o2c k) + cos995o2c 956 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 955) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_955
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 956 - ((-482373/625000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_956).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_957 : ((134566211/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 957, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 957, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 956, cos995o2c k) + cos995o2c 957 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 956) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_956
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 957 - ((-4928727/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_957).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_958 : ((125173341/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 958, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 958, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 957, cos995o2c k) + cos995o2c 958 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 957) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_957
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 958 - ((-939187/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_958).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_959 : ((14840111/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 959, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 959, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 958, cos995o2c k) + cos995o2c 959 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 958) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_958
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 959 - ((-6451453/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_959).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_960 : ((116902849/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 960, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 960, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 959, cos995o2c k) + cos995o2c 960 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 959) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_959
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 960 - ((-1817039/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_960).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_961 : ((120192167/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 961, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 961, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 960, cos995o2c k) + cos995o2c 961 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 960) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_960
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 961 - ((1645159/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_961).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_962 : ((127721619/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 962, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 962, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 961, cos995o2c k) + cos995o2c 962 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 961) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_961
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 962 - ((1882613/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_962).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_963 : ((68759431/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 963, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 963, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 962, cos995o2c k) + cos995o2c 963 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 962) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_962
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 963 - ((9798243/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_963).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_964 : ((36756387/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 964, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 964, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 963, cos995o2c k) + cos995o2c 964 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 963) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_963
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 964 - ((4753843/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_964).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_965 : ((153766311/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 965, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 965, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 964, cos995o2c k) + cos995o2c 965 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 964) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_964
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 965 - ((6741763/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_965).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_966 : ((155992359/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 966, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 966, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 965, cos995o2c k) + cos995o2c 966 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 965) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_965
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 966 - ((278381/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_966).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_967 : ((30626127/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 967, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 967, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 966, cos995o2c k) + cos995o2c 967 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 966) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_966
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 967 - ((-715181/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_967).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_968 : ((29185179/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 968, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 968, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 967, cos995o2c k) + cos995o2c 968 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 967) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_967
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 968 - ((-360187/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_968).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_969 : ((136242577/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 969, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 969, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 968, cos995o2c k) + cos995o2c 969 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 968) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_968
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 969 - ((-4841159/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_969).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_970 : ((31644667/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 970, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 970, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 969, cos995o2c k) + cos995o2c 970 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 969) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_969
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 970 - ((-9662909/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_970).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_971 : ((119419541/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 971, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 971, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 970, cos995o2c k) + cos995o2c 971 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 970) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_970
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 971 - ((-7158127/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_971).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_972 : ((58300313/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 972, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 972, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 971, cos995o2c k) + cos995o2c 972 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 971) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_971
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 972 - ((-563583/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_972).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_973 : ((59419579/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 973, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 973, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 972, cos995o2c k) + cos995o2c 973 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 972) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_972
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 973 - ((559883/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_973).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_974 : ((62779243/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 974, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 974, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 973, cos995o2c k) + cos995o2c 974 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 973) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_973
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 974 - ((840041/1250000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_974).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_975 : ((67519607/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 975, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 975, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 974, cos995o2c k) + cos995o2c 975 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 974) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_974
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 975 - ((74076/78125 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_975).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_976 : ((36216143/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 976, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 976, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 975, cos995o2c k) + cos995o2c 976 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 975) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_975
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 976 - ((4913179/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_976).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_977 : ((76268479/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 977, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 977, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 976, cos995o2c k) + cos995o2c 977 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 976) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_976
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 977 - ((3836693/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_977).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_978 : ((78056171/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 978, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 978, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 977, cos995o2c k) + cos995o2c 978 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 977) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_977
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 978 - ((55881/156250 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_978).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_979 : ((154689109/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 979, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 979, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 978, cos995o2c k) + cos995o2c 979 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 978) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_978
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 979 - ((-1422233/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_979).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_980 : ((148631431/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 980, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 980, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 979, cos995o2c k) + cos995o2c 980 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 979) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_979
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 980 - ((-3028339/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_980).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_981 : ((8716899/625000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 981, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 981, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 980, cos995o2c k) + cos995o2c 981 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 980) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_980
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 981 - ((-9160047/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_981).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_982 : ((32378409/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 982, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 982, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 981, cos995o2c k) + cos995o2c 982 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 981) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_981
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 982 - ((-2488937/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_982).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_983 : ((60630959/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 983, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 983, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 982, cos995o2c k) + cos995o2c 983 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 982) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_982
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 983 - ((-4125359/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_983).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_984 : ((29195243/2500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 984, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 984, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 983, cos995o2c k) + cos995o2c 984 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 983) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_983
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 984 - ((-2239973/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_984).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_985 : ((117188253/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 985, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 985, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 984, cos995o2c k) + cos995o2c 985 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 984) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_984
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 985 - ((408281/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_985).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_986 : ((61188507/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 986, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 986, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 985, cos995o2c k) + cos995o2c 986 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 985) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_985
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 986 - ((5189761/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_986).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_987 : ((131050089/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 987, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 987, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 986, cos995o2c k) + cos995o2c 987 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 986) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_986
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 987 - ((346963/400000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_987).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_988 : ((70523817/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 988, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 988, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 987, cos995o2c k) + cos995o2c 988 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 987) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_987
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 988 - ((1999709/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_988).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_989 : ((18735937/1250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 989, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 989, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 988, cos995o2c k) + cos995o2c 989 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 988) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_988
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 989 - ((4420431/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_989).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_990 : ((7769073/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 990, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 990, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 989, cos995o2c k) + cos995o2c 990 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 989) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_989
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 990 - ((1373741/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_990).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_991 : ((156174477/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 991, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 991, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 990, cos995o2c k) + cos995o2c 991 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 990) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_990
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 991 - ((794017/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_991).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_992 : ((30414989/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 992, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 992, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 991, cos995o2c k) + cos995o2c 992 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 991) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_991
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 992 - ((-1024633/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_992).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_993 : ((144096627/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 993, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 993, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 992, cos995o2c k) + cos995o2c 993 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 992) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_992
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 993 - ((-3988659/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_993).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_994 : ((13420273/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 994, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 994, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 993, cos995o2c k) + cos995o2c 994 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 993) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_993
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 994 - ((-9892897/10000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_994).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_995 : ((3120523/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 995, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 995, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 994, cos995o2c k) + cos995o2c 995 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 994) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_994
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 995 - ((-938081/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_995).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_996 : ((59123161/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 996, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 996, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 995, cos995o2c k) + cos995o2c 996 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 995) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_995
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 996 - ((-3286799/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_996).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_997 : ((58040939/5000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 997, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 997, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 996, cos995o2c k) + cos995o2c 997 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 996) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_996
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 997 - ((-540861/2500000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_997).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_998 : ((118850923/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 998, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 998, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 997, cos995o2c k) + cos995o2c 998 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 997) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_997
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 998 - ((554009/2000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_998).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_999 : ((25175009/2000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 999, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 999, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 998, cos995o2c k) + cos995o2c 999 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 998) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_998
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 999 - ((3512561/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_999).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum995o2_1000 : ((135444603/10000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 1000, cos995o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 1000, cos995o2c k)
      = (∑ k ∈ Finset.Icc 11 999, cos995o2c k) + cos995o2c 1000 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 999) (by norm_num) cos995o2c
    simpa using h
  have hprev := psum995o2_999
  have hstep : -((1/10000 : ℚ) : ℝ) ≤ cos995o2c 1000 - ((4785279/5000000 : ℚ) : ℝ) :=
    (abs_le.mp cos995o2_br_1000).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 32768 in
theorem psum995o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 1000 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos995o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum995o2_11
  · exact le_trans (by norm_num) psum995o2_12
  · exact le_trans (by norm_num) psum995o2_13
  · exact le_trans (by norm_num) psum995o2_14
  · exact le_trans (by norm_num) psum995o2_15
  · exact le_trans (by norm_num) psum995o2_16
  · exact le_trans (by norm_num) psum995o2_17
  · exact le_trans (by norm_num) psum995o2_18
  · exact le_trans (by norm_num) psum995o2_19
  · exact le_trans (by norm_num) psum995o2_20
  · exact le_trans (by norm_num) psum995o2_21
  · exact le_trans (by norm_num) psum995o2_22
  · exact le_trans (by norm_num) psum995o2_23
  · exact le_trans (by norm_num) psum995o2_24
  · exact le_trans (by norm_num) psum995o2_25
  · exact le_trans (by norm_num) psum995o2_26
  · exact le_trans (by norm_num) psum995o2_27
  · exact le_trans (by norm_num) psum995o2_28
  · exact le_trans (by norm_num) psum995o2_29
  · exact le_trans (by norm_num) psum995o2_30
  · exact le_trans (by norm_num) psum995o2_31
  · exact le_trans (by norm_num) psum995o2_32
  · exact le_trans (by norm_num) psum995o2_33
  · exact le_trans (by norm_num) psum995o2_34
  · exact le_trans (by norm_num) psum995o2_35
  · exact le_trans (by norm_num) psum995o2_36
  · exact le_trans (by norm_num) psum995o2_37
  · exact le_trans (by norm_num) psum995o2_38
  · exact le_trans (by norm_num) psum995o2_39
  · exact le_trans (by norm_num) psum995o2_40
  · exact le_trans (by norm_num) psum995o2_41
  · exact le_trans (by norm_num) psum995o2_42
  · exact le_trans (by norm_num) psum995o2_43
  · exact le_trans (by norm_num) psum995o2_44
  · exact le_trans (by norm_num) psum995o2_45
  · exact le_trans (by norm_num) psum995o2_46
  · exact le_trans (by norm_num) psum995o2_47
  · exact le_trans (by norm_num) psum995o2_48
  · exact le_trans (by norm_num) psum995o2_49
  · exact le_trans (by norm_num) psum995o2_50
  · exact le_trans (by norm_num) psum995o2_51
  · exact le_trans (by norm_num) psum995o2_52
  · exact le_trans (by norm_num) psum995o2_53
  · exact le_trans (by norm_num) psum995o2_54
  · exact le_trans (by norm_num) psum995o2_55
  · exact le_trans (by norm_num) psum995o2_56
  · exact le_trans (by norm_num) psum995o2_57
  · exact le_trans (by norm_num) psum995o2_58
  · exact le_trans (by norm_num) psum995o2_59
  · exact le_trans (by norm_num) psum995o2_60
  · exact le_trans (by norm_num) psum995o2_61
  · exact le_trans (by norm_num) psum995o2_62
  · exact le_trans (by norm_num) psum995o2_63
  · exact le_trans (by norm_num) psum995o2_64
  · exact le_trans (by norm_num) psum995o2_65
  · exact le_trans (by norm_num) psum995o2_66
  · exact le_trans (by norm_num) psum995o2_67
  · exact le_trans (by norm_num) psum995o2_68
  · exact le_trans (by norm_num) psum995o2_69
  · exact le_trans (by norm_num) psum995o2_70
  · exact le_trans (by norm_num) psum995o2_71
  · exact le_trans (by norm_num) psum995o2_72
  · exact le_trans (by norm_num) psum995o2_73
  · exact le_trans (by norm_num) psum995o2_74
  · exact le_trans (by norm_num) psum995o2_75
  · exact le_trans (by norm_num) psum995o2_76
  · exact le_trans (by norm_num) psum995o2_77
  · exact le_trans (by norm_num) psum995o2_78
  · exact le_trans (by norm_num) psum995o2_79
  · exact le_trans (by norm_num) psum995o2_80
  · exact le_trans (by norm_num) psum995o2_81
  · exact le_trans (by norm_num) psum995o2_82
  · exact le_trans (by norm_num) psum995o2_83
  · exact le_trans (by norm_num) psum995o2_84
  · exact le_trans (by norm_num) psum995o2_85
  · exact le_trans (by norm_num) psum995o2_86
  · exact le_trans (by norm_num) psum995o2_87
  · exact le_trans (by norm_num) psum995o2_88
  · exact le_trans (by norm_num) psum995o2_89
  · exact le_trans (by norm_num) psum995o2_90
  · exact le_trans (by norm_num) psum995o2_91
  · exact le_trans (by norm_num) psum995o2_92
  · exact le_trans (by norm_num) psum995o2_93
  · exact le_trans (by norm_num) psum995o2_94
  · exact le_trans (by norm_num) psum995o2_95
  · exact le_trans (by norm_num) psum995o2_96
  · exact le_trans (by norm_num) psum995o2_97
  · exact le_trans (by norm_num) psum995o2_98
  · exact le_trans (by norm_num) psum995o2_99
  · exact le_trans (by norm_num) psum995o2_100
  · exact le_trans (by norm_num) psum995o2_101
  · exact le_trans (by norm_num) psum995o2_102
  · exact le_trans (by norm_num) psum995o2_103
  · exact le_trans (by norm_num) psum995o2_104
  · exact le_trans (by norm_num) psum995o2_105
  · exact le_trans (by norm_num) psum995o2_106
  · exact le_trans (by norm_num) psum995o2_107
  · exact le_trans (by norm_num) psum995o2_108
  · exact le_trans (by norm_num) psum995o2_109
  · exact le_trans (by norm_num) psum995o2_110
  · exact le_trans (by norm_num) psum995o2_111
  · exact le_trans (by norm_num) psum995o2_112
  · exact le_trans (by norm_num) psum995o2_113
  · exact le_trans (by norm_num) psum995o2_114
  · exact le_trans (by norm_num) psum995o2_115
  · exact le_trans (by norm_num) psum995o2_116
  · exact le_trans (by norm_num) psum995o2_117
  · exact le_trans (by norm_num) psum995o2_118
  · exact le_trans (by norm_num) psum995o2_119
  · exact le_trans (by norm_num) psum995o2_120
  · exact le_trans (by norm_num) psum995o2_121
  · exact le_trans (by norm_num) psum995o2_122
  · exact le_trans (by norm_num) psum995o2_123
  · exact le_trans (by norm_num) psum995o2_124
  · exact le_trans (by norm_num) psum995o2_125
  · exact le_trans (by norm_num) psum995o2_126
  · exact le_trans (by norm_num) psum995o2_127
  · exact le_trans (by norm_num) psum995o2_128
  · exact le_trans (by norm_num) psum995o2_129
  · exact le_trans (by norm_num) psum995o2_130
  · exact le_trans (by norm_num) psum995o2_131
  · exact le_trans (by norm_num) psum995o2_132
  · exact le_trans (by norm_num) psum995o2_133
  · exact le_trans (by norm_num) psum995o2_134
  · exact le_trans (by norm_num) psum995o2_135
  · exact le_trans (by norm_num) psum995o2_136
  · exact le_trans (by norm_num) psum995o2_137
  · exact le_trans (by norm_num) psum995o2_138
  · exact le_trans (by norm_num) psum995o2_139
  · exact le_trans (by norm_num) psum995o2_140
  · exact le_trans (by norm_num) psum995o2_141
  · exact le_trans (by norm_num) psum995o2_142
  · exact le_trans (by norm_num) psum995o2_143
  · exact le_trans (by norm_num) psum995o2_144
  · exact le_trans (by norm_num) psum995o2_145
  · exact le_trans (by norm_num) psum995o2_146
  · exact le_trans (by norm_num) psum995o2_147
  · exact le_trans (by norm_num) psum995o2_148
  · exact le_trans (by norm_num) psum995o2_149
  · exact le_trans (by norm_num) psum995o2_150
  · exact le_trans (by norm_num) psum995o2_151
  · exact le_trans (by norm_num) psum995o2_152
  · exact le_trans (by norm_num) psum995o2_153
  · exact le_trans (by norm_num) psum995o2_154
  · exact le_trans (by norm_num) psum995o2_155
  · exact le_trans (by norm_num) psum995o2_156
  · exact le_trans (by norm_num) psum995o2_157
  · exact le_trans (by norm_num) psum995o2_158
  · exact le_trans (by norm_num) psum995o2_159
  · exact le_trans (by norm_num) psum995o2_160
  · exact le_trans (by norm_num) psum995o2_161
  · exact le_trans (by norm_num) psum995o2_162
  · exact le_trans (by norm_num) psum995o2_163
  · exact le_trans (by norm_num) psum995o2_164
  · exact le_trans (by norm_num) psum995o2_165
  · exact le_trans (by norm_num) psum995o2_166
  · exact le_trans (by norm_num) psum995o2_167
  · exact le_trans (by norm_num) psum995o2_168
  · exact le_trans (by norm_num) psum995o2_169
  · exact le_trans (by norm_num) psum995o2_170
  · exact le_trans (by norm_num) psum995o2_171
  · exact le_trans (by norm_num) psum995o2_172
  · exact le_trans (by norm_num) psum995o2_173
  · exact le_trans (by norm_num) psum995o2_174
  · exact le_trans (by norm_num) psum995o2_175
  · exact le_trans (by norm_num) psum995o2_176
  · exact le_trans (by norm_num) psum995o2_177
  · exact le_trans (by norm_num) psum995o2_178
  · exact le_trans (by norm_num) psum995o2_179
  · exact le_trans (by norm_num) psum995o2_180
  · exact le_trans (by norm_num) psum995o2_181
  · exact le_trans (by norm_num) psum995o2_182
  · exact le_trans (by norm_num) psum995o2_183
  · exact le_trans (by norm_num) psum995o2_184
  · exact le_trans (by norm_num) psum995o2_185
  · exact le_trans (by norm_num) psum995o2_186
  · exact le_trans (by norm_num) psum995o2_187
  · exact le_trans (by norm_num) psum995o2_188
  · exact le_trans (by norm_num) psum995o2_189
  · exact le_trans (by norm_num) psum995o2_190
  · exact le_trans (by norm_num) psum995o2_191
  · exact le_trans (by norm_num) psum995o2_192
  · exact le_trans (by norm_num) psum995o2_193
  · exact le_trans (by norm_num) psum995o2_194
  · exact le_trans (by norm_num) psum995o2_195
  · exact le_trans (by norm_num) psum995o2_196
  · exact le_trans (by norm_num) psum995o2_197
  · exact le_trans (by norm_num) psum995o2_198
  · exact le_trans (by norm_num) psum995o2_199
  · exact le_trans (by norm_num) psum995o2_200
  · exact le_trans (by norm_num) psum995o2_201
  · exact le_trans (by norm_num) psum995o2_202
  · exact le_trans (by norm_num) psum995o2_203
  · exact le_trans (by norm_num) psum995o2_204
  · exact le_trans (by norm_num) psum995o2_205
  · exact le_trans (by norm_num) psum995o2_206
  · exact le_trans (by norm_num) psum995o2_207
  · exact le_trans (by norm_num) psum995o2_208
  · exact le_trans (by norm_num) psum995o2_209
  · exact le_trans (by norm_num) psum995o2_210
  · exact le_trans (by norm_num) psum995o2_211
  · exact le_trans (by norm_num) psum995o2_212
  · exact le_trans (by norm_num) psum995o2_213
  · exact le_trans (by norm_num) psum995o2_214
  · exact le_trans (by norm_num) psum995o2_215
  · exact le_trans (by norm_num) psum995o2_216
  · exact le_trans (by norm_num) psum995o2_217
  · exact le_trans (by norm_num) psum995o2_218
  · exact le_trans (by norm_num) psum995o2_219
  · exact le_trans (by norm_num) psum995o2_220
  · exact le_trans (by norm_num) psum995o2_221
  · exact le_trans (by norm_num) psum995o2_222
  · exact le_trans (by norm_num) psum995o2_223
  · exact le_trans (by norm_num) psum995o2_224
  · exact le_trans (by norm_num) psum995o2_225
  · exact le_trans (by norm_num) psum995o2_226
  · exact le_trans (by norm_num) psum995o2_227
  · exact le_trans (by norm_num) psum995o2_228
  · exact le_trans (by norm_num) psum995o2_229
  · exact le_trans (by norm_num) psum995o2_230
  · exact le_trans (by norm_num) psum995o2_231
  · exact le_trans (by norm_num) psum995o2_232
  · exact le_trans (by norm_num) psum995o2_233
  · exact le_trans (by norm_num) psum995o2_234
  · exact le_trans (by norm_num) psum995o2_235
  · exact le_trans (by norm_num) psum995o2_236
  · exact le_trans (by norm_num) psum995o2_237
  · exact le_trans (by norm_num) psum995o2_238
  · exact le_trans (by norm_num) psum995o2_239
  · exact le_trans (by norm_num) psum995o2_240
  · exact le_trans (by norm_num) psum995o2_241
  · exact le_trans (by norm_num) psum995o2_242
  · exact le_trans (by norm_num) psum995o2_243
  · exact le_trans (by norm_num) psum995o2_244
  · exact le_trans (by norm_num) psum995o2_245
  · exact le_trans (by norm_num) psum995o2_246
  · exact le_trans (by norm_num) psum995o2_247
  · exact le_trans (by norm_num) psum995o2_248
  · exact le_trans (by norm_num) psum995o2_249
  · exact le_trans (by norm_num) psum995o2_250
  · exact le_trans (by norm_num) psum995o2_251
  · exact le_trans (by norm_num) psum995o2_252
  · exact le_trans (by norm_num) psum995o2_253
  · exact le_trans (by norm_num) psum995o2_254
  · exact le_trans (by norm_num) psum995o2_255
  · exact le_trans (by norm_num) psum995o2_256
  · exact le_trans (by norm_num) psum995o2_257
  · exact le_trans (by norm_num) psum995o2_258
  · exact le_trans (by norm_num) psum995o2_259
  · exact le_trans (by norm_num) psum995o2_260
  · exact le_trans (by norm_num) psum995o2_261
  · exact le_trans (by norm_num) psum995o2_262
  · exact le_trans (by norm_num) psum995o2_263
  · exact le_trans (by norm_num) psum995o2_264
  · exact le_trans (by norm_num) psum995o2_265
  · exact le_trans (by norm_num) psum995o2_266
  · exact le_trans (by norm_num) psum995o2_267
  · exact le_trans (by norm_num) psum995o2_268
  · exact le_trans (by norm_num) psum995o2_269
  · exact le_trans (by norm_num) psum995o2_270
  · exact le_trans (by norm_num) psum995o2_271
  · exact le_trans (by norm_num) psum995o2_272
  · exact le_trans (by norm_num) psum995o2_273
  · exact le_trans (by norm_num) psum995o2_274
  · exact le_trans (by norm_num) psum995o2_275
  · exact le_trans (by norm_num) psum995o2_276
  · exact le_trans (by norm_num) psum995o2_277
  · exact le_trans (by norm_num) psum995o2_278
  · exact le_trans (by norm_num) psum995o2_279
  · exact le_trans (by norm_num) psum995o2_280
  · exact le_trans (by norm_num) psum995o2_281
  · exact le_trans (by norm_num) psum995o2_282
  · exact le_trans (by norm_num) psum995o2_283
  · exact le_trans (by norm_num) psum995o2_284
  · exact le_trans (by norm_num) psum995o2_285
  · exact le_trans (by norm_num) psum995o2_286
  · exact le_trans (by norm_num) psum995o2_287
  · exact le_trans (by norm_num) psum995o2_288
  · exact le_trans (by norm_num) psum995o2_289
  · exact le_trans (by norm_num) psum995o2_290
  · exact le_trans (by norm_num) psum995o2_291
  · exact le_trans (by norm_num) psum995o2_292
  · exact le_trans (by norm_num) psum995o2_293
  · exact le_trans (by norm_num) psum995o2_294
  · exact le_trans (by norm_num) psum995o2_295
  · exact le_trans (by norm_num) psum995o2_296
  · exact le_trans (by norm_num) psum995o2_297
  · exact le_trans (by norm_num) psum995o2_298
  · exact le_trans (by norm_num) psum995o2_299
  · exact le_trans (by norm_num) psum995o2_300
  · exact le_trans (by norm_num) psum995o2_301
  · exact le_trans (by norm_num) psum995o2_302
  · exact le_trans (by norm_num) psum995o2_303
  · exact le_trans (by norm_num) psum995o2_304
  · exact le_trans (by norm_num) psum995o2_305
  · exact le_trans (by norm_num) psum995o2_306
  · exact le_trans (by norm_num) psum995o2_307
  · exact le_trans (by norm_num) psum995o2_308
  · exact le_trans (by norm_num) psum995o2_309
  · exact le_trans (by norm_num) psum995o2_310
  · exact le_trans (by norm_num) psum995o2_311
  · exact le_trans (by norm_num) psum995o2_312
  · exact le_trans (by norm_num) psum995o2_313
  · exact le_trans (by norm_num) psum995o2_314
  · exact le_trans (by norm_num) psum995o2_315
  · exact le_trans (by norm_num) psum995o2_316
  · exact le_trans (by norm_num) psum995o2_317
  · exact le_trans (by norm_num) psum995o2_318
  · exact le_trans (by norm_num) psum995o2_319
  · exact le_trans (by norm_num) psum995o2_320
  · exact le_trans (by norm_num) psum995o2_321
  · exact le_trans (by norm_num) psum995o2_322
  · exact le_trans (by norm_num) psum995o2_323
  · exact le_trans (by norm_num) psum995o2_324
  · exact le_trans (by norm_num) psum995o2_325
  · exact le_trans (by norm_num) psum995o2_326
  · exact le_trans (by norm_num) psum995o2_327
  · exact le_trans (by norm_num) psum995o2_328
  · exact le_trans (by norm_num) psum995o2_329
  · exact le_trans (by norm_num) psum995o2_330
  · exact le_trans (by norm_num) psum995o2_331
  · exact le_trans (by norm_num) psum995o2_332
  · exact le_trans (by norm_num) psum995o2_333
  · exact le_trans (by norm_num) psum995o2_334
  · exact le_trans (by norm_num) psum995o2_335
  · exact le_trans (by norm_num) psum995o2_336
  · exact le_trans (by norm_num) psum995o2_337
  · exact le_trans (by norm_num) psum995o2_338
  · exact le_trans (by norm_num) psum995o2_339
  · exact le_trans (by norm_num) psum995o2_340
  · exact le_trans (by norm_num) psum995o2_341
  · exact le_trans (by norm_num) psum995o2_342
  · exact le_trans (by norm_num) psum995o2_343
  · exact le_trans (by norm_num) psum995o2_344
  · exact le_trans (by norm_num) psum995o2_345
  · exact le_trans (by norm_num) psum995o2_346
  · exact le_trans (by norm_num) psum995o2_347
  · exact le_trans (by norm_num) psum995o2_348
  · exact le_trans (by norm_num) psum995o2_349
  · exact le_trans (by norm_num) psum995o2_350
  · exact le_trans (by norm_num) psum995o2_351
  · exact le_trans (by norm_num) psum995o2_352
  · exact le_trans (by norm_num) psum995o2_353
  · exact le_trans (by norm_num) psum995o2_354
  · exact le_trans (by norm_num) psum995o2_355
  · exact le_trans (by norm_num) psum995o2_356
  · exact le_trans (by norm_num) psum995o2_357
  · exact le_trans (by norm_num) psum995o2_358
  · exact le_trans (by norm_num) psum995o2_359
  · exact le_trans (by norm_num) psum995o2_360
  · exact le_trans (by norm_num) psum995o2_361
  · exact le_trans (by norm_num) psum995o2_362
  · exact le_trans (by norm_num) psum995o2_363
  · exact le_trans (by norm_num) psum995o2_364
  · exact le_trans (by norm_num) psum995o2_365
  · exact le_trans (by norm_num) psum995o2_366
  · exact le_trans (by norm_num) psum995o2_367
  · exact le_trans (by norm_num) psum995o2_368
  · exact le_trans (by norm_num) psum995o2_369
  · exact le_trans (by norm_num) psum995o2_370
  · exact le_trans (by norm_num) psum995o2_371
  · exact le_trans (by norm_num) psum995o2_372
  · exact le_trans (by norm_num) psum995o2_373
  · exact le_trans (by norm_num) psum995o2_374
  · exact le_trans (by norm_num) psum995o2_375
  · exact le_trans (by norm_num) psum995o2_376
  · exact le_trans (by norm_num) psum995o2_377
  · exact le_trans (by norm_num) psum995o2_378
  · exact le_trans (by norm_num) psum995o2_379
  · exact le_trans (by norm_num) psum995o2_380
  · exact le_trans (by norm_num) psum995o2_381
  · exact le_trans (by norm_num) psum995o2_382
  · exact le_trans (by norm_num) psum995o2_383
  · exact le_trans (by norm_num) psum995o2_384
  · exact le_trans (by norm_num) psum995o2_385
  · exact le_trans (by norm_num) psum995o2_386
  · exact le_trans (by norm_num) psum995o2_387
  · exact le_trans (by norm_num) psum995o2_388
  · exact le_trans (by norm_num) psum995o2_389
  · exact le_trans (by norm_num) psum995o2_390
  · exact le_trans (by norm_num) psum995o2_391
  · exact le_trans (by norm_num) psum995o2_392
  · exact le_trans (by norm_num) psum995o2_393
  · exact le_trans (by norm_num) psum995o2_394
  · exact le_trans (by norm_num) psum995o2_395
  · exact le_trans (by norm_num) psum995o2_396
  · exact le_trans (by norm_num) psum995o2_397
  · exact le_trans (by norm_num) psum995o2_398
  · exact le_trans (by norm_num) psum995o2_399
  · exact le_trans (by norm_num) psum995o2_400
  · exact le_trans (by norm_num) psum995o2_401
  · exact le_trans (by norm_num) psum995o2_402
  · exact le_trans (by norm_num) psum995o2_403
  · exact le_trans (by norm_num) psum995o2_404
  · exact le_trans (by norm_num) psum995o2_405
  · exact le_trans (by norm_num) psum995o2_406
  · exact le_trans (by norm_num) psum995o2_407
  · exact le_trans (by norm_num) psum995o2_408
  · exact le_trans (by norm_num) psum995o2_409
  · exact le_trans (by norm_num) psum995o2_410
  · exact le_trans (by norm_num) psum995o2_411
  · exact le_trans (by norm_num) psum995o2_412
  · exact le_trans (by norm_num) psum995o2_413
  · exact le_trans (by norm_num) psum995o2_414
  · exact le_trans (by norm_num) psum995o2_415
  · exact le_trans (by norm_num) psum995o2_416
  · exact le_trans (by norm_num) psum995o2_417
  · exact le_trans (by norm_num) psum995o2_418
  · exact le_trans (by norm_num) psum995o2_419
  · exact le_trans (by norm_num) psum995o2_420
  · exact le_trans (by norm_num) psum995o2_421
  · exact le_trans (by norm_num) psum995o2_422
  · exact le_trans (by norm_num) psum995o2_423
  · exact le_trans (by norm_num) psum995o2_424
  · exact le_trans (by norm_num) psum995o2_425
  · exact le_trans (by norm_num) psum995o2_426
  · exact le_trans (by norm_num) psum995o2_427
  · exact le_trans (by norm_num) psum995o2_428
  · exact le_trans (by norm_num) psum995o2_429
  · exact le_trans (by norm_num) psum995o2_430
  · exact le_trans (by norm_num) psum995o2_431
  · exact le_trans (by norm_num) psum995o2_432
  · exact le_trans (by norm_num) psum995o2_433
  · exact le_trans (by norm_num) psum995o2_434
  · exact le_trans (by norm_num) psum995o2_435
  · exact le_trans (by norm_num) psum995o2_436
  · exact le_trans (by norm_num) psum995o2_437
  · exact le_trans (by norm_num) psum995o2_438
  · exact le_trans (by norm_num) psum995o2_439
  · exact le_trans (by norm_num) psum995o2_440
  · exact le_trans (by norm_num) psum995o2_441
  · exact le_trans (by norm_num) psum995o2_442
  · exact le_trans (by norm_num) psum995o2_443
  · exact le_trans (by norm_num) psum995o2_444
  · exact le_trans (by norm_num) psum995o2_445
  · exact le_trans (by norm_num) psum995o2_446
  · exact le_trans (by norm_num) psum995o2_447
  · exact le_trans (by norm_num) psum995o2_448
  · exact le_trans (by norm_num) psum995o2_449
  · exact le_trans (by norm_num) psum995o2_450
  · exact le_trans (by norm_num) psum995o2_451
  · exact le_trans (by norm_num) psum995o2_452
  · exact le_trans (by norm_num) psum995o2_453
  · exact le_trans (by norm_num) psum995o2_454
  · exact le_trans (by norm_num) psum995o2_455
  · exact le_trans (by norm_num) psum995o2_456
  · exact le_trans (by norm_num) psum995o2_457
  · exact le_trans (by norm_num) psum995o2_458
  · exact le_trans (by norm_num) psum995o2_459
  · exact le_trans (by norm_num) psum995o2_460
  · exact le_trans (by norm_num) psum995o2_461
  · exact le_trans (by norm_num) psum995o2_462
  · exact le_trans (by norm_num) psum995o2_463
  · exact le_trans (by norm_num) psum995o2_464
  · exact le_trans (by norm_num) psum995o2_465
  · exact le_trans (by norm_num) psum995o2_466
  · exact le_trans (by norm_num) psum995o2_467
  · exact le_trans (by norm_num) psum995o2_468
  · exact le_trans (by norm_num) psum995o2_469
  · exact le_trans (by norm_num) psum995o2_470
  · exact le_trans (by norm_num) psum995o2_471
  · exact le_trans (by norm_num) psum995o2_472
  · exact le_trans (by norm_num) psum995o2_473
  · exact le_trans (by norm_num) psum995o2_474
  · exact le_trans (by norm_num) psum995o2_475
  · exact le_trans (by norm_num) psum995o2_476
  · exact le_trans (by norm_num) psum995o2_477
  · exact le_trans (by norm_num) psum995o2_478
  · exact le_trans (by norm_num) psum995o2_479
  · exact le_trans (by norm_num) psum995o2_480
  · exact le_trans (by norm_num) psum995o2_481
  · exact le_trans (by norm_num) psum995o2_482
  · exact le_trans (by norm_num) psum995o2_483
  · exact le_trans (by norm_num) psum995o2_484
  · exact le_trans (by norm_num) psum995o2_485
  · exact le_trans (by norm_num) psum995o2_486
  · exact le_trans (by norm_num) psum995o2_487
  · exact le_trans (by norm_num) psum995o2_488
  · exact le_trans (by norm_num) psum995o2_489
  · exact le_trans (by norm_num) psum995o2_490
  · exact le_trans (by norm_num) psum995o2_491
  · exact le_trans (by norm_num) psum995o2_492
  · exact le_trans (by norm_num) psum995o2_493
  · exact le_trans (by norm_num) psum995o2_494
  · exact le_trans (by norm_num) psum995o2_495
  · exact le_trans (by norm_num) psum995o2_496
  · exact le_trans (by norm_num) psum995o2_497
  · exact le_trans (by norm_num) psum995o2_498
  · exact le_trans (by norm_num) psum995o2_499
  · exact le_trans (by norm_num) psum995o2_500
  · exact le_trans (by norm_num) psum995o2_501
  · exact le_trans (by norm_num) psum995o2_502
  · exact le_trans (by norm_num) psum995o2_503
  · exact le_trans (by norm_num) psum995o2_504
  · exact le_trans (by norm_num) psum995o2_505
  · exact le_trans (by norm_num) psum995o2_506
  · exact le_trans (by norm_num) psum995o2_507
  · exact le_trans (by norm_num) psum995o2_508
  · exact le_trans (by norm_num) psum995o2_509
  · exact le_trans (by norm_num) psum995o2_510
  · exact le_trans (by norm_num) psum995o2_511
  · exact le_trans (by norm_num) psum995o2_512
  · exact le_trans (by norm_num) psum995o2_513
  · exact le_trans (by norm_num) psum995o2_514
  · exact le_trans (by norm_num) psum995o2_515
  · exact le_trans (by norm_num) psum995o2_516
  · exact le_trans (by norm_num) psum995o2_517
  · exact le_trans (by norm_num) psum995o2_518
  · exact le_trans (by norm_num) psum995o2_519
  · exact le_trans (by norm_num) psum995o2_520
  · exact le_trans (by norm_num) psum995o2_521
  · exact le_trans (by norm_num) psum995o2_522
  · exact le_trans (by norm_num) psum995o2_523
  · exact le_trans (by norm_num) psum995o2_524
  · exact le_trans (by norm_num) psum995o2_525
  · exact le_trans (by norm_num) psum995o2_526
  · exact le_trans (by norm_num) psum995o2_527
  · exact le_trans (by norm_num) psum995o2_528
  · exact le_trans (by norm_num) psum995o2_529
  · exact le_trans (by norm_num) psum995o2_530
  · exact le_trans (by norm_num) psum995o2_531
  · exact le_trans (by norm_num) psum995o2_532
  · exact le_trans (by norm_num) psum995o2_533
  · exact le_trans (by norm_num) psum995o2_534
  · exact le_trans (by norm_num) psum995o2_535
  · exact le_trans (by norm_num) psum995o2_536
  · exact le_trans (by norm_num) psum995o2_537
  · exact le_trans (by norm_num) psum995o2_538
  · exact le_trans (by norm_num) psum995o2_539
  · exact le_trans (by norm_num) psum995o2_540
  · exact le_trans (by norm_num) psum995o2_541
  · exact le_trans (by norm_num) psum995o2_542
  · exact le_trans (by norm_num) psum995o2_543
  · exact le_trans (by norm_num) psum995o2_544
  · exact le_trans (by norm_num) psum995o2_545
  · exact le_trans (by norm_num) psum995o2_546
  · exact le_trans (by norm_num) psum995o2_547
  · exact le_trans (by norm_num) psum995o2_548
  · exact le_trans (by norm_num) psum995o2_549
  · exact le_trans (by norm_num) psum995o2_550
  · exact le_trans (by norm_num) psum995o2_551
  · exact le_trans (by norm_num) psum995o2_552
  · exact le_trans (by norm_num) psum995o2_553
  · exact le_trans (by norm_num) psum995o2_554
  · exact le_trans (by norm_num) psum995o2_555
  · exact le_trans (by norm_num) psum995o2_556
  · exact le_trans (by norm_num) psum995o2_557
  · exact le_trans (by norm_num) psum995o2_558
  · exact le_trans (by norm_num) psum995o2_559
  · exact le_trans (by norm_num) psum995o2_560
  · exact le_trans (by norm_num) psum995o2_561
  · exact le_trans (by norm_num) psum995o2_562
  · exact le_trans (by norm_num) psum995o2_563
  · exact le_trans (by norm_num) psum995o2_564
  · exact le_trans (by norm_num) psum995o2_565
  · exact le_trans (by norm_num) psum995o2_566
  · exact le_trans (by norm_num) psum995o2_567
  · exact le_trans (by norm_num) psum995o2_568
  · exact le_trans (by norm_num) psum995o2_569
  · exact le_trans (by norm_num) psum995o2_570
  · exact le_trans (by norm_num) psum995o2_571
  · exact le_trans (by norm_num) psum995o2_572
  · exact le_trans (by norm_num) psum995o2_573
  · exact le_trans (by norm_num) psum995o2_574
  · exact le_trans (by norm_num) psum995o2_575
  · exact le_trans (by norm_num) psum995o2_576
  · exact le_trans (by norm_num) psum995o2_577
  · exact le_trans (by norm_num) psum995o2_578
  · exact le_trans (by norm_num) psum995o2_579
  · exact le_trans (by norm_num) psum995o2_580
  · exact le_trans (by norm_num) psum995o2_581
  · exact le_trans (by norm_num) psum995o2_582
  · exact le_trans (by norm_num) psum995o2_583
  · exact le_trans (by norm_num) psum995o2_584
  · exact le_trans (by norm_num) psum995o2_585
  · exact le_trans (by norm_num) psum995o2_586
  · exact le_trans (by norm_num) psum995o2_587
  · exact le_trans (by norm_num) psum995o2_588
  · exact le_trans (by norm_num) psum995o2_589
  · exact le_trans (by norm_num) psum995o2_590
  · exact le_trans (by norm_num) psum995o2_591
  · exact le_trans (by norm_num) psum995o2_592
  · exact le_trans (by norm_num) psum995o2_593
  · exact le_trans (by norm_num) psum995o2_594
  · exact le_trans (by norm_num) psum995o2_595
  · exact le_trans (by norm_num) psum995o2_596
  · exact le_trans (by norm_num) psum995o2_597
  · exact le_trans (by norm_num) psum995o2_598
  · exact le_trans (by norm_num) psum995o2_599
  · exact le_trans (by norm_num) psum995o2_600
  · exact le_trans (by norm_num) psum995o2_601
  · exact le_trans (by norm_num) psum995o2_602
  · exact le_trans (by norm_num) psum995o2_603
  · exact le_trans (by norm_num) psum995o2_604
  · exact le_trans (by norm_num) psum995o2_605
  · exact le_trans (by norm_num) psum995o2_606
  · exact le_trans (by norm_num) psum995o2_607
  · exact le_trans (by norm_num) psum995o2_608
  · exact le_trans (by norm_num) psum995o2_609
  · exact le_trans (by norm_num) psum995o2_610
  · exact le_trans (by norm_num) psum995o2_611
  · exact le_trans (by norm_num) psum995o2_612
  · exact le_trans (by norm_num) psum995o2_613
  · exact le_trans (by norm_num) psum995o2_614
  · exact le_trans (by norm_num) psum995o2_615
  · exact le_trans (by norm_num) psum995o2_616
  · exact le_trans (by norm_num) psum995o2_617
  · exact le_trans (by norm_num) psum995o2_618
  · exact le_trans (by norm_num) psum995o2_619
  · exact le_trans (by norm_num) psum995o2_620
  · exact le_trans (by norm_num) psum995o2_621
  · exact le_trans (by norm_num) psum995o2_622
  · exact le_trans (by norm_num) psum995o2_623
  · exact le_trans (by norm_num) psum995o2_624
  · exact le_trans (by norm_num) psum995o2_625
  · exact le_trans (by norm_num) psum995o2_626
  · exact le_trans (by norm_num) psum995o2_627
  · exact le_trans (by norm_num) psum995o2_628
  · exact le_trans (by norm_num) psum995o2_629
  · exact le_trans (by norm_num) psum995o2_630
  · exact le_trans (by norm_num) psum995o2_631
  · exact le_trans (by norm_num) psum995o2_632
  · exact le_trans (by norm_num) psum995o2_633
  · exact le_trans (by norm_num) psum995o2_634
  · exact le_trans (by norm_num) psum995o2_635
  · exact le_trans (by norm_num) psum995o2_636
  · exact le_trans (by norm_num) psum995o2_637
  · exact le_trans (by norm_num) psum995o2_638
  · exact le_trans (by norm_num) psum995o2_639
  · exact le_trans (by norm_num) psum995o2_640
  · exact le_trans (by norm_num) psum995o2_641
  · exact le_trans (by norm_num) psum995o2_642
  · exact le_trans (by norm_num) psum995o2_643
  · exact le_trans (by norm_num) psum995o2_644
  · exact le_trans (by norm_num) psum995o2_645
  · exact le_trans (by norm_num) psum995o2_646
  · exact le_trans (by norm_num) psum995o2_647
  · exact le_trans (by norm_num) psum995o2_648
  · exact le_trans (by norm_num) psum995o2_649
  · exact le_trans (by norm_num) psum995o2_650
  · exact le_trans (by norm_num) psum995o2_651
  · exact le_trans (by norm_num) psum995o2_652
  · exact le_trans (by norm_num) psum995o2_653
  · exact le_trans (by norm_num) psum995o2_654
  · exact le_trans (by norm_num) psum995o2_655
  · exact le_trans (by norm_num) psum995o2_656
  · exact le_trans (by norm_num) psum995o2_657
  · exact le_trans (by norm_num) psum995o2_658
  · exact le_trans (by norm_num) psum995o2_659
  · exact le_trans (by norm_num) psum995o2_660
  · exact le_trans (by norm_num) psum995o2_661
  · exact le_trans (by norm_num) psum995o2_662
  · exact le_trans (by norm_num) psum995o2_663
  · exact le_trans (by norm_num) psum995o2_664
  · exact le_trans (by norm_num) psum995o2_665
  · exact le_trans (by norm_num) psum995o2_666
  · exact le_trans (by norm_num) psum995o2_667
  · exact le_trans (by norm_num) psum995o2_668
  · exact le_trans (by norm_num) psum995o2_669
  · exact le_trans (by norm_num) psum995o2_670
  · exact le_trans (by norm_num) psum995o2_671
  · exact le_trans (by norm_num) psum995o2_672
  · exact le_trans (by norm_num) psum995o2_673
  · exact le_trans (by norm_num) psum995o2_674
  · exact le_trans (by norm_num) psum995o2_675
  · exact le_trans (by norm_num) psum995o2_676
  · exact le_trans (by norm_num) psum995o2_677
  · exact le_trans (by norm_num) psum995o2_678
  · exact le_trans (by norm_num) psum995o2_679
  · exact le_trans (by norm_num) psum995o2_680
  · exact le_trans (by norm_num) psum995o2_681
  · exact le_trans (by norm_num) psum995o2_682
  · exact le_trans (by norm_num) psum995o2_683
  · exact le_trans (by norm_num) psum995o2_684
  · exact le_trans (by norm_num) psum995o2_685
  · exact le_trans (by norm_num) psum995o2_686
  · exact le_trans (by norm_num) psum995o2_687
  · exact le_trans (by norm_num) psum995o2_688
  · exact le_trans (by norm_num) psum995o2_689
  · exact le_trans (by norm_num) psum995o2_690
  · exact le_trans (by norm_num) psum995o2_691
  · exact le_trans (by norm_num) psum995o2_692
  · exact le_trans (by norm_num) psum995o2_693
  · exact le_trans (by norm_num) psum995o2_694
  · exact le_trans (by norm_num) psum995o2_695
  · exact le_trans (by norm_num) psum995o2_696
  · exact le_trans (by norm_num) psum995o2_697
  · exact le_trans (by norm_num) psum995o2_698
  · exact le_trans (by norm_num) psum995o2_699
  · exact le_trans (by norm_num) psum995o2_700
  · exact le_trans (by norm_num) psum995o2_701
  · exact le_trans (by norm_num) psum995o2_702
  · exact le_trans (by norm_num) psum995o2_703
  · exact le_trans (by norm_num) psum995o2_704
  · exact le_trans (by norm_num) psum995o2_705
  · exact le_trans (by norm_num) psum995o2_706
  · exact le_trans (by norm_num) psum995o2_707
  · exact le_trans (by norm_num) psum995o2_708
  · exact le_trans (by norm_num) psum995o2_709
  · exact le_trans (by norm_num) psum995o2_710
  · exact le_trans (by norm_num) psum995o2_711
  · exact le_trans (by norm_num) psum995o2_712
  · exact le_trans (by norm_num) psum995o2_713
  · exact le_trans (by norm_num) psum995o2_714
  · exact le_trans (by norm_num) psum995o2_715
  · exact le_trans (by norm_num) psum995o2_716
  · exact le_trans (by norm_num) psum995o2_717
  · exact le_trans (by norm_num) psum995o2_718
  · exact le_trans (by norm_num) psum995o2_719
  · exact le_trans (by norm_num) psum995o2_720
  · exact le_trans (by norm_num) psum995o2_721
  · exact le_trans (by norm_num) psum995o2_722
  · exact le_trans (by norm_num) psum995o2_723
  · exact le_trans (by norm_num) psum995o2_724
  · exact le_trans (by norm_num) psum995o2_725
  · exact le_trans (by norm_num) psum995o2_726
  · exact le_trans (by norm_num) psum995o2_727
  · exact le_trans (by norm_num) psum995o2_728
  · exact le_trans (by norm_num) psum995o2_729
  · exact le_trans (by norm_num) psum995o2_730
  · exact le_trans (by norm_num) psum995o2_731
  · exact le_trans (by norm_num) psum995o2_732
  · exact le_trans (by norm_num) psum995o2_733
  · exact le_trans (by norm_num) psum995o2_734
  · exact le_trans (by norm_num) psum995o2_735
  · exact le_trans (by norm_num) psum995o2_736
  · exact le_trans (by norm_num) psum995o2_737
  · exact le_trans (by norm_num) psum995o2_738
  · exact le_trans (by norm_num) psum995o2_739
  · exact le_trans (by norm_num) psum995o2_740
  · exact le_trans (by norm_num) psum995o2_741
  · exact le_trans (by norm_num) psum995o2_742
  · exact le_trans (by norm_num) psum995o2_743
  · exact le_trans (by norm_num) psum995o2_744
  · exact le_trans (by norm_num) psum995o2_745
  · exact le_trans (by norm_num) psum995o2_746
  · exact le_trans (by norm_num) psum995o2_747
  · exact le_trans (by norm_num) psum995o2_748
  · exact le_trans (by norm_num) psum995o2_749
  · exact le_trans (by norm_num) psum995o2_750
  · exact le_trans (by norm_num) psum995o2_751
  · exact le_trans (by norm_num) psum995o2_752
  · exact le_trans (by norm_num) psum995o2_753
  · exact le_trans (by norm_num) psum995o2_754
  · exact le_trans (by norm_num) psum995o2_755
  · exact le_trans (by norm_num) psum995o2_756
  · exact le_trans (by norm_num) psum995o2_757
  · exact le_trans (by norm_num) psum995o2_758
  · exact le_trans (by norm_num) psum995o2_759
  · exact le_trans (by norm_num) psum995o2_760
  · exact le_trans (by norm_num) psum995o2_761
  · exact le_trans (by norm_num) psum995o2_762
  · exact le_trans (by norm_num) psum995o2_763
  · exact le_trans (by norm_num) psum995o2_764
  · exact le_trans (by norm_num) psum995o2_765
  · exact le_trans (by norm_num) psum995o2_766
  · exact le_trans (by norm_num) psum995o2_767
  · exact le_trans (by norm_num) psum995o2_768
  · exact le_trans (by norm_num) psum995o2_769
  · exact le_trans (by norm_num) psum995o2_770
  · exact le_trans (by norm_num) psum995o2_771
  · exact le_trans (by norm_num) psum995o2_772
  · exact le_trans (by norm_num) psum995o2_773
  · exact le_trans (by norm_num) psum995o2_774
  · exact le_trans (by norm_num) psum995o2_775
  · exact le_trans (by norm_num) psum995o2_776
  · exact le_trans (by norm_num) psum995o2_777
  · exact le_trans (by norm_num) psum995o2_778
  · exact le_trans (by norm_num) psum995o2_779
  · exact le_trans (by norm_num) psum995o2_780
  · exact le_trans (by norm_num) psum995o2_781
  · exact le_trans (by norm_num) psum995o2_782
  · exact le_trans (by norm_num) psum995o2_783
  · exact le_trans (by norm_num) psum995o2_784
  · exact le_trans (by norm_num) psum995o2_785
  · exact le_trans (by norm_num) psum995o2_786
  · exact le_trans (by norm_num) psum995o2_787
  · exact le_trans (by norm_num) psum995o2_788
  · exact le_trans (by norm_num) psum995o2_789
  · exact le_trans (by norm_num) psum995o2_790
  · exact le_trans (by norm_num) psum995o2_791
  · exact le_trans (by norm_num) psum995o2_792
  · exact le_trans (by norm_num) psum995o2_793
  · exact le_trans (by norm_num) psum995o2_794
  · exact le_trans (by norm_num) psum995o2_795
  · exact le_trans (by norm_num) psum995o2_796
  · exact le_trans (by norm_num) psum995o2_797
  · exact le_trans (by norm_num) psum995o2_798
  · exact le_trans (by norm_num) psum995o2_799
  · exact le_trans (by norm_num) psum995o2_800
  · exact le_trans (by norm_num) psum995o2_801
  · exact le_trans (by norm_num) psum995o2_802
  · exact le_trans (by norm_num) psum995o2_803
  · exact le_trans (by norm_num) psum995o2_804
  · exact le_trans (by norm_num) psum995o2_805
  · exact le_trans (by norm_num) psum995o2_806
  · exact le_trans (by norm_num) psum995o2_807
  · exact le_trans (by norm_num) psum995o2_808
  · exact le_trans (by norm_num) psum995o2_809
  · exact le_trans (by norm_num) psum995o2_810
  · exact le_trans (by norm_num) psum995o2_811
  · exact le_trans (by norm_num) psum995o2_812
  · exact le_trans (by norm_num) psum995o2_813
  · exact le_trans (by norm_num) psum995o2_814
  · exact le_trans (by norm_num) psum995o2_815
  · exact le_trans (by norm_num) psum995o2_816
  · exact le_trans (by norm_num) psum995o2_817
  · exact le_trans (by norm_num) psum995o2_818
  · exact le_trans (by norm_num) psum995o2_819
  · exact le_trans (by norm_num) psum995o2_820
  · exact le_trans (by norm_num) psum995o2_821
  · exact le_trans (by norm_num) psum995o2_822
  · exact le_trans (by norm_num) psum995o2_823
  · exact le_trans (by norm_num) psum995o2_824
  · exact le_trans (by norm_num) psum995o2_825
  · exact le_trans (by norm_num) psum995o2_826
  · exact le_trans (by norm_num) psum995o2_827
  · exact le_trans (by norm_num) psum995o2_828
  · exact le_trans (by norm_num) psum995o2_829
  · exact le_trans (by norm_num) psum995o2_830
  · exact le_trans (by norm_num) psum995o2_831
  · exact le_trans (by norm_num) psum995o2_832
  · exact le_trans (by norm_num) psum995o2_833
  · exact le_trans (by norm_num) psum995o2_834
  · exact le_trans (by norm_num) psum995o2_835
  · exact le_trans (by norm_num) psum995o2_836
  · exact le_trans (by norm_num) psum995o2_837
  · exact le_trans (by norm_num) psum995o2_838
  · exact le_trans (by norm_num) psum995o2_839
  · exact le_trans (by norm_num) psum995o2_840
  · exact le_trans (by norm_num) psum995o2_841
  · exact le_trans (by norm_num) psum995o2_842
  · exact le_trans (by norm_num) psum995o2_843
  · exact le_trans (by norm_num) psum995o2_844
  · exact le_trans (by norm_num) psum995o2_845
  · exact le_trans (by norm_num) psum995o2_846
  · exact le_trans (by norm_num) psum995o2_847
  · exact le_trans (by norm_num) psum995o2_848
  · exact le_trans (by norm_num) psum995o2_849
  · exact le_trans (by norm_num) psum995o2_850
  · exact le_trans (by norm_num) psum995o2_851
  · exact le_trans (by norm_num) psum995o2_852
  · exact le_trans (by norm_num) psum995o2_853
  · exact le_trans (by norm_num) psum995o2_854
  · exact le_trans (by norm_num) psum995o2_855
  · exact le_trans (by norm_num) psum995o2_856
  · exact le_trans (by norm_num) psum995o2_857
  · exact le_trans (by norm_num) psum995o2_858
  · exact le_trans (by norm_num) psum995o2_859
  · exact le_trans (by norm_num) psum995o2_860
  · exact le_trans (by norm_num) psum995o2_861
  · exact le_trans (by norm_num) psum995o2_862
  · exact le_trans (by norm_num) psum995o2_863
  · exact le_trans (by norm_num) psum995o2_864
  · exact le_trans (by norm_num) psum995o2_865
  · exact le_trans (by norm_num) psum995o2_866
  · exact le_trans (by norm_num) psum995o2_867
  · exact le_trans (by norm_num) psum995o2_868
  · exact le_trans (by norm_num) psum995o2_869
  · exact le_trans (by norm_num) psum995o2_870
  · exact le_trans (by norm_num) psum995o2_871
  · exact le_trans (by norm_num) psum995o2_872
  · exact le_trans (by norm_num) psum995o2_873
  · exact le_trans (by norm_num) psum995o2_874
  · exact le_trans (by norm_num) psum995o2_875
  · exact le_trans (by norm_num) psum995o2_876
  · exact le_trans (by norm_num) psum995o2_877
  · exact le_trans (by norm_num) psum995o2_878
  · exact le_trans (by norm_num) psum995o2_879
  · exact le_trans (by norm_num) psum995o2_880
  · exact le_trans (by norm_num) psum995o2_881
  · exact le_trans (by norm_num) psum995o2_882
  · exact le_trans (by norm_num) psum995o2_883
  · exact le_trans (by norm_num) psum995o2_884
  · exact le_trans (by norm_num) psum995o2_885
  · exact le_trans (by norm_num) psum995o2_886
  · exact le_trans (by norm_num) psum995o2_887
  · exact le_trans (by norm_num) psum995o2_888
  · exact le_trans (by norm_num) psum995o2_889
  · exact le_trans (by norm_num) psum995o2_890
  · exact le_trans (by norm_num) psum995o2_891
  · exact le_trans (by norm_num) psum995o2_892
  · exact le_trans (by norm_num) psum995o2_893
  · exact le_trans (by norm_num) psum995o2_894
  · exact le_trans (by norm_num) psum995o2_895
  · exact le_trans (by norm_num) psum995o2_896
  · exact le_trans (by norm_num) psum995o2_897
  · exact le_trans (by norm_num) psum995o2_898
  · exact le_trans (by norm_num) psum995o2_899
  · exact le_trans (by norm_num) psum995o2_900
  · exact le_trans (by norm_num) psum995o2_901
  · exact le_trans (by norm_num) psum995o2_902
  · exact le_trans (by norm_num) psum995o2_903
  · exact le_trans (by norm_num) psum995o2_904
  · exact le_trans (by norm_num) psum995o2_905
  · exact le_trans (by norm_num) psum995o2_906
  · exact le_trans (by norm_num) psum995o2_907
  · exact le_trans (by norm_num) psum995o2_908
  · exact le_trans (by norm_num) psum995o2_909
  · exact le_trans (by norm_num) psum995o2_910
  · exact le_trans (by norm_num) psum995o2_911
  · exact le_trans (by norm_num) psum995o2_912
  · exact le_trans (by norm_num) psum995o2_913
  · exact le_trans (by norm_num) psum995o2_914
  · exact le_trans (by norm_num) psum995o2_915
  · exact le_trans (by norm_num) psum995o2_916
  · exact le_trans (by norm_num) psum995o2_917
  · exact le_trans (by norm_num) psum995o2_918
  · exact le_trans (by norm_num) psum995o2_919
  · exact le_trans (by norm_num) psum995o2_920
  · exact le_trans (by norm_num) psum995o2_921
  · exact le_trans (by norm_num) psum995o2_922
  · exact le_trans (by norm_num) psum995o2_923
  · exact le_trans (by norm_num) psum995o2_924
  · exact le_trans (by norm_num) psum995o2_925
  · exact le_trans (by norm_num) psum995o2_926
  · exact le_trans (by norm_num) psum995o2_927
  · exact le_trans (by norm_num) psum995o2_928
  · exact le_trans (by norm_num) psum995o2_929
  · exact le_trans (by norm_num) psum995o2_930
  · exact le_trans (by norm_num) psum995o2_931
  · exact le_trans (by norm_num) psum995o2_932
  · exact le_trans (by norm_num) psum995o2_933
  · exact le_trans (by norm_num) psum995o2_934
  · exact le_trans (by norm_num) psum995o2_935
  · exact le_trans (by norm_num) psum995o2_936
  · exact le_trans (by norm_num) psum995o2_937
  · exact le_trans (by norm_num) psum995o2_938
  · exact le_trans (by norm_num) psum995o2_939
  · exact le_trans (by norm_num) psum995o2_940
  · exact le_trans (by norm_num) psum995o2_941
  · exact le_trans (by norm_num) psum995o2_942
  · exact le_trans (by norm_num) psum995o2_943
  · exact le_trans (by norm_num) psum995o2_944
  · exact le_trans (by norm_num) psum995o2_945
  · exact le_trans (by norm_num) psum995o2_946
  · exact le_trans (by norm_num) psum995o2_947
  · exact le_trans (by norm_num) psum995o2_948
  · exact le_trans (by norm_num) psum995o2_949
  · exact le_trans (by norm_num) psum995o2_950
  · exact le_trans (by norm_num) psum995o2_951
  · exact le_trans (by norm_num) psum995o2_952
  · exact le_trans (by norm_num) psum995o2_953
  · exact le_trans (by norm_num) psum995o2_954
  · exact le_trans (by norm_num) psum995o2_955
  · exact le_trans (by norm_num) psum995o2_956
  · exact le_trans (by norm_num) psum995o2_957
  · exact le_trans (by norm_num) psum995o2_958
  · exact le_trans (by norm_num) psum995o2_959
  · exact le_trans (by norm_num) psum995o2_960
  · exact le_trans (by norm_num) psum995o2_961
  · exact le_trans (by norm_num) psum995o2_962
  · exact le_trans (by norm_num) psum995o2_963
  · exact le_trans (by norm_num) psum995o2_964
  · exact le_trans (by norm_num) psum995o2_965
  · exact le_trans (by norm_num) psum995o2_966
  · exact le_trans (by norm_num) psum995o2_967
  · exact le_trans (by norm_num) psum995o2_968
  · exact le_trans (by norm_num) psum995o2_969
  · exact le_trans (by norm_num) psum995o2_970
  · exact le_trans (by norm_num) psum995o2_971
  · exact le_trans (by norm_num) psum995o2_972
  · exact le_trans (by norm_num) psum995o2_973
  · exact le_trans (by norm_num) psum995o2_974
  · exact le_trans (by norm_num) psum995o2_975
  · exact le_trans (by norm_num) psum995o2_976
  · exact le_trans (by norm_num) psum995o2_977
  · exact le_trans (by norm_num) psum995o2_978
  · exact le_trans (by norm_num) psum995o2_979
  · exact le_trans (by norm_num) psum995o2_980
  · exact le_trans (by norm_num) psum995o2_981
  · exact le_trans (by norm_num) psum995o2_982
  · exact le_trans (by norm_num) psum995o2_983
  · exact le_trans (by norm_num) psum995o2_984
  · exact le_trans (by norm_num) psum995o2_985
  · exact le_trans (by norm_num) psum995o2_986
  · exact le_trans (by norm_num) psum995o2_987
  · exact le_trans (by norm_num) psum995o2_988
  · exact le_trans (by norm_num) psum995o2_989
  · exact le_trans (by norm_num) psum995o2_990
  · exact le_trans (by norm_num) psum995o2_991
  · exact le_trans (by norm_num) psum995o2_992
  · exact le_trans (by norm_num) psum995o2_993
  · exact le_trans (by norm_num) psum995o2_994
  · exact le_trans (by norm_num) psum995o2_995
  · exact le_trans (by norm_num) psum995o2_996
  · exact le_trans (by norm_num) psum995o2_997
  · exact le_trans (by norm_num) psum995o2_998
  · exact le_trans (by norm_num) psum995o2_999
  · exact le_trans (by norm_num) psum995o2_1000

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum995o2_floor
#print axioms CriticalLinePhasor.DVP.psum995o2_1000
end AxiomAudit
