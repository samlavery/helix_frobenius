import RequestProject.DVPCos81Table

/-!
# The cosine partial-sum floor, `t = 81`
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 81` segment certificate. -/
def cos81c (n : ℕ) : ℝ := Real.cos (((81:ℕ):ℝ) * Real.log n)

theorem psum81_11 : ((106611/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos81c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/25000 : ℚ) : ℝ) ≤ cos81c 11 - ((13327/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_11).1
  push_cast at h ⊢
  linarith

theorem psum81_12 : ((457429/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos81c k)
      = (∑ k ∈ Finset.Icc 11 11, cos81c k) + cos81c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_11
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 12 - ((244217/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_13 : ((686119/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos81c k)
      = (∑ k ∈ Finset.Icc 11 12, cos81c k) + cos81c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_12
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 13 - ((2287/2500 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_14 : ((3735291/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos81c k)
      = (∑ k ∈ Finset.Icc 11 13, cos81c k) + cos81c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_13
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 14 - ((198171/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_15 : ((2291407/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos81c k)
      = (∑ k ∈ Finset.Icc 11 14, cos81c k) + cos81c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_14
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 15 - ((847563/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_16 : ((22693/5000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos81c k)
      = (∑ k ∈ Finset.Icc 11 15, cos81c k) + cos81c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_15
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 16 - ((-22087/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_17 : ((3550397/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos81c k)
      = (∑ k ∈ Finset.Icc 11 16, cos81c k) + cos81c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_16
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 17 - ((-988163/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_18 : ((1739479/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos81c k)
      = (∑ k ∈ Finset.Icc 11 17, cos81c k) + cos81c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_17
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 18 - ((-71399/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_19 : ((177797/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos81c k)
      = (∑ k ∈ Finset.Icc 11 18, cos81c k) + cos81c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_18
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 19 - ((966007/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_20 : ((1857171/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos81c k)
      = (∑ k ∈ Finset.Icc 11 19, cos81c k) + cos81c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_19
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 20 - ((-730543/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_21 : ((58172/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos81c k)
      = (∑ k ∈ Finset.Icc 11 20, cos81c k) + cos81c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_20
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 21 - ((4353/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_22 : ((430223/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos81c k)
      = (∑ k ∈ Finset.Icc 11 21, cos81c k) + cos81c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_21
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 22 - ((289631/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_23 : ((1710867/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos81c k)
      = (∑ k ∈ Finset.Icc 11 22, cos81c k) + cos81c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_22
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 23 - ((-110057/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_24 : ((440403/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos81c k)
      = (∑ k ∈ Finset.Icc 11 23, cos81c k) + cos81c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_23
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 24 - ((15349/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_25 : ((170213/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos81c k)
      = (∑ k ∈ Finset.Icc 11 24, cos81c k) + cos81c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_24
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 25 - ((-99973/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_26 : ((1101037/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos81c k)
      = (∑ k ∈ Finset.Icc 11 25, cos81c k) + cos81c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_25
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 26 - ((124991/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_27 : ((3406741/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos81c k)
      = (∑ k ∈ Finset.Icc 11 26, cos81c k) + cos81c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_26
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 27 - ((-997367/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_28 : ((4370897/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos81c k)
      = (∑ k ∈ Finset.Icc 11 27, cos81c k) + cos81c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_27
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 28 - ((241049/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_29 : ((3527663/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos81c k)
      = (∑ k ∈ Finset.Icc 11 28, cos81c k) + cos81c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_28
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 29 - ((-421597/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_30 : ((4098547/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos81c k)
      = (∑ k ∈ Finset.Icc 11 29, cos81c k) + cos81c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_29
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 30 - ((142731/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_31 : ((994199/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos81c k)
      = (∑ k ∈ Finset.Icc 11 30, cos81c k) + cos81c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_30
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 31 - ((-121711/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_32 : ((3543651/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos81c k)
      = (∑ k ∈ Finset.Icc 11 31, cos81c k) + cos81c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_31
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 32 - ((-86621/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_33 : ((554183/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos81c k)
      = (∑ k ∈ Finset.Icc 11 32, cos81c k) + cos81c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_32
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 33 - ((889853/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_34 : ((692889/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos81c k)
      = (∑ k ∈ Finset.Icc 11 33, cos81c k) + cos81c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_33
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 34 - ((-968979/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_35 : ((15871/4000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos81c k)
      = (∑ k ∈ Finset.Icc 11 34, cos81c k) + cos81c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_34
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 35 - ((100669/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_36 : ((1073479/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos81c k)
      = (∑ k ∈ Finset.Icc 11 35, cos81c k) + cos81c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_35
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 36 - ((163103/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_37 : ((3343463/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos81c k)
      = (∑ k ∈ Finset.Icc 11 36, cos81c k) + cos81c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_36
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 37 - ((-950413/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_38 : ((4130197/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos81c k)
      = (∑ k ∈ Finset.Icc 11 37, cos81c k) + cos81c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_37
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 38 - ((393387/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_39 : ((4261787/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos81c k)
      = (∑ k ∈ Finset.Icc 11 38, cos81c k) + cos81c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_38
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 39 - ((13163/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_40 : ((830417/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos81c k)
      = (∑ k ∈ Finset.Icc 11 39, cos81c k) + cos81c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_39
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 40 - ((-940079/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_41 : ((2011471/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos81c k)
      = (∑ k ∈ Finset.Icc 11 40, cos81c k) + cos81c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_40
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 41 - ((350657/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_42 : ((4423759/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos81c k)
      = (∑ k ∈ Finset.Icc 11 41, cos81c k) + cos81c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_41
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 42 - ((400857/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_43 : ((3426703/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos81c k)
      = (∑ k ∈ Finset.Icc 11 42, cos81c k) + cos81c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_42
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 43 - ((-124627/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_44 : ((909777/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos81c k)
      = (∑ k ∈ Finset.Icc 11 43, cos81c k) + cos81c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_43
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 44 - ((42489/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_45 : ((181341/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos81c k)
      = (∑ k ∈ Finset.Icc 11 44, cos81c k) + cos81c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_44
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 45 - ((894457/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_46 : ((3910091/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos81c k)
      = (∑ k ∈ Finset.Icc 11 45, cos81c k) + cos81c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_45
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 46 - ((-311697/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_47 : ((3245783/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos81c k)
      = (∑ k ∈ Finset.Icc 11 46, cos81c k) + cos81c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_46
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 47 - ((-166067/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_48 : ((2037789/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos81c k)
      = (∑ k ∈ Finset.Icc 11 47, cos81c k) + cos81c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_47
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 48 - ((165967/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_49 : ((568559/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos81c k)
      = (∑ k ∈ Finset.Icc 11 48, cos81c k) + cos81c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_48
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 49 - ((236467/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_50 : ((1819109/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos81c k)
      = (∑ k ∈ Finset.Icc 11 49, cos81c k) + cos81c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_49
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 50 - ((-455107/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_51 : ((1627249/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos81c k)
      = (∑ k ∈ Finset.Icc 11 50, cos81c k) + cos81c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_50
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 51 - ((-1199/3125 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_52 : ((1044679/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos81c k)
      = (∑ k ∈ Finset.Icc 11 51, cos81c k) + cos81c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_51
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 52 - ((462129/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_53 : ((4586073/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos81c k)
      = (∑ k ∈ Finset.Icc 11 52, cos81c k) + cos81c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_52
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 53 - ((407397/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_54 : ((462169/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos81c k)
      = (∑ k ∈ Finset.Icc 11 53, cos81c k) + cos81c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_53
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 54 - ((-888681/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_55 : ((791351/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos81c k)
      = (∑ k ∈ Finset.Icc 11 54, cos81c k) + cos81c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_54
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 55 - ((-132977/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_56 : ((3947849/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos81c k)
      = (∑ k ∈ Finset.Icc 11 55, cos81c k) + cos81c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_55
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 56 - ((156497/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_57 : ((4671599/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos81c k)
      = (∑ k ∈ Finset.Icc 11 56, cos81c k) + cos81c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_56
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 57 - ((72379/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_58 : ((4107369/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos81c k)
      = (∑ k ∈ Finset.Icc 11 57, cos81c k) + cos81c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_57
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 58 - ((-56419/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_59 : ((319153/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos81c k)
      = (∑ k ∈ Finset.Icc 11 58, cos81c k) + cos81c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_58
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 59 - ((-915799/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_60 : ((678793/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos81c k)
      = (∑ k ∈ Finset.Icc 11 59, cos81c k) + cos81c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_59
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 60 - ((8099/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_61 : ((1098383/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos81c k)
      = (∑ k ∈ Finset.Icc 11 60, cos81c k) + cos81c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_60
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 61 - ((999607/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_62 : ((583939/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos81c k)
      = (∑ k ∈ Finset.Icc 11 61, cos81c k) + cos81c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_61
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 62 - ((13901/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_63 : ((955591/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos81c k)
      = (∑ k ∈ Finset.Icc 11 62, cos81c k) + cos81c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_62
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 63 - ((-212277/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_64 : ((613987/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos81c k)
      = (∑ k ∈ Finset.Icc 11 63, cos81c k) + cos81c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_63
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 64 - ((-752389/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_65 : ((173157/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos81c k)
      = (∑ k ∈ Finset.Icc 11 64, cos81c k) + cos81c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_64
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 65 - ((78649/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_66 : ((4460649/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos81c k)
      = (∑ k ∈ Finset.Icc 11 65, cos81c k) + cos81c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_65
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 66 - ((997549/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_67 : ((118489/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos81c k)
      = (∑ k ∈ Finset.Icc 11 66, cos81c k) + cos81c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_66
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 67 - ((278951/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_68 : ((493193/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos81c k)
      = (∑ k ∈ Finset.Icc 11 67, cos81c k) + cos81c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_67
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 68 - ((-99247/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_69 : ((1541103/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos81c k)
      = (∑ k ∈ Finset.Icc 11 68, cos81c k) + cos81c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_68
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 69 - ((-431649/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_70 : ((3205569/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos81c k)
      = (∑ k ∈ Finset.Icc 11 69, cos81c k) + cos81c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_69
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 70 - ((123403/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_71 : ((4161419/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos81c k)
      = (∑ k ∈ Finset.Icc 11 70, cos81c k) + cos81c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_70
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 71 - ((95589/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_72 : ((1208183/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos81c k)
      = (∑ k ∈ Finset.Icc 11 71, cos81c k) + cos81c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_71
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 72 - ((671353/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_73 : ((4460633/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos81c k)
      = (∑ k ∈ Finset.Icc 11 72, cos81c k) + cos81c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_72
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 73 - ((-372059/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_74 : ((173221/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos81c k)
      = (∑ k ∈ Finset.Icc 11 73, cos81c k) + cos81c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_73
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 74 - ((-996173/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_75 : ((2923869/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos81c k)
      = (∑ k ∈ Finset.Icc 11 74, cos81c k) + cos81c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_74
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 75 - ((-540511/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_76 : ((3404851/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos81c k)
      = (∑ k ∈ Finset.Icc 11 75, cos81c k) + cos81c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_75
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 76 - ((240511/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_77 : ((110119/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos81c k)
      = (∑ k ∈ Finset.Icc 11 76, cos81c k) + cos81c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_76
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 77 - ((999949/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_78 : ((2457607/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos81c k)
      = (∑ k ∈ Finset.Icc 11 77, cos81c k) + cos81c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_77
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 78 - ((255247/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_79 : ((1109793/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos81c k)
      = (∑ k ∈ Finset.Icc 11 78, cos81c k) + cos81c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_78
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 79 - ((-238001/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_80 : ((3440689/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos81c k)
      = (∑ k ∈ Finset.Icc 11 79, cos81c k) + cos81c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_79
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 80 - ((-998443/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_81 : ((2859301/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos81c k)
      = (∑ k ∈ Finset.Icc 11 80, cos81c k) + cos81c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_80
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 81 - ((-145337/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_82 : ((3224131/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos81c k)
      = (∑ k ∈ Finset.Icc 11 81, cos81c k) + cos81c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_81
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 82 - ((36487/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_83 : ((2100483/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos81c k)
      = (∑ k ∈ Finset.Icc 11 82, cos81c k) + cos81c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_82
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 83 - ((1563/1600 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_84 : ((4929473/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos81c k)
      = (∑ k ∈ Finset.Icc 11 83, cos81c k) + cos81c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_83
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 84 - ((728547/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_85 : ((4787521/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos81c k)
      = (∑ k ∈ Finset.Icc 11 84, cos81c k) + cos81c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_84
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 85 - ((-17739/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_86 : ((24381/6250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos81c k)
      = (∑ k ∈ Finset.Icc 11 85, cos81c k) + cos81c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_85
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 86 - ((-886521/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_87 : ((750709/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos81c k)
      = (∑ k ∈ Finset.Icc 11 86, cos81c k) + cos81c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_86
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 87 - ((-224521/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_88 : ((2814261/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos81c k)
      = (∑ k ∈ Finset.Icc 11 87, cos81c k) + cos81c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_87
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 88 - ((-37707/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_89 : ((3477801/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos81c k)
      = (∑ k ∈ Finset.Icc 11 88, cos81c k) + cos81c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_88
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 89 - ((33179/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_90 : ((4475971/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos81c k)
      = (∑ k ∈ Finset.Icc 11 89, cos81c k) + cos81c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_89
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 90 - ((99821/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_91 : ((1263411/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos81c k)
      = (∑ k ∈ Finset.Icc 11 90, cos81c k) + cos81c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_90
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 91 - ((577713/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_92 : ((2393759/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos81c k)
      = (∑ k ∈ Finset.Icc 11 91, cos81c k) + cos81c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_91
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 92 - ((-133043/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_93 : ((1938381/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos81c k)
      = (∑ k ∈ Finset.Icc 11 92, cos81c k) + cos81c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_92
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 93 - ((-227679/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_94 : ((2972199/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos81c k)
      = (∑ k ∈ Finset.Icc 11 93, cos81c k) + cos81c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_93
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 94 - ((-904523/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_95 : ((2702433/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos81c k)
      = (∑ k ∈ Finset.Icc 11 94, cos81c k) + cos81c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_94
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 95 - ((-134863/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_96 : ((3246283/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos81c k)
      = (∑ k ∈ Finset.Icc 11 95, cos81c k) + cos81c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_95
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 96 - ((54389/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_97 : ((2117023/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos81c k)
      = (∑ k ∈ Finset.Icc 11 96, cos81c k) + cos81c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_96
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 97 - ((987803/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_98 : ((1253767/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos81c k)
      = (∑ k ∈ Finset.Icc 11 97, cos81c k) + cos81c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_97
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 98 - ((390531/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_99 : ((2544491/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos81c k)
      = (∑ k ∈ Finset.Icc 11 98, cos81c k) + cos81c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_98
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 99 - ((36977/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum81_100 : ((4414613/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos81c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos81c k)
      = (∑ k ∈ Finset.Icc 11 99, cos81c k) + cos81c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos81c
    simpa using h
  have hprev := psum81_99
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos81c 100 - ((-674329/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos81_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

/-- **The Abel floor at `t = 81`.** -/
theorem psum81_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 100 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos81c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum81_11
  · exact le_trans (by norm_num) psum81_12
  · exact le_trans (by norm_num) psum81_13
  · exact le_trans (by norm_num) psum81_14
  · exact le_trans (by norm_num) psum81_15
  · exact le_trans (by norm_num) psum81_16
  · exact le_trans (by norm_num) psum81_17
  · exact le_trans (by norm_num) psum81_18
  · exact le_trans (by norm_num) psum81_19
  · exact le_trans (by norm_num) psum81_20
  · exact le_trans (by norm_num) psum81_21
  · exact le_trans (by norm_num) psum81_22
  · exact le_trans (by norm_num) psum81_23
  · exact le_trans (by norm_num) psum81_24
  · exact le_trans (by norm_num) psum81_25
  · exact le_trans (by norm_num) psum81_26
  · exact le_trans (by norm_num) psum81_27
  · exact le_trans (by norm_num) psum81_28
  · exact le_trans (by norm_num) psum81_29
  · exact le_trans (by norm_num) psum81_30
  · exact le_trans (by norm_num) psum81_31
  · exact le_trans (by norm_num) psum81_32
  · exact le_trans (by norm_num) psum81_33
  · exact le_trans (by norm_num) psum81_34
  · exact le_trans (by norm_num) psum81_35
  · exact le_trans (by norm_num) psum81_36
  · exact le_trans (by norm_num) psum81_37
  · exact le_trans (by norm_num) psum81_38
  · exact le_trans (by norm_num) psum81_39
  · exact le_trans (by norm_num) psum81_40
  · exact le_trans (by norm_num) psum81_41
  · exact le_trans (by norm_num) psum81_42
  · exact le_trans (by norm_num) psum81_43
  · exact le_trans (by norm_num) psum81_44
  · exact le_trans (by norm_num) psum81_45
  · exact le_trans (by norm_num) psum81_46
  · exact le_trans (by norm_num) psum81_47
  · exact le_trans (by norm_num) psum81_48
  · exact le_trans (by norm_num) psum81_49
  · exact le_trans (by norm_num) psum81_50
  · exact le_trans (by norm_num) psum81_51
  · exact le_trans (by norm_num) psum81_52
  · exact le_trans (by norm_num) psum81_53
  · exact le_trans (by norm_num) psum81_54
  · exact le_trans (by norm_num) psum81_55
  · exact le_trans (by norm_num) psum81_56
  · exact le_trans (by norm_num) psum81_57
  · exact le_trans (by norm_num) psum81_58
  · exact le_trans (by norm_num) psum81_59
  · exact le_trans (by norm_num) psum81_60
  · exact le_trans (by norm_num) psum81_61
  · exact le_trans (by norm_num) psum81_62
  · exact le_trans (by norm_num) psum81_63
  · exact le_trans (by norm_num) psum81_64
  · exact le_trans (by norm_num) psum81_65
  · exact le_trans (by norm_num) psum81_66
  · exact le_trans (by norm_num) psum81_67
  · exact le_trans (by norm_num) psum81_68
  · exact le_trans (by norm_num) psum81_69
  · exact le_trans (by norm_num) psum81_70
  · exact le_trans (by norm_num) psum81_71
  · exact le_trans (by norm_num) psum81_72
  · exact le_trans (by norm_num) psum81_73
  · exact le_trans (by norm_num) psum81_74
  · exact le_trans (by norm_num) psum81_75
  · exact le_trans (by norm_num) psum81_76
  · exact le_trans (by norm_num) psum81_77
  · exact le_trans (by norm_num) psum81_78
  · exact le_trans (by norm_num) psum81_79
  · exact le_trans (by norm_num) psum81_80
  · exact le_trans (by norm_num) psum81_81
  · exact le_trans (by norm_num) psum81_82
  · exact le_trans (by norm_num) psum81_83
  · exact le_trans (by norm_num) psum81_84
  · exact le_trans (by norm_num) psum81_85
  · exact le_trans (by norm_num) psum81_86
  · exact le_trans (by norm_num) psum81_87
  · exact le_trans (by norm_num) psum81_88
  · exact le_trans (by norm_num) psum81_89
  · exact le_trans (by norm_num) psum81_90
  · exact le_trans (by norm_num) psum81_91
  · exact le_trans (by norm_num) psum81_92
  · exact le_trans (by norm_num) psum81_93
  · exact le_trans (by norm_num) psum81_94
  · exact le_trans (by norm_num) psum81_95
  · exact le_trans (by norm_num) psum81_96
  · exact le_trans (by norm_num) psum81_97
  · exact le_trans (by norm_num) psum81_98
  · exact le_trans (by norm_num) psum81_99
  · exact le_trans (by norm_num) psum81_100

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum81_floor
#print axioms CriticalLinePhasor.DVP.psum81_100
end AxiomAudit
