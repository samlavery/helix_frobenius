import RequestProject.DVPCos91Table

/-!
# The cosine partial-sum floor, `t = 91`
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 91` segment certificate. -/
def cos91c (n : ℕ) : ℝ := Real.cos (((91:ℕ):ℝ) * Real.log n)

theorem psum91_11 : ((-211/1600 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos91c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/25000 : ℚ) : ℝ) ≤ cos91c 11 - ((-26367/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_11).1
  push_cast at h ⊢
  linarith

theorem psum91_12 : ((865763/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos91c k)
      = (∑ k ∈ Finset.Icc 11 11, cos91c k) + cos91c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_11
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 12 - ((498839/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_13 : ((1461523/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos91c k)
      = (∑ k ∈ Finset.Icc 11 12, cos91c k) + cos91c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_12
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 13 - ((2979/5000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_14 : ((409543/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos91c k)
      = (∑ k ∈ Finset.Icc 11 13, cos91c k) + cos91c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_13
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 14 - ((176689/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_15 : ((227447/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos91c k)
      = (∑ k ∈ Finset.Icc 11 14, cos91c k) + cos91c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_14
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 15 - ((45361/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_16 : ((475617/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos91c k)
      = (∑ k ∈ Finset.Icc 11 15, cos91c k) + cos91c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_15
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 16 - ((558549/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_17 : ((209731/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos91c k)
      = (∑ k ∈ Finset.Icc 11 16, cos91c k) + cos91c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_16
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 17 - ((977651/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_18 : ((2000259/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos91c k)
      = (∑ k ∈ Finset.Icc 11 17, cos91c k) + cos91c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_17
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 18 - ((322431/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_19 : ((677121/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos91c k)
      = (∑ k ∈ Finset.Icc 11 18, cos91c k) + cos91c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_18
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 19 - ((-614873/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_20 : ((1312601/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos91c k)
      = (∑ k ∈ Finset.Icc 11 19, cos91c k) + cos91c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_19
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 20 - ((-760363/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_21 : ((345533/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos91c k)
      = (∑ k ∈ Finset.Icc 11 20, cos91c k) + cos91c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_20
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 21 - ((103771/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_22 : ((28539/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos91c k)
      = (∑ k ∈ Finset.Icc 11 21, cos91c k) + cos91c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_21
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 22 - ((22417/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_23 : ((679353/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos91c k)
      = (∑ k ∈ Finset.Icc 11 22, cos91c k) + cos91c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_22
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 23 - ((-849923/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_24 : ((1850929/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos91c k)
      = (∑ k ∈ Finset.Icc 11 23, cos91c k) + cos91c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_23
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 24 - ((492243/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_25 : ((593969/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos91c k)
      = (∑ k ∈ Finset.Icc 11 24, cos91c k) + cos91c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_24
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 25 - ((-731973/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_26 : ((419179/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos91c k)
      = (∑ k ∈ Finset.Icc 11 25, cos91c k) + cos91c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_25
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 26 - ((383627/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_27 : ((162631/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos91c k)
      = (∑ k ∈ Finset.Icc 11 26, cos91c k) + cos91c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_26
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 27 - ((-25193/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_28 : ((3185711/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos91c k)
      = (∑ k ∈ Finset.Icc 11 27, cos91c k) + cos91c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_27
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 28 - ((-66869/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_29 : ((330403/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos91c k)
      = (∑ k ∈ Finset.Icc 11 28, cos91c k) + cos91c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_28
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 29 - ((118359/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_30 : ((648389/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos91c k)
      = (∑ k ∈ Finset.Icc 11 29, cos91c k) + cos91c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_29
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 30 - ((-12409/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_31 : ((3146417/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos91c k)
      = (∑ k ∈ Finset.Icc 11 30, cos91c k) + cos91c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_30
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 31 - ((-1492/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_32 : ((871871/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos91c k)
      = (∑ k ∈ Finset.Icc 11 31, cos91c k) + cos91c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_31
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 32 - ((341107/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_33 : ((1425659/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos91c k)
      = (∑ k ∈ Finset.Icc 11 32, cos91c k) + cos91c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_32
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 33 - ((-318063/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_34 : ((1874471/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos91c k)
      = (∑ k ∈ Finset.Icc 11 33, cos91c k) + cos91c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_33
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 34 - ((14026/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_35 : ((343753/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos91c k)
      = (∑ k ∈ Finset.Icc 11 34, cos91c k) + cos91c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_34
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 35 - ((-499439/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_36 : ((1780353/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos91c k)
      = (∑ k ∈ Finset.Icc 11 35, cos91c k) + cos91c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_35
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 36 - ((405361/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_37 : ((40849/12500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos91c k)
      = (∑ k ∈ Finset.Icc 11 36, cos91c k) + cos91c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_36
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 37 - ((-146373/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_38 : ((572447/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos91c k)
      = (∑ k ∈ Finset.Icc 11 37, cos91c k) + cos91c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_37
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 38 - ((-81129/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_39 : ((3792597/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos91c k)
      = (∑ k ∈ Finset.Icc 11 38, cos91c k) + cos91c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_38
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 39 - ((465201/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_40 : ((579513/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos91c k)
      = (∑ k ∈ Finset.Icc 11 39, cos91c k) + cos91c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_39
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 40 - ((-55937/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_41 : ((1554873/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos91c k)
      = (∑ k ∈ Finset.Icc 11 40, cos91c k) + cos91c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_40
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 41 - ((212221/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_42 : ((756039/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos91c k)
      = (∑ k ∈ Finset.Icc 11 41, cos91c k) + cos91c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_41
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 42 - ((670489/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_43 : ((698409/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos91c k)
      = (∑ k ∈ Finset.Icc 11 42, cos91c k) + cos91c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_42
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 43 - ((-986519/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_44 : ((314293/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos91c k)
      = (∑ k ∈ Finset.Icc 11 43, cos91c k) + cos91c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_43
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 44 - ((174667/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_45 : ((1908479/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos91c k)
      = (∑ k ∈ Finset.Icc 11 44, cos91c k) + cos91c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_44
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 45 - ((168517/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_46 : ((358089/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos91c k)
      = (∑ k ∈ Finset.Icc 11 45, cos91c k) + cos91c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_45
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 46 - ((-476103/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_47 : ((58809/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos91c k)
      = (∑ k ∈ Finset.Icc 11 46, cos91c k) + cos91c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_46
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 47 - ((37889/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_48 : ((1926563/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos91c k)
      = (∑ k ∈ Finset.Icc 11 47, cos91c k) + cos91c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_47
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 48 - ((228179/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_49 : ((3188849/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos91c k)
      = (∑ k ∈ Finset.Icc 11 48, cos91c k) + cos91c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_48
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 49 - ((-664237/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_50 : ((2643571/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos91c k)
      = (∑ k ∈ Finset.Icc 11 49, cos91c k) + cos91c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_49
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 50 - ((-272619/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_51 : ((3584461/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos91c k)
      = (∑ k ∈ Finset.Icc 11 50, cos91c k) + cos91c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_50
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 51 - ((94093/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_52 : ((3733049/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos91c k)
      = (∑ k ∈ Finset.Icc 11 51, cos91c k) + cos91c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_51
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 52 - ((37157/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_53 : ((2733099/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos91c k)
      = (∑ k ∈ Finset.Icc 11 52, cos91c k) + cos91c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_52
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 53 - ((-99991/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_54 : ((2876163/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos91c k)
      = (∑ k ∈ Finset.Icc 11 53, cos91c k) + cos91c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_53
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 54 - ((2236/15625 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_55 : ((1923423/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos91c k)
      = (∑ k ∈ Finset.Icc 11 54, cos91c k) + cos91c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_54
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 55 - ((970723/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_56 : ((1770179/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos91c k)
      = (∑ k ∈ Finset.Icc 11 55, cos91c k) + cos91c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_55
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 56 - ((-19153/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_57 : ((13007/5000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos91c k)
      = (∑ k ∈ Finset.Icc 11 56, cos91c k) + cos91c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_56
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 57 - ((-469459/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_58 : ((1478303/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos91c k)
      = (∑ k ∈ Finset.Icc 11 57, cos91c k) + cos91c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_57
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 58 - ((177623/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_59 : ((3896631/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos91c k)
      = (∑ k ∈ Finset.Icc 11 58, cos91c k) + cos91c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_58
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 59 - ((188013/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_60 : ((898687/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos91c k)
      = (∑ k ∈ Finset.Icc 11 59, cos91c k) + cos91c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_59
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 60 - ((-301843/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_61 : ((2623369/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos91c k)
      = (∑ k ∈ Finset.Icc 11 60, cos91c k) + cos91c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_60
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 61 - ((-971339/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_62 : ((1385843/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos91c k)
      = (∑ k ∈ Finset.Icc 11 61, cos91c k) + cos91c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_61
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 62 - ((148357/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_63 : ((3771063/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos91c k)
      = (∑ k ∈ Finset.Icc 11 62, cos91c k) + cos91c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_62
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 63 - ((999417/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_64 : ((484299/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos91c k)
      = (∑ k ∈ Finset.Icc 11 63, cos91c k) + cos91c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_63
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 64 - ((103369/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_65 : ((145443/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos91c k)
      = (∑ k ∈ Finset.Icc 11 64, cos91c k) + cos91c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_64
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 65 - ((-241373/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_66 : ((2478429/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos91c k)
      = (∑ k ∈ Finset.Icc 11 65, cos91c k) + cos91c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_65
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 66 - ((-430391/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_67 : ((3276119/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos91c k)
      = (∑ k ∈ Finset.Icc 11 66, cos91c k) + cos91c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_66
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 67 - ((79773/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_68 : ((4040343/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos91c k)
      = (∑ k ∈ Finset.Icc 11 67, cos91c k) + cos91c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_67
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 68 - ((95533/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_69 : ((3597617/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos91c k)
      = (∑ k ∈ Finset.Icc 11 68, cos91c k) + cos91c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_68
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 69 - ((-221343/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_70 : ((327119/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos91c k)
      = (∑ k ∈ Finset.Icc 11 69, cos91c k) + cos91c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_69
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 70 - ((-1569/1600 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_71 : ((2534183/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos91c k)
      = (∑ k ∈ Finset.Icc 11 70, cos91c k) + cos91c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_70
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 71 - ((-82729/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_72 : ((865621/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos91c k)
      = (∑ k ∈ Finset.Icc 11 71, cos91c k) + cos91c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_71
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 72 - ((928341/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_73 : ((4103963/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos91c k)
      = (∑ k ∈ Finset.Icc 11 72, cos91c k) + cos91c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_72
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 73 - ((641519/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_74 : ((3588383/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos91c k)
      = (∑ k ∈ Finset.Icc 11 73, cos91c k) + cos91c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_73
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 74 - ((-25777/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_75 : ((2606783/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos91c k)
      = (∑ k ∈ Finset.Icc 11 74, cos91c k) + cos91c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_74
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 75 - ((-24539/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_76 : ((2434463/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos91c k)
      = (∑ k ∈ Finset.Icc 11 75, cos91c k) + cos91c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_75
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 76 - ((-4307/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_77 : ((3284649/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos91c k)
      = (∑ k ∈ Finset.Icc 11 76, cos91c k) + cos91c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_76
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 77 - ((425113/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_78 : ((4098587/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos91c k)
      = (∑ k ∈ Finset.Icc 11 77, cos91c k) + cos91c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_77
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 78 - ((406989/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_79 : ((1945883/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos91c k)
      = (∑ k ∈ Finset.Icc 11 78, cos91c k) + cos91c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_78
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 79 - ((-206781/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_80 : ((18221/6250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos91c k)
      = (∑ k ∈ Finset.Icc 11 79, cos91c k) + cos91c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_79
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 80 - ((-488183/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_81 : ((1151817/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos91c k)
      = (∑ k ∈ Finset.Icc 11 80, cos91c k) + cos91c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_80
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 81 - ((-305843/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_82 : ((2746097/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos91c k)
      = (∑ k ∈ Finset.Icc 11 81, cos91c k) + cos91c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_81
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 82 - ((442503/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_83 : ((3746013/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos91c k)
      = (∑ k ∈ Finset.Icc 11 82, cos91c k) + cos91c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_82
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 83 - ((249989/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_84 : ((527111/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos91c k)
      = (∑ k ∈ Finset.Icc 11 83, cos91c k) + cos91c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_83
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 84 - ((94183/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_85 : ((3663309/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos91c k)
      = (∑ k ∈ Finset.Icc 11 84, cos91c k) + cos91c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_84
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 85 - ((-553539/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_86 : ((2666479/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos91c k)
      = (∑ k ∈ Finset.Icc 11 85, cos91c k) + cos91c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_85
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 86 - ((-99679/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_87 : ((2241757/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos91c k)
      = (∑ k ∈ Finset.Icc 11 86, cos91c k) + cos91c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_86
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 87 - ((-212341/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_88 : ((561503/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos91c k)
      = (∑ k ∈ Finset.Icc 11 87, cos91c k) + cos91c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_87
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 88 - ((282899/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_89 : ((3805743/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos91c k)
      = (∑ k ∈ Finset.Icc 11 88, cos91c k) + cos91c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_88
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 89 - ((249567/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_90 : ((4280877/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos91c k)
      = (∑ k ∈ Finset.Icc 11 89, cos91c k) + cos91c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_89
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 90 - ((237587/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_91 : ((1896167/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos91c k)
      = (∑ k ∈ Finset.Icc 11 90, cos91c k) + cos91c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_90
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 91 - ((-488503/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_92 : ((2794463/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos91c k)
      = (∑ k ∈ Finset.Icc 11 91, cos91c k) + cos91c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_91
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 92 - ((-997831/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_93 : ((1093473/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos91c k)
      = (∑ k ∈ Finset.Icc 11 92, cos91c k) + cos91c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_92
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 93 - ((-607477/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_94 : ((625461/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos91c k)
      = (∑ k ∈ Finset.Icc 11 93, cos91c k) + cos91c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_93
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 94 - ((157469/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_95 : ((3460779/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos91c k)
      = (∑ k ∈ Finset.Icc 11 94, cos91c k) + cos91c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_94
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 95 - ((38359/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_96 : ((33979/8000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos91c k)
      = (∑ k ∈ Finset.Icc 11 95, cos91c k) + cos91c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_95
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 96 - ((196659/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_97 : ((526209/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos91c k)
      = (∑ k ∈ Finset.Icc 11 96, cos91c k) + cos91c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_96
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 97 - ((-37663/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_98 : ((1692087/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos91c k)
      = (∑ k ∈ Finset.Icc 11 97, cos91c k) + cos91c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_97
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 98 - ((-412729/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_99 : ((2436191/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos91c k)
      = (∑ k ∈ Finset.Icc 11 98, cos91c k) + cos91c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_98
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 99 - ((-947943/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum91_100 : ((2110091/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos91c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos91c k)
      = (∑ k ∈ Finset.Icc 11 99, cos91c k) + cos91c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos91c
    simpa using h
  have hprev := psum91_99
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos91c 100 - ((-16303/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos91_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

/-- **The Abel floor at `t = 91`.** -/
theorem psum91_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 100 →
    ((-211/1600 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos91c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum91_11
  · exact le_trans (by norm_num) psum91_12
  · exact le_trans (by norm_num) psum91_13
  · exact le_trans (by norm_num) psum91_14
  · exact le_trans (by norm_num) psum91_15
  · exact le_trans (by norm_num) psum91_16
  · exact le_trans (by norm_num) psum91_17
  · exact le_trans (by norm_num) psum91_18
  · exact le_trans (by norm_num) psum91_19
  · exact le_trans (by norm_num) psum91_20
  · exact le_trans (by norm_num) psum91_21
  · exact le_trans (by norm_num) psum91_22
  · exact le_trans (by norm_num) psum91_23
  · exact le_trans (by norm_num) psum91_24
  · exact le_trans (by norm_num) psum91_25
  · exact le_trans (by norm_num) psum91_26
  · exact le_trans (by norm_num) psum91_27
  · exact le_trans (by norm_num) psum91_28
  · exact le_trans (by norm_num) psum91_29
  · exact le_trans (by norm_num) psum91_30
  · exact le_trans (by norm_num) psum91_31
  · exact le_trans (by norm_num) psum91_32
  · exact le_trans (by norm_num) psum91_33
  · exact le_trans (by norm_num) psum91_34
  · exact le_trans (by norm_num) psum91_35
  · exact le_trans (by norm_num) psum91_36
  · exact le_trans (by norm_num) psum91_37
  · exact le_trans (by norm_num) psum91_38
  · exact le_trans (by norm_num) psum91_39
  · exact le_trans (by norm_num) psum91_40
  · exact le_trans (by norm_num) psum91_41
  · exact le_trans (by norm_num) psum91_42
  · exact le_trans (by norm_num) psum91_43
  · exact le_trans (by norm_num) psum91_44
  · exact le_trans (by norm_num) psum91_45
  · exact le_trans (by norm_num) psum91_46
  · exact le_trans (by norm_num) psum91_47
  · exact le_trans (by norm_num) psum91_48
  · exact le_trans (by norm_num) psum91_49
  · exact le_trans (by norm_num) psum91_50
  · exact le_trans (by norm_num) psum91_51
  · exact le_trans (by norm_num) psum91_52
  · exact le_trans (by norm_num) psum91_53
  · exact le_trans (by norm_num) psum91_54
  · exact le_trans (by norm_num) psum91_55
  · exact le_trans (by norm_num) psum91_56
  · exact le_trans (by norm_num) psum91_57
  · exact le_trans (by norm_num) psum91_58
  · exact le_trans (by norm_num) psum91_59
  · exact le_trans (by norm_num) psum91_60
  · exact le_trans (by norm_num) psum91_61
  · exact le_trans (by norm_num) psum91_62
  · exact le_trans (by norm_num) psum91_63
  · exact le_trans (by norm_num) psum91_64
  · exact le_trans (by norm_num) psum91_65
  · exact le_trans (by norm_num) psum91_66
  · exact le_trans (by norm_num) psum91_67
  · exact le_trans (by norm_num) psum91_68
  · exact le_trans (by norm_num) psum91_69
  · exact le_trans (by norm_num) psum91_70
  · exact le_trans (by norm_num) psum91_71
  · exact le_trans (by norm_num) psum91_72
  · exact le_trans (by norm_num) psum91_73
  · exact le_trans (by norm_num) psum91_74
  · exact le_trans (by norm_num) psum91_75
  · exact le_trans (by norm_num) psum91_76
  · exact le_trans (by norm_num) psum91_77
  · exact le_trans (by norm_num) psum91_78
  · exact le_trans (by norm_num) psum91_79
  · exact le_trans (by norm_num) psum91_80
  · exact le_trans (by norm_num) psum91_81
  · exact le_trans (by norm_num) psum91_82
  · exact le_trans (by norm_num) psum91_83
  · exact le_trans (by norm_num) psum91_84
  · exact le_trans (by norm_num) psum91_85
  · exact le_trans (by norm_num) psum91_86
  · exact le_trans (by norm_num) psum91_87
  · exact le_trans (by norm_num) psum91_88
  · exact le_trans (by norm_num) psum91_89
  · exact le_trans (by norm_num) psum91_90
  · exact le_trans (by norm_num) psum91_91
  · exact le_trans (by norm_num) psum91_92
  · exact le_trans (by norm_num) psum91_93
  · exact le_trans (by norm_num) psum91_94
  · exact le_trans (by norm_num) psum91_95
  · exact le_trans (by norm_num) psum91_96
  · exact le_trans (by norm_num) psum91_97
  · exact le_trans (by norm_num) psum91_98
  · exact le_trans (by norm_num) psum91_99
  · exact le_trans (by norm_num) psum91_100

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum91_floor
#print axioms CriticalLinePhasor.DVP.psum91_100
end AxiomAudit
