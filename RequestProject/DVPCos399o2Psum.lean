import RequestProject.DVPCos399o2Table

/-!
# The cosine partial-sum floor, `t = 399/2`
-/

open Finset

noncomputable section

namespace CriticalLinePhasor.DVP

/-- The cosine sequence of the `t = 399/2` segment certificate. -/
def cos399o2c (n : ℕ) : ℝ := Real.cos (((399:ℕ):ℝ) * (Real.log n / 2))

theorem psum399o2_11 : ((653897/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 11, cos399o2c k := by
  rw [Finset.Icc_self, Finset.sum_singleton]
  have h : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 11 - ((653937/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_11).1
  push_cast at h ⊢
  linarith

theorem psum399o2_12 : ((730127/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 12, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 12, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 11, cos399o2c k) + cos399o2c 12 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 11) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_11
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 12 - ((806397/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_12).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_13 : ((528687/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 13, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 13, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 12, cos399o2c k) + cos399o2c 13 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 12) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_12
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 13 - ((-931527/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_13).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_14 : ((800359/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 14, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 14, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 13, cos399o2c k) + cos399o2c 14 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 13) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_13
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 14 - ((8491/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_14).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_15 : ((1795529/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 15, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 15, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 14, cos399o2c k) + cos399o2c 15 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 14) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_14
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 15 - ((99521/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_15).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_16 : ((17333/6250 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 16, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 16, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 15, cos399o2c k) + cos399o2c 16 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 15) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_15
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 16 - ((977791/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_16).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_17 : ((233717/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 17, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 17, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 16, cos399o2c k) + cos399o2c 17 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 16) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_16
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 17 - ((120779/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_17).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_18 : ((485727/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 18, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 18, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 17, cos399o2c k) + cos399o2c 18 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 17) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_17
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 18 - ((9149/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_18).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_19 : ((2887713/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 19, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 19, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 18, cos399o2c k) + cos399o2c 19 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 18) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_18
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 19 - ((-998063/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_19).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_20 : ((226381/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 20, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 20, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 19, cos399o2c k) + cos399o2c 20 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 19) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_19
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 20 - ((734423/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_20).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_21 : ((625739/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 21, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 21, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 20, cos399o2c k) + cos399o2c 21 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 20) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_20
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 21 - ((-493361/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_21).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_22 : ((1870881/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 22, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 22, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 21, cos399o2c k) + cos399o2c 22 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 21) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_21
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 22 - ((613107/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_22).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_23 : ((560757/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 23, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 23, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 22, cos399o2c k) + cos399o2c 23 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 22) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_22
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 23 - ((-937937/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_23).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_24 : ((3640223/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 24, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 24, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 23, cos399o2c k) + cos399o2c 24 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 23) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_23
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 24 - ((418239/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_24).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_25 : ((1963051/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 25, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 25, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 24, cos399o2c k) + cos399o2c 25 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 24) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_24
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 25 - ((285919/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_25).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_26 : ((2976643/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 26, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 26, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 25, cos399o2c k) + cos399o2c 26 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 25) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_25
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 26 - ((-949419/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_26).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_27 : ((2376037/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 27, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 27, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 26, cos399o2c k) + cos399o2c 27 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 26) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_26
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 27 - ((-300283/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_27).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_28 : ((2698111/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 28, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 28, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 27, cos399o2c k) + cos399o2c 28 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 27) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_27
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 28 - ((161057/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_28).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_29 : ((1781621/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 29, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 29, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 28, cos399o2c k) + cos399o2c 29 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 28) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_28
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 29 - ((865171/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_29).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_30 : ((4562183/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 30, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 30, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 29, cos399o2c k) + cos399o2c 30 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 29) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_29
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 30 - ((998981/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_30).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_31 : ((553949/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 31, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 31, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 30, cos399o2c k) + cos399o2c 31 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 30) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_30
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 31 - ((977347/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_31).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_32 : ((325241/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 32, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 32, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 31, cos399o2c k) + cos399o2c 32 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 31) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_31
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 32 - ((96537/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_32).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_33 : ((3748813/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 33, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 33, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 32, cos399o2c k) + cos399o2c 33 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 32) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_32
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 33 - ((496423/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_33).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_34 : ((2119017/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 34, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 34, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 33, cos399o2c k) + cos399o2c 34 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 33) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_33
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 34 - ((489241/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_34).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_35 : ((923569/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 35, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 35, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 34, cos399o2c k) + cos399o2c 35 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 34) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_34
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 35 - ((379831/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_35).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_36 : ((9434027/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 36, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 36, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 35, cos399o2c k) + cos399o2c 36 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 35) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_35
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 36 - ((198377/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_36).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_37 : ((2213771/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 37, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 37, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 36, cos399o2c k) + cos399o2c 37 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 36) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_36
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 37 - ((-578903/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_37).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_38 : ((7855089/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 38, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 38, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 37, cos399o2c k) + cos399o2c 38 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 37) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_37
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 38 - ((-199991/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_38).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_39 : ((741087/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 39, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 39, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 38, cos399o2c k) + cos399o2c 39 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 38) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_38
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 39 - ((-444179/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_39).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_40 : ((8108419/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 40, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 40, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 39, cos399o2c k) + cos399o2c 40 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 39) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_39
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 40 - ((697589/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_40).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_41 : ((4478283/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 41, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 41, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 40, cos399o2c k) + cos399o2c 41 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 40) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_40
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 41 - ((848187/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_41).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_42 : ((8509749/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 42, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 42, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 41, cos399o2c k) + cos399o2c 42 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 41) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_41
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 42 - ((-446777/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_42).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_43 : ((304931/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 43, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 43, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 42, cos399o2c k) + cos399o2c 43 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 42) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_42
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 43 - ((-443217/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_43).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_44 : ((2048451/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 44, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 44, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 43, cos399o2c k) + cos399o2c 44 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 43) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_43
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 44 - ((570569/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_44).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_45 : ((1772801/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 45, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 45, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 44, cos399o2c k) + cos399o2c 45 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 44) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_44
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 45 - ((670241/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_45).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_46 : ((7945627/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 46, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 46, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 45, cos399o2c k) + cos399o2c 46 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 45) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_45
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 46 - ((-459169/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_46).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_47 : ((3980267/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 47, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 47, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 46, cos399o2c k) + cos399o2c 47 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 46) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_46
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 47 - ((14947/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_47).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_48 : ((4412361/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 48, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 48, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 47, cos399o2c k) + cos399o2c 48 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 47) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_47
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 48 - ((216057/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_48).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_49 : ((3960983/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 49, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 49, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 48, cos399o2c k) + cos399o2c 49 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 48) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_48
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 49 - ((-225679/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_49).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_50 : ((1631377/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 50, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 50, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 49, cos399o2c k) + cos399o2c 50 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 49) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_49
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 50 - ((234959/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_50).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_51 : ((4349017/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 51, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 51, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 50, cos399o2c k) + cos399o2c 51 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 50) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_50
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 51 - ((541189/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_51).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_52 : ((7733329/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 52, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 52, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 51, cos399o2c k) + cos399o2c 52 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 51) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_51
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 52 - ((-192933/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_52).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_53 : ((2164369/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 53, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 53, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 52, cos399o2c k) + cos399o2c 53 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 52) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_52
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 53 - ((924187/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_53).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_54 : ((1012487/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 54, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 54, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 53, cos399o2c k) + cos399o2c 54 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 53) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_53
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 54 - ((-27877/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_54).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_55 : ((25538/3125 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 55, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 55, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 54, cos399o2c k) + cos399o2c 55 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 54) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_54
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 55 - ((4519/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_55).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_56 : ((8543719/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 56, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 56, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 55, cos399o2c k) + cos399o2c 56 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 55) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_55
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 56 - ((371599/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_56).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_57 : ((3923697/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 57, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 57, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 56, cos399o2c k) + cos399o2c 57 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 56) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_56
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 57 - ((-139257/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_57).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_58 : ((436889/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 58, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 58, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 57, cos399o2c k) + cos399o2c 58 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 57) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_57
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 58 - ((445213/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_58).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_59 : ((7758431/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 59, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 59, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 58, cos399o2c k) + cos399o2c 59 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 58) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_58
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 59 - ((-979309/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_59).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_60 : ((4379181/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 60, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 60, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 59, cos399o2c k) + cos399o2c 60 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 59) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_59
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 60 - ((999971/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_60).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_61 : ((7771683/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 61, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 61, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 60, cos399o2c k) + cos399o2c 61 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 60) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_60
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 61 - ((-986639/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_61).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_62 : ((4368233/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 62, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 62, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 61, cos399o2c k) + cos399o2c 62 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 61) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_61
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 62 - ((964823/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_62).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_63 : ((77861/10000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 63, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 63, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 62, cos399o2c k) + cos399o2c 63 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 62) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_62
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 63 - ((-475163/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_63).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_64 : ((4368163/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 64, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 64, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 63, cos399o2c k) + cos399o2c 64 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 63) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_63
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 64 - ((475133/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_64).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_65 : ((7772037/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 65, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 65, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 64, cos399o2c k) + cos399o2c 65 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 64) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_64
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 65 - ((-964249/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_65).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_66 : ((218929/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 66, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 66, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 65, cos399o2c k) + cos399o2c 66 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 65) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_65
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 66 - ((985163/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_66).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_67 : ((7757599/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 67, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 67, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 66, cos399o2c k) + cos399o2c 67 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 66) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_66
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 67 - ((-999521/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_67).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_68 : ((1749113/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 68, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 68, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 67, cos399o2c k) + cos399o2c 68 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 67) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_67
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 68 - ((494003/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_68).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_69 : ((3909207/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 69, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 69, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 68, cos399o2c k) + cos399o2c 69 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 68) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_68
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 69 - ((-927111/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_69).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_70 : ((2152823/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 70, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 70, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 69, cos399o2c k) + cos399o2c 70 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 69) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_69
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 70 - ((396459/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_70).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_71 : ((8043463/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 71, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 71, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 70, cos399o2c k) + cos399o2c 71 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 70) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_70
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 71 - ((-567789/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_71).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_72 : ((207331/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 72, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 72, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 71, cos399o2c k) + cos399o2c 72 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 71) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_71
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 72 - ((249817/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_72).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_73 : ((8430107/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 73, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 73, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 72, cos399o2c k) + cos399o2c 73 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 72) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_72
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 73 - ((136907/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_73).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_74 : ((3947489/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 74, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 74, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 73, cos399o2c k) + cos399o2c 74 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 73) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_73
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 74 - ((-535089/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_74).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_75 : ((8751359/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 75, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 75, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 74, cos399o2c k) + cos399o2c 75 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 74) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_74
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 75 - ((856421/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_75).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_76 : ((7752257/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 76, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 76, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 75, cos399o2c k) + cos399o2c 76 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 75) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_75
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 76 - ((-499531/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_76).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_77 : ((8634369/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 77, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 77, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 76, cos399o2c k) + cos399o2c 77 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 76) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_76
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 77 - ((110269/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_77).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_78 : ((1628699/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 78, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 78, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 77, cos399o2c k) + cos399o2c 78 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 77) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_77
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 78 - ((-245417/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_78).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_79 : ((161129/20000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 79, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 79, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 78, cos399o2c k) + cos399o2c 79 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 78) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_78
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 79 - ((-17401/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_79).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_80 : ((8715221/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 80, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 80, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 79, cos399o2c k) + cos399o2c 80 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 79) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_79
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 80 - ((658811/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_80).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_81 : ((7732849/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 81, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 81, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 80, cos399o2c k) + cos399o2c 81 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 80) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_80
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 81 - ((-245583/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_81).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_82 : ((2151941/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 82, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 82, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 81, cos399o2c k) + cos399o2c 82 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 81) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_81
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 82 - ((174991/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_82).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_83 : ((413619/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 83, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 83, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 82, cos399o2c k) + cos399o2c 83 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 82) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_82
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 83 - ((-20959/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_83).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_84 : ((3936691/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 84, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 84, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 83, cos399o2c k) + cos399o2c 84 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 83) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_83
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 84 - ((-199479/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_84).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_85 : ((4401041/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 85, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 85, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 84, cos399o2c k) + cos399o2c 85 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 84) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_84
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 85 - ((46437/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_85).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_86 : ((7892429/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 86, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 86, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 85, cos399o2c k) + cos399o2c 86 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 85) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_85
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 86 - ((-909613/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_86).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_87 : ((8194741/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 87, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 87, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 86, cos399o2c k) + cos399o2c 87 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 86) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_86
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 87 - ((18897/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_87).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_88 : ((8721141/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 88, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 88, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 87, cos399o2c k) + cos399o2c 88 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 87) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_87
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 88 - ((13161/25000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_88).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_89 : ((966177/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 89, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 89, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 88, cos399o2c k) + cos399o2c 89 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 88) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_88
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 89 - ((-198337/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_89).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_90 : ((4218921/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 90, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 90, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 89, cos399o2c k) + cos399o2c 90 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 89) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_89
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 90 - ((354233/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_90).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_91 : ((8587067/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 91, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 91, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 90, cos399o2c k) + cos399o2c 91 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 90) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_90
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 91 - ((29853/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_91).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_92 : ((1922713/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 92, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 92, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 91, cos399o2c k) + cos399o2c 92 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 91) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_91
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 92 - ((-35847/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_92).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_93 : ((8556089/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 93, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 93, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 92, cos399o2c k) + cos399o2c 93 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 92) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_92
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 93 - ((865277/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_93).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_94 : ((2129559/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 94, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 94, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 93, cos399o2c k) + cos399o2c 94 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 93) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_93
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 94 - ((-37813/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_94).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_95 : ((7680723/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 95, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 95, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 94, cos399o2c k) + cos399o2c 95 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 94) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_94
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 95 - ((-837473/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_95).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_96 : ((2142561/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 96, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 96, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 95, cos399o2c k) + cos399o2c 96 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 95) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_95
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 96 - ((889561/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_96).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_97 : ((8548037/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 97, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 97, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 96, cos399o2c k) + cos399o2c 97 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 96) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_96
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 97 - ((-22167/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_97).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_98 : ((191731/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 98, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 98, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 97, cos399o2c k) + cos399o2c 98 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 97) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_97
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 98 - ((-878757/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_98).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_99 : ((1696773/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 99, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 99, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 98, cos399o2c k) + cos399o2c 99 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 98) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_98
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 99 - ((162933/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_99).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_100 : ((2166797/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 100, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 100, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 99, cos399o2c k) + cos399o2c 100 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 99) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_99
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 100 - ((183363/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_100).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_101 : ((7693459/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 101, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 101, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 100, cos399o2c k) + cos399o2c 101 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 100) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_100
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 101 - ((-973689/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_101).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_102 : ((517389/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 102, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 102, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 101, cos399o2c k) + cos399o2c 102 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 101) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_101
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 102 - ((116961/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_102).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_103 : ((881833/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 103, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 103, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 102, cos399o2c k) + cos399o2c 103 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 102) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_102
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 103 - ((270073/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_103).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_104 : ((7841071/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 104, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 104, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 103, cos399o2c k) + cos399o2c 104 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 103) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_103
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 104 - ((-977219/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_104).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_105 : ((7965171/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 105, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 105, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 104, cos399o2c k) + cos399o2c 105 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 104) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_104
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 105 - ((6207/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_105).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_106 : ((4433943/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 106, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 106, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 105, cos399o2c k) + cos399o2c 106 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 105) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_105
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 106 - ((180551/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_106).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_107 : ((8188307/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 107, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 107, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 106, cos399o2c k) + cos399o2c 107 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 106) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_106
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 107 - ((-679539/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_107).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_108 : ((3837653/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 108, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 108, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 107, cos399o2c k) + cos399o2c 108 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 107) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_107
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 108 - ((-512961/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_108).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_109 : ((4319423/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 109, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 109, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 108, cos399o2c k) + cos399o2c 109 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 108) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_108
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 109 - ((48179/50000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_109).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_110 : ((4329191/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 110, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 110, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 109, cos399o2c k) + cos399o2c 110 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 109) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_109
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 110 - ((2447/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_110).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_111 : ((7681383/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 111, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 111, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 110, cos399o2c k) + cos399o2c 111 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 110) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_110
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 111 - ((-976959/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_111).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_112 : ((8101411/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 112, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 112, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 111, cos399o2c k) + cos399o2c 112 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 111) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_111
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 112 - ((105017/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_112).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_113 : ((4452901/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 113, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 113, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 112, cos399o2c k) + cos399o2c 113 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 112) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_112
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 113 - ((804431/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_113).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_114 : ((4086287/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 114, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 114, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 113, cos399o2c k) + cos399o2c 114 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 113) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_113
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 114 - ((-183297/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_114).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_115 : ((305107/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 115, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 115, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 114, cos399o2c k) + cos399o2c 115 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 114) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_114
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 115 - ((-544859/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_115).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_116 : ((8540827/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 116, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 116, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 115, cos399o2c k) + cos399o2c 116 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 115) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_115
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 116 - ((114149/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_116).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_117 : ((2203823/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 117, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 117, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 116, cos399o2c k) + cos399o2c 117 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 116) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_116
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 117 - ((54901/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_117).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_118 : ((7826629/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 118, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 118, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 117, cos399o2c k) + cos399o2c 118 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 117) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_117
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 118 - ((-988623/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_118).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_119 : ((1947089/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 119, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 119, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 118, cos399o2c k) + cos399o2c 119 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 118) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_118
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 119 - ((-38233/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_119).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_120 : ((878649/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 120, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 120, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 119, cos399o2c k) + cos399o2c 120 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 119) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_119
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 120 - ((499087/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_120).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_121 : ((8641709/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 121, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 121, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 120, cos399o2c k) + cos399o2c 121 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 120) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_120
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 121 - ((-144741/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_121).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_122 : ((7665001/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 122, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 122, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 121, cos399o2c k) + cos399o2c 122 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 121) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_121
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 122 - ((-244167/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_122).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_123 : ((7935759/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 123, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 123, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 122, cos399o2c k) + cos399o2c 123 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 122) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_122
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 123 - ((135399/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_123).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_124 : ((4442663/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 124, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 124, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 123, cos399o2c k) + cos399o2c 124 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 123) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_123
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 124 - ((949607/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_124).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_125 : ((854197/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 125, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 125, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 124, cos399o2c k) + cos399o2c 125 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 124) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_124
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 125 - ((-85829/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_125).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_126 : ((7609351/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 126, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 126, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 125, cos399o2c k) + cos399o2c 126 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 125) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_125
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 126 - ((-932579/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_126).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_127 : ((7976119/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 127, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 127, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 126, cos399o2c k) + cos399o2c 127 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 126) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_126
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 127 - ((45851/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_127).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_128 : ((2227147/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 128, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 128, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 127, cos399o2c k) + cos399o2c 128 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 127) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_127
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 128 - ((932509/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_128).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_129 : ((2141119/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 129, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 129, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 128, cos399o2c k) + cos399o2c 129 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 128) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_128
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 129 - ((-43009/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_129).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_130 : ((7615513/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 130, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 130, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 129, cos399o2c k) + cos399o2c 130 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 129) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_129
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 130 - ((-948923/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_130).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_131 : ((1578163/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 131, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 131, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 130, cos399o2c k) + cos399o2c 131 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 130) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_130
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 131 - ((137671/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_131).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_132 : ((886551/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 132, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 132, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 131, cos399o2c k) + cos399o2c 132 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 131) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_131
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 132 - ((194947/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_132).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_133 : ((8706017/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 133, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 133, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 132, cos399o2c k) + cos399o2c 133 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 132) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_132
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 133 - ((-159453/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_133).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_134 : ((192737/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 134, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 134, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 133, cos399o2c k) + cos399o2c 134 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 133) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_133
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 134 - ((-996497/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_134).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_135 : ((7705641/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 135, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 135, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 134, cos399o2c k) + cos399o2c 135 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 134) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_134
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 135 - ((-3799/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_135).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_136 : ((1087547/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 136, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 136, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 135, cos399o2c k) + cos399o2c 136 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 135) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_135
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 136 - ((39791/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_136).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_137 : ((8910267/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 137, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 137, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 136, cos399o2c k) + cos399o2c 137 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 136) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_136
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 137 - ((209931/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_137).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_138 : ((3982319/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 138, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 138, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 137, cos399o2c k) + cos399o2c 138 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 137) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_137
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 138 - ((-945589/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_138).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_139 : ((469943/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 139, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 139, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 138, cos399o2c k) + cos399o2c 139 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 138) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_138
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 139 - ((-44551/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_139).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_140 : ((2085753/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 140, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 140, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 139, cos399o2c k) + cos399o2c 140 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 139) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_139
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 140 - ((205991/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_140).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_141 : ((9027021/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 141, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 141, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 140, cos399o2c k) + cos399o2c 141 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 140) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_140
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 141 - ((684049/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_141).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_142 : ((2104137/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 142, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 142, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 141, cos399o2c k) + cos399o2c 142 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 141) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_141
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 142 - ((-610433/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_142).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_143 : ((7532217/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 143, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 143, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 142, cos399o2c k) + cos399o2c 143 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 142) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_142
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 143 - ((-884291/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_143).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_144 : ((7832719/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 144, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 144, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 143, cos399o2c k) + cos399o2c 144 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 143) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_143
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 144 - ((150271/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_144).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_145 : ((4413031/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 145, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 145, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 144, cos399o2c k) + cos399o2c 145 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 144) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_144
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 145 - ((993383/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_145).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_146 : ((891047/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 146, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 146, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 145, cos399o2c k) + cos399o2c 146 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 145) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_145
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 146 - ((2639/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_146).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_147 : ((1590643/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 147, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 147, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 146, cos399o2c k) + cos399o2c 147 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 146) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_146
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 147 - ((-191443/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_147).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_148 : ((7463407/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 148, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 148, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 147, cos399o2c k) + cos399o2c 148 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 147) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_147
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 148 - ((-61221/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_148).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_149 : ((8202397/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 149, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 149, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 148, cos399o2c k) + cos399o2c 149 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 148) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_148
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 149 - ((73903/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_149).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_150 : ((1806071/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 150, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 150, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 149, cos399o2c k) + cos399o2c 150 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 149) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_149
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 150 - ((413999/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_150).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_151 : ((8687351/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 151, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 151, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 150, cos399o2c k) + cos399o2c 151 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 150) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_150
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 151 - ((-85741/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_151).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_152 : ((3845963/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 152, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 152, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 151, cos399o2c k) + cos399o2c 152 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 151) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_151
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 152 - ((-199077/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_152).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_153 : ((1881543/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 153, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 153, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 152, cos399o2c k) + cos399o2c 153 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 152) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_152
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 153 - ((-82857/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_153).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_154 : ((1686381/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 154, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 154, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 153, cos399o2c k) + cos399o2c 154 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 153) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_153
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 154 - ((905773/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_154).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_155 : ((142017/15625 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 155, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 155, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 154, cos399o2c k) + cos399o2c 155 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 154) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_154
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 155 - ((657223/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_155).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_156 : ((4276463/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 156, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 156, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 155, cos399o2c k) + cos399o2c 156 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 155) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_155
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 156 - ((-268061/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_156).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_157 : ((7589063/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 157, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 157, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 156, cos399o2c k) + cos399o2c 157 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 156) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_156
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 157 - ((-963823/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_157).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_158 : ((472169/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 158, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 158, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 157, cos399o2c k) + cos399o2c 158 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 157) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_157
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 158 - ((-34319/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_158).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_159 : ((8495253/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 159, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 159, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 158, cos399o2c k) + cos399o2c 159 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 158) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_158
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 159 - ((940589/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_159).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_160 : ((9113411/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 160, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 160, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 159, cos399o2c k) + cos399o2c 160 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 159) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_159
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 160 - ((309099/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_160).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_161 : ((8568247/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 161, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 161, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 160, cos399o2c k) + cos399o2c 161 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 160) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_160
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 161 - ((-136281/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_161).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_162 : ((3798559/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 162, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 162, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 161, cos399o2c k) + cos399o2c 162 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 161) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_161
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 162 - ((-971089/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_162).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_163 : ((7495207/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 163, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 163, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 162, cos399o2c k) + cos399o2c 163 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 162) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_162
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 163 - ((-101871/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_163).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_164 : ((8394453/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 164, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 164, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 163, cos399o2c k) + cos399o2c 164 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 163) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_163
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 164 - ((449643/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_164).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_165 : ((4559591/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 165, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 165, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 164, cos399o2c k) + cos399o2c 165 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 164) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_164
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 165 - ((724769/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_165).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_166 : ((4367287/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 166, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 166, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 165, cos399o2c k) + cos399o2c 166 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 165) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_165
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 166 - ((-48071/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_166).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_167 : ((386739/50000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 167, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 167, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 166, cos399o2c k) + cos399o2c 167 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 166) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_166
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 167 - ((-499877/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_167).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_168 : ((923089/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 168, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 168, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 167, cos399o2c k) + cos399o2c 168 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 167) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_167
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 168 - ((-87507/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_168).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_169 : ((2030041/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 169, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 169, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 168, cos399o2c k) + cos399o2c 169 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 168) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_168
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 169 - ((183873/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_169).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_170 : ((9028009/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 170, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 170, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 169, cos399o2c k) + cos399o2c 170 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 169) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_169
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 170 - ((181577/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_170).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_171 : ((4498049/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 171, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 171, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 170, cos399o2c k) + cos399o2c 171 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 170) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_170
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 171 - ((-31871/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_171).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_172 : ((8065791/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 172, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 172, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 171, cos399o2c k) + cos399o2c 172 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 171) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_171
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 172 - ((-930267/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_172).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_173 : ((7355447/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 173, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 173, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 172, cos399o2c k) + cos399o2c 173 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 172) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_172
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 173 - ((-22197/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_173).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_174 : ((3853807/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 174, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 174, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 173, cos399o2c k) + cos399o2c 174 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 173) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_173
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 174 - ((352207/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_174).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_175 : ((870529/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 175, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 175, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 174, cos399o2c k) + cos399o2c 175 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 174) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_174
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 175 - ((249429/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_175).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_176 : ((9186113/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 176, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 176, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 175, cos399o2c k) + cos399o2c 176 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 175) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_175
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 176 - ((480863/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_176).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_177 : ((2149497/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 177, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 177, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 176, cos399o2c k) + cos399o2c 177 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 176) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_176
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 177 - ((-117617/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_177).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_178 : ((3807217/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 178, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 178, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 177, cos399o2c k) + cos399o2c 178 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 177) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_177
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 178 - ((-491757/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_178).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_179 : ((918301/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 179, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 179, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 178, cos399o2c k) + cos399o2c 179 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 178) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_178
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 179 - ((-133993/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_179).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_180 : ((4045543/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 180, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 180, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 179, cos399o2c k) + cos399o2c 180 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 179) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_179
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 180 - ((372359/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_180).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_181 : ((1804341/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 181, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 181, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 180, cos399o2c k) + cos399o2c 181 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 180) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_180
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 181 - ((930659/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_181).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_182 : ((4559279/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 182, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 182, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 181, cos399o2c k) + cos399o2c 182 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 181) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_181
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 182 - ((96893/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_182).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_183 : ((8279153/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 183, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 183, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 182, cos399o2c k) + cos399o2c 183 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 182) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_182
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 183 - ((-167873/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_183).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_184 : ((3703799/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 184, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 184, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 183, cos399o2c k) + cos399o2c 184 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 183) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_183
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 184 - ((-174303/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_184).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_185 : ((7430583/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 185, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 185, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 184, cos399o2c k) + cos399o2c 185 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 184) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_184
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 185 - ((921/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_185).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_186 : ((1664213/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 186, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 186, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 185, cos399o2c k) + cos399o2c 186 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 185) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_185
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 186 - ((445261/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_186).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_187 : ((4573909/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 187, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 187, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 186, cos399o2c k) + cos399o2c 187 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 186) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_186
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 187 - ((826793/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_187).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_188 : ((905729/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 188, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 188, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 187, cos399o2c k) + cos399o2c 188 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 187) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_187
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 188 - ((-11311/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_188).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_189 : ((8144903/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 189, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 189, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 188, cos399o2c k) + cos399o2c 189 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 188) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_188
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 189 - ((-912347/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_189).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_190 : ((458587/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 190, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 190, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 189, cos399o2c k) + cos399o2c 190 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 189) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_189
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 190 - ((-807471/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_190).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_191 : ((7444549/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 191, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 191, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 190, cos399o2c k) + cos399o2c 191 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 190) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_190
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 191 - ((107197/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_191).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_192 : ((1671387/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 192, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 192, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 191, cos399o2c k) + cos399o2c 192 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 191) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_191
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 192 - ((456213/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_192).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_193 : ((9173819/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 193, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 193, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 192, cos399o2c k) + cos399o2c 193 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 192) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_192
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 193 - ((204231/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_193).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_194 : ((9098891/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 194, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 194, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 193, cos399o2c k) + cos399o2c 194 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 193) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_193
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 194 - ((-9361/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_194).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_195 : ((8207341/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 195, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 195, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 194, cos399o2c k) + cos399o2c 195 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 194) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_194
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 195 - ((-89151/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_195).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_196 : ((7354951/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 196, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 196, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 195, cos399o2c k) + cos399o2c 196 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 195) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_195
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 196 - ((-17047/20000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_196).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_197 : ((1837431/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 197, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 197, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 196, cos399o2c k) + cos399o2c 197 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 196) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_196
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 197 - ((-5187/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_197).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_198 : ((4096907/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 198, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 198, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 197, cos399o2c k) + cos399o2c 198 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 197) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_197
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 198 - ((84413/100000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_198).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_199 : ((1137359/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 199, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 199, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 198, cos399o2c k) + cos399o2c 199 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 198) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_198
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 199 - ((452549/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_199).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_200 : ((9230069/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 200, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 200, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 199, cos399o2c k) + cos399o2c 200 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 199) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_199
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 200 - ((131237/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_200).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_201 : ((4234983/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 201, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 201, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 200, cos399o2c k) + cos399o2c 201 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 200) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_200
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 201 - ((-760063/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_201).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_202 : ((1877403/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 202, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 202, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 201, cos399o2c k) + cos399o2c 202 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 201) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_201
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 202 - ((-480157/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_202).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_203 : ((5769/800 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 203, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 203, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 202, cos399o2c k) + cos399o2c 203 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 202) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_202
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 203 - ((-149161/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_203).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_204 : ((7837987/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 204, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 204, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 203, cos399o2c k) + cos399o2c 204 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 203) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_203
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 204 - ((626777/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_204).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_205 : ((8834573/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 205, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 205, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 204, cos399o2c k) + cos399o2c 205 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 204) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_204
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 205 - ((498313/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_205).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_206 : ((9329521/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 206, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 206, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 205, cos399o2c k) + cos399o2c 206 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 205) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_205
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 206 - ((123747/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_206).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_207 : ((8896067/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 207, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 207, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 206, cos399o2c k) + cos399o2c 207 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 206) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_206
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 207 - ((-216707/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_207).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_208 : ((7908971/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 208, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 208, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 207, cos399o2c k) + cos399o2c 208 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 207) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_207
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 208 - ((-61691/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_208).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_209 : ((7209199/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 209, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 209, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 208, cos399o2c k) + cos399o2c 209 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 208) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_208
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 209 - ((-174933/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_209).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_210 : ((7385483/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 210, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 210, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 209, cos399o2c k) + cos399o2c 210 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 209) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_209
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 210 - ((44081/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_210).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_211 : ((2071927/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 211, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 211, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 210, cos399o2c k) + cos399o2c 211 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 210) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_210
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 211 - ((180453/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_211).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_212 : ((2291617/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 212, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 212, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 211, cos399o2c k) + cos399o2c 212 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 211) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_211
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 212 - ((2197/2500 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_212).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_213 : ((9300537/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 213, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 213, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 212, cos399o2c k) + cos399o2c 213 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 212) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_212
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 213 - ((134109/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_213).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_214 : ((4291597/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 214, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 214, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 213, cos399o2c k) + cos399o2c 214 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 213) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_213
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 214 - ((-717303/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_214).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_215 : ((7595799/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 215, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 215, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 214, cos399o2c k) + cos399o2c 215 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 214) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_214
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 215 - ((-197471/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_215).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_216 : ((7128807/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 216, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 216, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 215, cos399o2c k) + cos399o2c 216 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 215) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_215
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 216 - ((-58369/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_216).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_217 : ((7550749/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 217, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 217, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 216, cos399o2c k) + cos399o2c 217 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 216) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_216
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 217 - ((210991/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_217).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_218 : ((8527057/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 218, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 218, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 217, cos399o2c k) + cos399o2c 218 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 217) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_217
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 218 - ((244087/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_218).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_219 : ((929499/100000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 219, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 219, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 218, cos399o2c k) + cos399o2c 219 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 218) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_218
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 219 - ((767973/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_219).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_220 : ((578859/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 220, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 220, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 219, cos399o2c k) + cos399o2c 220 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 219) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_219
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 220 - ((-16603/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_220).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_221 : ((1056917/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 221, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 221, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 220, cos399o2c k) + cos399o2c 221 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 220) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_220
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 221 - ((-25199/31250 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_221).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_222 : ((3745477/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 222, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 222, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 221, cos399o2c k) + cos399o2c 222 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 221) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_221
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 222 - ((-482171/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_222).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_223 : ((7095689/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 223, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 223, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 222, cos399o2c k) + cos399o2c 223 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 222) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_222
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 223 - ((-15809/40000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_223).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_224 : ((945377/125000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 224, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 224, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 223, cos399o2c k) + cos399o2c 224 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 223) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_223
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 224 - ((467367/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_224).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_225 : ((4271931/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 225, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 225, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 224, cos399o2c k) + cos399o2c 225 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 224) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_224
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 225 - ((490443/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_225).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_226 : ((9315793/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 226, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 226, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 225, cos399o2c k) + cos399o2c 226 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 225) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_225
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 226 - ((771971/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_226).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_227 : ((9316887/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 227, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 227, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 226, cos399o2c k) + cos399o2c 227 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 226) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_226
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 227 - ((567/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_227).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_228 : ((8548799/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 228, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 228, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 227, cos399o2c k) + cos399o2c 228 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 227) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_227
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 228 - ((-48003/62500 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_228).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_229 : ((3782287/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 229, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 229, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 228, cos399o2c k) + cos399o2c 229 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 228) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_228
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 229 - ((-196837/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_229).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_230 : ((7064679/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 230, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 230, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 229, cos399o2c k) + cos399o2c 230 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 229) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_229
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 230 - ((-99971/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_230).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_231 : ((1480017/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 231, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 231, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 230, cos399o2c k) + cos399o2c 231 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 230) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_230
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 231 - ((167723/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_231).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_232 : ((2083367/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 232, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 232, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 231, cos399o2c k) + cos399o2c 232 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 231) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_231
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 232 - ((933423/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_232).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_233 : ((9215237/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 233, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 233, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 232, cos399o2c k) + cos399o2c 233 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 232) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_232
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 233 - ((881809/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_233).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_234 : ((9438581/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 234, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 234, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 233, cos399o2c k) + cos399o2c 234 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 233) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_233
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 234 - ((27923/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_234).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_235 : ((2213267/250000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 235, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 235, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 234, cos399o2c k) + cos399o2c 235 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 234) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_234
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 235 - ((-585473/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_235).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_236 : ((1571569/200000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 236, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 236, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 235, cos399o2c k) + cos399o2c 236 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 235) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_235
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 236 - ((-995183/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_236).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_237 : ((3561477/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 237, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 237, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 236, cos399o2c k) + cos399o2c 237 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 236) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_236
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 237 - ((-734851/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_237).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_238 : ((7137461/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 238, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 238, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 237, cos399o2c k) + cos399o2c 238 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 237) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_237
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 238 - ((14547/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_238).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_239 : ((3944691/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 239, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 239, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 238, cos399o2c k) + cos399o2c 239 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 238) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_238
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 239 - ((751961/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_239).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_240 : ((8882939/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 240, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 240, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 239, cos399o2c k) + cos399o2c 240 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 239) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_239
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 240 - ((993597/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_240).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_241 : ((4735233/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 241, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 241, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 240, cos399o2c k) + cos399o2c 241 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 240) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_240
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 241 - ((587567/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_241).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_242 : ((9273677/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 242, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 242, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 241, cos399o2c k) + cos399o2c 242 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 241) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_241
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 242 - ((-196749/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_242).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_243 : ((8421153/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 243, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 243, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 242, cos399o2c k) + cos399o2c 243 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 242) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_242
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 243 - ((-213121/250000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_243).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_244 : ((7457137/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 244, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 244, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 243, cos399o2c k) + cos399o2c 244 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 243) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_243
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 244 - ((-120497/125000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_244).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_245 : ((6990339/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 245, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 245, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 244, cos399o2c k) + cos399o2c 245 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 244) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_244
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 245 - ((-233379/500000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_245).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_246 : ((3655757/500000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 246, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 246, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 245, cos399o2c k) + cos399o2c 246 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 245) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_245
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 246 - ((64243/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_246).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_247 : ((328743/40000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 247, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 247, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 246, cos399o2c k) + cos399o2c 247 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 246) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_246
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 247 - ((907101/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_247).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_248 : ((228757/25000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 248, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 248, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 247, cos399o2c k) + cos399o2c 248 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 247) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_247
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 248 - ((186349/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_248).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_249 : ((9536323/1000000 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 249, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 249, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 248, cos399o2c k) + cos399o2c 249 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 248) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_248
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 249 - ((386083/1000000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_249).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

theorem psum399o2_250 : ((571493/62500 : ℚ) : ℝ)
    ≤ ∑ k ∈ Finset.Icc 11 250, cos399o2c k := by
  have hsplit : (∑ k ∈ Finset.Icc 11 250, cos399o2c k)
      = (∑ k ∈ Finset.Icc 11 249, cos399o2c k) + cos399o2c 250 := by
    have h := Finset.sum_Icc_succ_top
      (a := 11) (b := 249) (by norm_num) cos399o2c
    simpa using h
  have hprev := psum399o2_249
  have hstep : -((1/25000 : ℚ) : ℝ) ≤ cos399o2c 250 - ((-78479/200000 : ℚ) : ℝ) :=
    (abs_le.mp cos399o2_br_250).1
  rw [hsplit]
  push_cast at hprev hstep ⊢
  linarith

set_option maxHeartbeats 3200000 in
/-- **The Abel floor at `t = 399/2`.** -/
theorem psum399o2_floor : ∀ j : ℕ, 11 ≤ j → j ≤ 250 →
    ((0 : ℚ) : ℝ) ≤ ∑ k ∈ Finset.Icc 11 j, cos399o2c k := by
  intro j hj1 hj2
  interval_cases j
  · exact le_trans (by norm_num) psum399o2_11
  · exact le_trans (by norm_num) psum399o2_12
  · exact le_trans (by norm_num) psum399o2_13
  · exact le_trans (by norm_num) psum399o2_14
  · exact le_trans (by norm_num) psum399o2_15
  · exact le_trans (by norm_num) psum399o2_16
  · exact le_trans (by norm_num) psum399o2_17
  · exact le_trans (by norm_num) psum399o2_18
  · exact le_trans (by norm_num) psum399o2_19
  · exact le_trans (by norm_num) psum399o2_20
  · exact le_trans (by norm_num) psum399o2_21
  · exact le_trans (by norm_num) psum399o2_22
  · exact le_trans (by norm_num) psum399o2_23
  · exact le_trans (by norm_num) psum399o2_24
  · exact le_trans (by norm_num) psum399o2_25
  · exact le_trans (by norm_num) psum399o2_26
  · exact le_trans (by norm_num) psum399o2_27
  · exact le_trans (by norm_num) psum399o2_28
  · exact le_trans (by norm_num) psum399o2_29
  · exact le_trans (by norm_num) psum399o2_30
  · exact le_trans (by norm_num) psum399o2_31
  · exact le_trans (by norm_num) psum399o2_32
  · exact le_trans (by norm_num) psum399o2_33
  · exact le_trans (by norm_num) psum399o2_34
  · exact le_trans (by norm_num) psum399o2_35
  · exact le_trans (by norm_num) psum399o2_36
  · exact le_trans (by norm_num) psum399o2_37
  · exact le_trans (by norm_num) psum399o2_38
  · exact le_trans (by norm_num) psum399o2_39
  · exact le_trans (by norm_num) psum399o2_40
  · exact le_trans (by norm_num) psum399o2_41
  · exact le_trans (by norm_num) psum399o2_42
  · exact le_trans (by norm_num) psum399o2_43
  · exact le_trans (by norm_num) psum399o2_44
  · exact le_trans (by norm_num) psum399o2_45
  · exact le_trans (by norm_num) psum399o2_46
  · exact le_trans (by norm_num) psum399o2_47
  · exact le_trans (by norm_num) psum399o2_48
  · exact le_trans (by norm_num) psum399o2_49
  · exact le_trans (by norm_num) psum399o2_50
  · exact le_trans (by norm_num) psum399o2_51
  · exact le_trans (by norm_num) psum399o2_52
  · exact le_trans (by norm_num) psum399o2_53
  · exact le_trans (by norm_num) psum399o2_54
  · exact le_trans (by norm_num) psum399o2_55
  · exact le_trans (by norm_num) psum399o2_56
  · exact le_trans (by norm_num) psum399o2_57
  · exact le_trans (by norm_num) psum399o2_58
  · exact le_trans (by norm_num) psum399o2_59
  · exact le_trans (by norm_num) psum399o2_60
  · exact le_trans (by norm_num) psum399o2_61
  · exact le_trans (by norm_num) psum399o2_62
  · exact le_trans (by norm_num) psum399o2_63
  · exact le_trans (by norm_num) psum399o2_64
  · exact le_trans (by norm_num) psum399o2_65
  · exact le_trans (by norm_num) psum399o2_66
  · exact le_trans (by norm_num) psum399o2_67
  · exact le_trans (by norm_num) psum399o2_68
  · exact le_trans (by norm_num) psum399o2_69
  · exact le_trans (by norm_num) psum399o2_70
  · exact le_trans (by norm_num) psum399o2_71
  · exact le_trans (by norm_num) psum399o2_72
  · exact le_trans (by norm_num) psum399o2_73
  · exact le_trans (by norm_num) psum399o2_74
  · exact le_trans (by norm_num) psum399o2_75
  · exact le_trans (by norm_num) psum399o2_76
  · exact le_trans (by norm_num) psum399o2_77
  · exact le_trans (by norm_num) psum399o2_78
  · exact le_trans (by norm_num) psum399o2_79
  · exact le_trans (by norm_num) psum399o2_80
  · exact le_trans (by norm_num) psum399o2_81
  · exact le_trans (by norm_num) psum399o2_82
  · exact le_trans (by norm_num) psum399o2_83
  · exact le_trans (by norm_num) psum399o2_84
  · exact le_trans (by norm_num) psum399o2_85
  · exact le_trans (by norm_num) psum399o2_86
  · exact le_trans (by norm_num) psum399o2_87
  · exact le_trans (by norm_num) psum399o2_88
  · exact le_trans (by norm_num) psum399o2_89
  · exact le_trans (by norm_num) psum399o2_90
  · exact le_trans (by norm_num) psum399o2_91
  · exact le_trans (by norm_num) psum399o2_92
  · exact le_trans (by norm_num) psum399o2_93
  · exact le_trans (by norm_num) psum399o2_94
  · exact le_trans (by norm_num) psum399o2_95
  · exact le_trans (by norm_num) psum399o2_96
  · exact le_trans (by norm_num) psum399o2_97
  · exact le_trans (by norm_num) psum399o2_98
  · exact le_trans (by norm_num) psum399o2_99
  · exact le_trans (by norm_num) psum399o2_100
  · exact le_trans (by norm_num) psum399o2_101
  · exact le_trans (by norm_num) psum399o2_102
  · exact le_trans (by norm_num) psum399o2_103
  · exact le_trans (by norm_num) psum399o2_104
  · exact le_trans (by norm_num) psum399o2_105
  · exact le_trans (by norm_num) psum399o2_106
  · exact le_trans (by norm_num) psum399o2_107
  · exact le_trans (by norm_num) psum399o2_108
  · exact le_trans (by norm_num) psum399o2_109
  · exact le_trans (by norm_num) psum399o2_110
  · exact le_trans (by norm_num) psum399o2_111
  · exact le_trans (by norm_num) psum399o2_112
  · exact le_trans (by norm_num) psum399o2_113
  · exact le_trans (by norm_num) psum399o2_114
  · exact le_trans (by norm_num) psum399o2_115
  · exact le_trans (by norm_num) psum399o2_116
  · exact le_trans (by norm_num) psum399o2_117
  · exact le_trans (by norm_num) psum399o2_118
  · exact le_trans (by norm_num) psum399o2_119
  · exact le_trans (by norm_num) psum399o2_120
  · exact le_trans (by norm_num) psum399o2_121
  · exact le_trans (by norm_num) psum399o2_122
  · exact le_trans (by norm_num) psum399o2_123
  · exact le_trans (by norm_num) psum399o2_124
  · exact le_trans (by norm_num) psum399o2_125
  · exact le_trans (by norm_num) psum399o2_126
  · exact le_trans (by norm_num) psum399o2_127
  · exact le_trans (by norm_num) psum399o2_128
  · exact le_trans (by norm_num) psum399o2_129
  · exact le_trans (by norm_num) psum399o2_130
  · exact le_trans (by norm_num) psum399o2_131
  · exact le_trans (by norm_num) psum399o2_132
  · exact le_trans (by norm_num) psum399o2_133
  · exact le_trans (by norm_num) psum399o2_134
  · exact le_trans (by norm_num) psum399o2_135
  · exact le_trans (by norm_num) psum399o2_136
  · exact le_trans (by norm_num) psum399o2_137
  · exact le_trans (by norm_num) psum399o2_138
  · exact le_trans (by norm_num) psum399o2_139
  · exact le_trans (by norm_num) psum399o2_140
  · exact le_trans (by norm_num) psum399o2_141
  · exact le_trans (by norm_num) psum399o2_142
  · exact le_trans (by norm_num) psum399o2_143
  · exact le_trans (by norm_num) psum399o2_144
  · exact le_trans (by norm_num) psum399o2_145
  · exact le_trans (by norm_num) psum399o2_146
  · exact le_trans (by norm_num) psum399o2_147
  · exact le_trans (by norm_num) psum399o2_148
  · exact le_trans (by norm_num) psum399o2_149
  · exact le_trans (by norm_num) psum399o2_150
  · exact le_trans (by norm_num) psum399o2_151
  · exact le_trans (by norm_num) psum399o2_152
  · exact le_trans (by norm_num) psum399o2_153
  · exact le_trans (by norm_num) psum399o2_154
  · exact le_trans (by norm_num) psum399o2_155
  · exact le_trans (by norm_num) psum399o2_156
  · exact le_trans (by norm_num) psum399o2_157
  · exact le_trans (by norm_num) psum399o2_158
  · exact le_trans (by norm_num) psum399o2_159
  · exact le_trans (by norm_num) psum399o2_160
  · exact le_trans (by norm_num) psum399o2_161
  · exact le_trans (by norm_num) psum399o2_162
  · exact le_trans (by norm_num) psum399o2_163
  · exact le_trans (by norm_num) psum399o2_164
  · exact le_trans (by norm_num) psum399o2_165
  · exact le_trans (by norm_num) psum399o2_166
  · exact le_trans (by norm_num) psum399o2_167
  · exact le_trans (by norm_num) psum399o2_168
  · exact le_trans (by norm_num) psum399o2_169
  · exact le_trans (by norm_num) psum399o2_170
  · exact le_trans (by norm_num) psum399o2_171
  · exact le_trans (by norm_num) psum399o2_172
  · exact le_trans (by norm_num) psum399o2_173
  · exact le_trans (by norm_num) psum399o2_174
  · exact le_trans (by norm_num) psum399o2_175
  · exact le_trans (by norm_num) psum399o2_176
  · exact le_trans (by norm_num) psum399o2_177
  · exact le_trans (by norm_num) psum399o2_178
  · exact le_trans (by norm_num) psum399o2_179
  · exact le_trans (by norm_num) psum399o2_180
  · exact le_trans (by norm_num) psum399o2_181
  · exact le_trans (by norm_num) psum399o2_182
  · exact le_trans (by norm_num) psum399o2_183
  · exact le_trans (by norm_num) psum399o2_184
  · exact le_trans (by norm_num) psum399o2_185
  · exact le_trans (by norm_num) psum399o2_186
  · exact le_trans (by norm_num) psum399o2_187
  · exact le_trans (by norm_num) psum399o2_188
  · exact le_trans (by norm_num) psum399o2_189
  · exact le_trans (by norm_num) psum399o2_190
  · exact le_trans (by norm_num) psum399o2_191
  · exact le_trans (by norm_num) psum399o2_192
  · exact le_trans (by norm_num) psum399o2_193
  · exact le_trans (by norm_num) psum399o2_194
  · exact le_trans (by norm_num) psum399o2_195
  · exact le_trans (by norm_num) psum399o2_196
  · exact le_trans (by norm_num) psum399o2_197
  · exact le_trans (by norm_num) psum399o2_198
  · exact le_trans (by norm_num) psum399o2_199
  · exact le_trans (by norm_num) psum399o2_200
  · exact le_trans (by norm_num) psum399o2_201
  · exact le_trans (by norm_num) psum399o2_202
  · exact le_trans (by norm_num) psum399o2_203
  · exact le_trans (by norm_num) psum399o2_204
  · exact le_trans (by norm_num) psum399o2_205
  · exact le_trans (by norm_num) psum399o2_206
  · exact le_trans (by norm_num) psum399o2_207
  · exact le_trans (by norm_num) psum399o2_208
  · exact le_trans (by norm_num) psum399o2_209
  · exact le_trans (by norm_num) psum399o2_210
  · exact le_trans (by norm_num) psum399o2_211
  · exact le_trans (by norm_num) psum399o2_212
  · exact le_trans (by norm_num) psum399o2_213
  · exact le_trans (by norm_num) psum399o2_214
  · exact le_trans (by norm_num) psum399o2_215
  · exact le_trans (by norm_num) psum399o2_216
  · exact le_trans (by norm_num) psum399o2_217
  · exact le_trans (by norm_num) psum399o2_218
  · exact le_trans (by norm_num) psum399o2_219
  · exact le_trans (by norm_num) psum399o2_220
  · exact le_trans (by norm_num) psum399o2_221
  · exact le_trans (by norm_num) psum399o2_222
  · exact le_trans (by norm_num) psum399o2_223
  · exact le_trans (by norm_num) psum399o2_224
  · exact le_trans (by norm_num) psum399o2_225
  · exact le_trans (by norm_num) psum399o2_226
  · exact le_trans (by norm_num) psum399o2_227
  · exact le_trans (by norm_num) psum399o2_228
  · exact le_trans (by norm_num) psum399o2_229
  · exact le_trans (by norm_num) psum399o2_230
  · exact le_trans (by norm_num) psum399o2_231
  · exact le_trans (by norm_num) psum399o2_232
  · exact le_trans (by norm_num) psum399o2_233
  · exact le_trans (by norm_num) psum399o2_234
  · exact le_trans (by norm_num) psum399o2_235
  · exact le_trans (by norm_num) psum399o2_236
  · exact le_trans (by norm_num) psum399o2_237
  · exact le_trans (by norm_num) psum399o2_238
  · exact le_trans (by norm_num) psum399o2_239
  · exact le_trans (by norm_num) psum399o2_240
  · exact le_trans (by norm_num) psum399o2_241
  · exact le_trans (by norm_num) psum399o2_242
  · exact le_trans (by norm_num) psum399o2_243
  · exact le_trans (by norm_num) psum399o2_244
  · exact le_trans (by norm_num) psum399o2_245
  · exact le_trans (by norm_num) psum399o2_246
  · exact le_trans (by norm_num) psum399o2_247
  · exact le_trans (by norm_num) psum399o2_248
  · exact le_trans (by norm_num) psum399o2_249
  · exact le_trans (by norm_num) psum399o2_250

end CriticalLinePhasor.DVP

section AxiomAudit
#print axioms CriticalLinePhasor.DVP.psum399o2_floor
#print axioms CriticalLinePhasor.DVP.psum399o2_250
end AxiomAudit
